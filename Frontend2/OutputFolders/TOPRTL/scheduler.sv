////////////////////////////////////////////////////////////////////////////////
// Module:    scheduler
// Generated: see the manifest's generated_utc (no timestamp here, so identical RTL is byte-identical)
// Generator:     Scheduler Generator (Phase 3)
//
// FR-FCFS (First-Ready First-Come-First-Served) scheduler.
// Open-page policy: row-hit requests prioritized over row-miss.
// Reads cmd_queue entries and bank_tracker permissions.
// Issues one command per cycle to cmd_gen.
////////////////////////////////////////////////////////////////////////////////

module scheduler #(
    parameter DEPTH     = 16,
    parameter IDX_BITS  = 4,
    parameter ROW_BITS  = 15,
    parameter COL_BITS  = 10,
    parameter BANK_BITS = 3,
    parameter NUM_BANKS = 8,
    parameter AUX_WIDTH = 4,
    parameter WORD_BEATS = 2
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // ── From cmd_queue (lookahead) ──
    input  logic [DEPTH-1:0]        q_valid,
    input  logic [ROW_BITS-1:0]     q_row     [DEPTH],
    input  logic [COL_BITS-1:0]     q_col     [DEPTH],
    input  logic [BANK_BITS-1:0]    q_bank    [DEPTH],
    input  logic                    q_we      [DEPTH],
    input  logic [AUX_WIDTH-1:0]    q_aux     [DEPTH],
    input  logic [DEPTH-1:0]        q_urgent,       // one-hot: oldest entry past the queue's age bound

    // ── From bank_tracker ──
    input  logic [NUM_BANKS-1:0]    bank_is_active,
    input  logic [ROW_BITS-1:0]     bank_open_row [NUM_BANKS],
    input  logic [NUM_BANKS-1:0]    bank_act_allowed,
    input  logic [NUM_BANKS-1:0]    bank_rd_allowed,
    input  logic [NUM_BANKS-1:0]    bank_wr_allowed,
    input  logic [NUM_BANKS-1:0]    bank_pre_allowed,

    // ── From refresh_ctrl ──
    input  logic                    ref_required,
    input  logic                    ref_urgent,
    output logic                    ref_ack,

    // ── Dequeue grant (to cmd_queue) ──
    output logic                    deq_grant,
    output logic [IDX_BITS-1:0]     deq_idx,

    // ── Command output (to cmd_gen) ──
    output logic                    cmd_valid,
    output logic [3:0]              cmd_type,       // ACT/RD/WR/PRE/REF/NOP
    output logic [ROW_BITS-1:0]     cmd_row,
    output logic [COL_BITS-1:0]     cmd_col,
    output logic [BANK_BITS-1:0]    cmd_bank,
    output logic                    cmd_we,
    output logic [AUX_WIDTH-1:0]    cmd_aux
);

    // Command type encoding
    localparam CMD_NOP = 4'd0;
    localparam CMD_ACT = 4'd1;
    localparam CMD_RD  = 4'd2;
    localparam CMD_WR  = 4'd3;
    localparam CMD_PRE = 4'd4;
    localparam CMD_REF = 4'd5;

    // ════════════════════════════════════════════════════
    // Candidate classification
    // ════════════════════════════════════════════════════
    // For each queue entry: is it a row-hit? is it ready for CAS?
    logic [DEPTH-1:0] is_row_hit;
    logic [DEPTH-1:0] is_cas_ready;  // bank active + row hit + timing ok
    logic [DEPTH-1:0] is_act_needed; // bank idle or wrong row

    // JEDEC: REF is only legal once every bank is precharged.
    wire all_banks_idle = ~(|bank_is_active);

    // ════════════════════════════════════════════════════
    // Feedback-latency hold (FB_LAG = 2 cycles after cmd_valid, plus the
    // one pending cycle the selection pipeline below adds)
    // ════════════════════════════════════════════════════
    // A command selected in cycle N is registered at the end of N (cmd_*),
    // cmd_gen registers its fb_* strobes at the end of N+1, and bank_tracker
    // updates its state/counters at the end of N+2. So the permissions this
    // module reads in cycles N+1 and N+2 do not yet reflect that command, and
    // selecting from them re-issues it (ACT to an already-active bank, an
    // ACT inside tRC/tRRD, a REF or RD straight after the PRE/ACT/WR that
    // should have blocked it). Track what was issued in the last two cycles
    // (cmd_* now, d1_* one cycle ago) and hold anything those could change.
    //
    // 2026-10-27 (backend timing finding scheduler/TIMING/cmd_row): selection
    // is now two pipeline stages (classify+prioritize, then mux+register --
    // see sel_*_r below), so a decision can sit for one cycle as sel_*_r
    // before it is even registered as cmd_valid. That cycle isn't covered by
    // cmd_*/d1_* at all, so it needs its own mask term (the sel_*_r
    // contribution in the inflight block below) -- without it, the cycle
    // right after a selection and right before it becomes cmd_valid could
    // pick a second, conflicting command for the same bank.
    logic                 d1_valid;
    logic [3:0]           d1_type;
    logic [BANK_BITS-1:0] d1_bank;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            d1_valid <= 1'b0;
            d1_type  <= CMD_NOP;
            d1_bank  <= '0;
        end else begin
            d1_valid <= cmd_valid;
            d1_type  <= cmd_type;
            d1_bank  <= cmd_bank;
        end
    end

    // Pending selection, one cycle ahead of cmd_valid (driven by the
    // always_ff right after the priority-select block below, which computes
    // sel_valid/sel_idx/... in the same cycle this register samples them).
    // Declared here so the inflight mask and the candidate-classification
    // guard below can both read it.
    logic                    sel_valid_r;
    logic [IDX_BITS-1:0]     sel_idx_r;
    logic [3:0]              sel_type_r;
    logic                    sel_is_ref_r;
    logic                    sel_from_queue_r;
    logic [BANK_BITS-1:0]    sel_bank_r;
    // 2026-10-29 (Backend, backend/handoff/HANDOFF_FRONTEND_2026-10-29_3.md,
    // correcting _2.md which you're reading the trace of if you diff this
    // against the previous commit): fix (a) -- the registered one-hot decode
    // below, sel_onehot_r -- is restored. The block-level measurement that
    // said to drop it was inverted relative to the chip: the block's
    // critical path starts at an input port carrying a 1ns I/O budget that
    // doesn't exist once this is assembled into the real chip, which hid
    // what (a) actually does. At chip level (a) alone is the best scheduler
    // this project has measured (186.8MHz, c32b44871f22), 0.43ns better than
    // this file with neither (a) nor (b). Fix (b) -- registering this bank
    // directly instead of re-muxing it -- stays reverted; a bare wire,
    // re-muxed from q_bank[sel_idx_r] each cycle, is still the better half
    // of the pair.
    wire [BANK_BITS-1:0] sel_bank_eff_r = sel_from_queue_r ? q_bank[sel_idx_r] : sel_bank_r;
    // sel_onehot_r: a one-hot decode of the pending CAS pick, registered
    // alongside sel_idx_r so recently_granted (below) can read a single bit
    // instead of comparing against sel_idx_r -- that comparison put 16
    // four-bit comparators in the same cone that computes the next
    // sel_idx_r, closing a 32-level feedback loop through the register the
    // pipeline stage was supposed to cut. This is fix (a).
    logic [DEPTH-1:0]        sel_onehot_r;

    logic [NUM_BANKS-1:0] inflight_any;    // any command to this bank in flight
    logic [NUM_BANKS-1:0] inflight_state;  // an ACT or PRE to this bank in flight
    logic                 inflight_ref;    // a REFRESH in flight (all banks)
    logic                 inflight_act;    // an ACT in flight (tRRD / tFAW, any bank)
    logic                 inflight_wr;     // a WRITE in flight (tWTR, any bank)
    always_comb begin
        inflight_any   = '0;
        inflight_state = '0;
        inflight_ref   = 1'b0;
        inflight_act   = 1'b0;
        inflight_wr    = 1'b0;
        if (cmd_valid) begin
            if (cmd_type == CMD_REF) inflight_ref = 1'b1;
            else if (cmd_type != CMD_NOP) begin
                inflight_any[cmd_bank] = 1'b1;
                if (cmd_type == CMD_ACT || cmd_type == CMD_PRE) inflight_state[cmd_bank] = 1'b1;
                if (cmd_type == CMD_ACT) inflight_act = 1'b1;
                if (cmd_type == CMD_WR)  inflight_wr  = 1'b1;
            end
        end
        if (d1_valid) begin
            if (d1_type == CMD_REF) inflight_ref = 1'b1;
            else if (d1_type != CMD_NOP) begin
                inflight_any[d1_bank] = 1'b1;
                if (d1_type == CMD_ACT || d1_type == CMD_PRE) inflight_state[d1_bank] = 1'b1;
                if (d1_type == CMD_ACT) inflight_act = 1'b1;
                if (d1_type == CMD_WR)  inflight_wr  = 1'b1;
            end
        end
        // Pending (sel_*_r): decided, not yet cmd_valid -- see the comment
        // by sel_valid_r's declaration above.
        if (sel_valid_r) begin
            if (sel_type_r == CMD_REF) inflight_ref = 1'b1;
            else if (sel_type_r != CMD_NOP) begin
                inflight_any[sel_bank_eff_r] = 1'b1;
                if (sel_type_r == CMD_ACT || sel_type_r == CMD_PRE) inflight_state[sel_bank_eff_r] = 1'b1;
                if (sel_type_r == CMD_ACT) inflight_act = 1'b1;
                if (sel_type_r == CMD_WR)  inflight_wr  = 1'b1;
            end
        end
    end

    // REF needs every bank idle AND past tRP/tRC/tRFC (bank_act_allowed
    // already folds those counters in), and no ACT/REF still in flight.
    wire ref_ok = all_banks_idle && (&bank_act_allowed) && !inflight_act && !inflight_ref;

    // Global CAS (RD/WR) issue spacing, independent of bank: at least
    // WORD_BEATS controller cycles between any two selected CAS commands,
    // because the DQ bus takes that many cycles to deliver one word no
    // matter which bank it came from. bank_tracker's own tCCD counter is
    // per-spec timing gated through cmd_gen's feedback path, which may or
    // may not land tight enough on its own; this is deliberately local and
    // self-contained instead -- loaded the same cycle a CAS is selected
    // (sel_valid/sel_type, not the registered sel_*_r, so there's no
    // pipeline lag of its own to go wrong), with nothing between it and
    // the decision it gates. (Validation, 2026-10-29, addendum 10: "Two
    // reads one cycle apart cannot both be captured on one bus, whatever
    // the data path does... until [the beat-rate model] is decided the
    // scheduler spacing is the safe choice.") Declared here, before
    // is_cas_ready reads it below; driven by an always_ff further down,
    // after sel_valid/sel_type exist to be read.
    logic [7:0] cas_spacing_ctr;
    wire        cas_spacing_active = (cas_spacing_ctr != 0);

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            logic [BANK_BITS-1:0] b;
            logic recently_granted;
            b = q_bank[i];
            // deq_grant/deq_idx are this module's OWN registered outputs
            // from last cycle -- cmd_queue's own q_valid/q_row/... won't
            // reflect the dequeue for (at least) one more cycle after that,
            // so without this guard the same entry gets re-selected and
            // re-granted every cycle until the queue catches up (observed:
            // 19 enqueued, 16 dequeued -- see
            // Frontend2/VALIDATION_INTEGRATION_PLAN.md Defect 1).
            // Also exclude an entry already pending in sel_*_r for CAS --
            // one cycle before deq_grant actually fires, now that selection
            // is two pipeline stages (2026-10-27). is_cas_ready deliberately
            // allows back-to-back CAS to the SAME bank (no inflight_any
            // check), so without this the identical entry could be re-picked
            // for RD/WR the cycle right after being picked, before its
            // dequeue retires -- the Defect-1 bug shape, stretched by the
            // new pipeline stage. ACT/PRE re-selection is already blocked by
            // the bank-level inflight_any/inflight_act mask above, which the
            // sel_*_r contribution covers -- this guard only needs CAS.
            //
            // sel_onehot_r[i], not (sel_idx_r == i[IDX_BITS-1:0]) -- fix (a),
            // restored (see sel_onehot_r's declaration above). The equality
            // form puts 16 four-bit comparators against sel_idx_r in the
            // same cone that computes the next sel_idx_r, closing a
            // feedback loop through the register the pipeline stage was
            // supposed to cut. A single registered bit read has no such
            // dependency.
            recently_granted = (deq_grant && (deq_idx == i[IDX_BITS-1:0]))
                               || (sel_valid_r && sel_from_queue_r
                                   && (sel_type_r == CMD_RD || sel_type_r == CMD_WR)
                                   && sel_onehot_r[i]);
            is_row_hit[i]   = q_valid[i] && bank_is_active[b] &&
                               (bank_open_row[b] == q_row[i]);
            is_cas_ready[i] = is_row_hit[i] && !recently_granted && !cas_spacing_active &&
                               !inflight_state[b] && !inflight_ref &&
                               (q_we[i] ? bank_wr_allowed[b] : (bank_rd_allowed[b] && !inflight_wr));
            is_act_needed[i] = q_valid[i] && (!bank_is_active[b] ||
                               (bank_open_row[b] != q_row[i]));
        end
    end

    // ════════════════════════════════════════════════════
    // FR-FCFS selection: row-hit CAS > any ACT-needed
    // ════════════════════════════════════════════════════
    logic                    sel_valid;
    logic [IDX_BITS-1:0]     sel_idx;
    logic [DEPTH-1:0]        sel_onehot;   // sel_idx, decoded -- see sel_onehot_r above
    logic [3:0]              sel_type;
    logic                    sel_is_ref;
    // Most commands source row/col/bank/we/aux from the winning queue entry
    // (q_*[sel_idx]). A refresh-driven forced PRE (below) isn't tied to any
    // queue entry -- it only carries a bank -- so this flag picks which
    // source the output-registration stage uses.
    logic                    sel_from_queue;
    logic [BANK_BITS-1:0]    sel_bank;

    // ────────────────────────────────────────────────────────────────
    // Priority 2/3 arbitration as a tree, not a ripple (2026-11-03,
    // backend/handoff/HANDOFF_FRONTEND_2026-11-03.md). The old code
    // chained two 16-deep first-match loops through `if (!sel_valid)`
    // -- 32 serial decision levels, and every failing endpoint on the
    // best chip built so far traced back through exactly this chain to
    // u_cmd_queue.entry_bank. Each entry's eligibility for a tier never
    // depended on any OTHER entry (is_cas_ready/is_act_needed above
    // already compute all DEPTH entries in parallel) or on the OTHER
    // tier (eligible3 below reads only bank state and inflight, never
    // tier 2's result) -- only "which entry wins" was serial. So both
    // tiers' winners are found by their own balanced reduction tree
    // (log2(DEPTH) levels instead of DEPTH), computed concurrently
    // rather than one gated behind the other, and only the final
    // "tier 2 beats tier 3" choice below is still a priority mux -- one
    // level, not sixteen.
    // ────────────────────────────────────────────────────────────────

    // Priority 3's per-entry eligibility, spelled out the same way
    // is_cas_ready is above: each i's PRE-first-vs-ACT-now resolution
    // reads only q_bank[i] and bank/inflight state, independent of
    // every other i.
    logic [DEPTH-1:0] act_cond_pre;   // bank active, wrong row, ready to PRE
    logic [DEPTH-1:0] act_cond_act;   // bank idle, ready to ACT
    logic [DEPTH-1:0] eligible3;
    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            logic [BANK_BITS-1:0] b;
            b = q_bank[i];
            act_cond_pre[i] = is_act_needed[i] && bank_is_active[b] && bank_pre_allowed[b] &&
                               !inflight_any[b] && !inflight_ref;
            act_cond_act[i] = is_act_needed[i] && !bank_is_active[b] && bank_act_allowed[b] &&
                               !inflight_any[b] && !inflight_act && !inflight_ref;
            eligible3[i]    = act_cond_pre[i] || act_cond_act[i];
        end
    end

    // q_urgent decoded once (one-hot or zero).
    logic                urg_valid;
    logic [IDX_BITS-1:0] urg_idx;
    always_comb begin
        urg_valid = |q_urgent;
        urg_idx   = '0;
        for (int i = 0; i < DEPTH; i++)
            if (q_urgent[i]) urg_idx = i[IDX_BITS-1:0];
    end

    logic                  t2_v_L1   [8];
    logic [3:0]   t2_idx_L1 [8];
    logic [3:0]            t2_type_L1[8];
    logic                  t2_v_L2   [4];
    logic [3:0]   t2_idx_L2 [4];
    logic [3:0]            t2_type_L2[4];
    logic                  t2_v_L3   [2];
    logic [3:0]   t2_idx_L3 [2];
    logic [3:0]            t2_type_L3[2];
    logic                  t2_v_L4   [1];
    logic [3:0]   t2_idx_L4 [1];
    logic [3:0]            t2_type_L4[1];

    assign t2_v_L1[0]    = is_cas_ready[0] | is_cas_ready[1];
    assign t2_idx_L1[0]  = is_cas_ready[0] ? 4'd0 : 4'd1;
    assign t2_type_L1[0] = is_cas_ready[0] ? (q_we[0] ? CMD_WR : CMD_RD) : (q_we[1] ? CMD_WR : CMD_RD);
    assign t2_v_L1[1]    = is_cas_ready[2] | is_cas_ready[3];
    assign t2_idx_L1[1]  = is_cas_ready[2] ? 4'd2 : 4'd3;
    assign t2_type_L1[1] = is_cas_ready[2] ? (q_we[2] ? CMD_WR : CMD_RD) : (q_we[3] ? CMD_WR : CMD_RD);
    assign t2_v_L1[2]    = is_cas_ready[4] | is_cas_ready[5];
    assign t2_idx_L1[2]  = is_cas_ready[4] ? 4'd4 : 4'd5;
    assign t2_type_L1[2] = is_cas_ready[4] ? (q_we[4] ? CMD_WR : CMD_RD) : (q_we[5] ? CMD_WR : CMD_RD);
    assign t2_v_L1[3]    = is_cas_ready[6] | is_cas_ready[7];
    assign t2_idx_L1[3]  = is_cas_ready[6] ? 4'd6 : 4'd7;
    assign t2_type_L1[3] = is_cas_ready[6] ? (q_we[6] ? CMD_WR : CMD_RD) : (q_we[7] ? CMD_WR : CMD_RD);
    assign t2_v_L1[4]    = is_cas_ready[8] | is_cas_ready[9];
    assign t2_idx_L1[4]  = is_cas_ready[8] ? 4'd8 : 4'd9;
    assign t2_type_L1[4] = is_cas_ready[8] ? (q_we[8] ? CMD_WR : CMD_RD) : (q_we[9] ? CMD_WR : CMD_RD);
    assign t2_v_L1[5]    = is_cas_ready[10] | is_cas_ready[11];
    assign t2_idx_L1[5]  = is_cas_ready[10] ? 4'd10 : 4'd11;
    assign t2_type_L1[5] = is_cas_ready[10] ? (q_we[10] ? CMD_WR : CMD_RD) : (q_we[11] ? CMD_WR : CMD_RD);
    assign t2_v_L1[6]    = is_cas_ready[12] | is_cas_ready[13];
    assign t2_idx_L1[6]  = is_cas_ready[12] ? 4'd12 : 4'd13;
    assign t2_type_L1[6] = is_cas_ready[12] ? (q_we[12] ? CMD_WR : CMD_RD) : (q_we[13] ? CMD_WR : CMD_RD);
    assign t2_v_L1[7]    = is_cas_ready[14] | is_cas_ready[15];
    assign t2_idx_L1[7]  = is_cas_ready[14] ? 4'd14 : 4'd15;
    assign t2_type_L1[7] = is_cas_ready[14] ? (q_we[14] ? CMD_WR : CMD_RD) : (q_we[15] ? CMD_WR : CMD_RD);
    assign t2_v_L2[0]    = t2_v_L1[0] | t2_v_L1[1];
    assign t2_idx_L2[0]  = t2_v_L1[0] ? t2_idx_L1[0] : t2_idx_L1[1];
    assign t2_type_L2[0] = t2_v_L1[0] ? t2_type_L1[0] : t2_type_L1[1];
    assign t2_v_L2[1]    = t2_v_L1[2] | t2_v_L1[3];
    assign t2_idx_L2[1]  = t2_v_L1[2] ? t2_idx_L1[2] : t2_idx_L1[3];
    assign t2_type_L2[1] = t2_v_L1[2] ? t2_type_L1[2] : t2_type_L1[3];
    assign t2_v_L2[2]    = t2_v_L1[4] | t2_v_L1[5];
    assign t2_idx_L2[2]  = t2_v_L1[4] ? t2_idx_L1[4] : t2_idx_L1[5];
    assign t2_type_L2[2] = t2_v_L1[4] ? t2_type_L1[4] : t2_type_L1[5];
    assign t2_v_L2[3]    = t2_v_L1[6] | t2_v_L1[7];
    assign t2_idx_L2[3]  = t2_v_L1[6] ? t2_idx_L1[6] : t2_idx_L1[7];
    assign t2_type_L2[3] = t2_v_L1[6] ? t2_type_L1[6] : t2_type_L1[7];
    assign t2_v_L3[0]    = t2_v_L2[0] | t2_v_L2[1];
    assign t2_idx_L3[0]  = t2_v_L2[0] ? t2_idx_L2[0] : t2_idx_L2[1];
    assign t2_type_L3[0] = t2_v_L2[0] ? t2_type_L2[0] : t2_type_L2[1];
    assign t2_v_L3[1]    = t2_v_L2[2] | t2_v_L2[3];
    assign t2_idx_L3[1]  = t2_v_L2[2] ? t2_idx_L2[2] : t2_idx_L2[3];
    assign t2_type_L3[1] = t2_v_L2[2] ? t2_type_L2[2] : t2_type_L2[3];
    assign t2_v_L4[0]    = t2_v_L3[0] | t2_v_L3[1];
    assign t2_idx_L4[0]  = t2_v_L3[0] ? t2_idx_L3[0] : t2_idx_L3[1];
    assign t2_type_L4[0] = t2_v_L3[0] ? t2_type_L3[0] : t2_type_L3[1];
    wire                t2_valid = t2_v_L4[0];
    wire [IDX_BITS-1:0] t2_idx   = t2_idx_L4[0];
    wire [3:0]          t2_type  = t2_type_L4[0];

    logic                  t3_v_L1   [8];
    logic [3:0]   t3_idx_L1 [8];
    logic [3:0]            t3_type_L1[8];
    logic                  t3_v_L2   [4];
    logic [3:0]   t3_idx_L2 [4];
    logic [3:0]            t3_type_L2[4];
    logic                  t3_v_L3   [2];
    logic [3:0]   t3_idx_L3 [2];
    logic [3:0]            t3_type_L3[2];
    logic                  t3_v_L4   [1];
    logic [3:0]   t3_idx_L4 [1];
    logic [3:0]            t3_type_L4[1];

    assign t3_v_L1[0]    = eligible3[0] | eligible3[1];
    assign t3_idx_L1[0]  = eligible3[0] ? 4'd0 : 4'd1;
    assign t3_type_L1[0] = eligible3[0] ? (act_cond_pre[0] ? CMD_PRE : CMD_ACT) : (act_cond_pre[1] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[1]    = eligible3[2] | eligible3[3];
    assign t3_idx_L1[1]  = eligible3[2] ? 4'd2 : 4'd3;
    assign t3_type_L1[1] = eligible3[2] ? (act_cond_pre[2] ? CMD_PRE : CMD_ACT) : (act_cond_pre[3] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[2]    = eligible3[4] | eligible3[5];
    assign t3_idx_L1[2]  = eligible3[4] ? 4'd4 : 4'd5;
    assign t3_type_L1[2] = eligible3[4] ? (act_cond_pre[4] ? CMD_PRE : CMD_ACT) : (act_cond_pre[5] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[3]    = eligible3[6] | eligible3[7];
    assign t3_idx_L1[3]  = eligible3[6] ? 4'd6 : 4'd7;
    assign t3_type_L1[3] = eligible3[6] ? (act_cond_pre[6] ? CMD_PRE : CMD_ACT) : (act_cond_pre[7] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[4]    = eligible3[8] | eligible3[9];
    assign t3_idx_L1[4]  = eligible3[8] ? 4'd8 : 4'd9;
    assign t3_type_L1[4] = eligible3[8] ? (act_cond_pre[8] ? CMD_PRE : CMD_ACT) : (act_cond_pre[9] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[5]    = eligible3[10] | eligible3[11];
    assign t3_idx_L1[5]  = eligible3[10] ? 4'd10 : 4'd11;
    assign t3_type_L1[5] = eligible3[10] ? (act_cond_pre[10] ? CMD_PRE : CMD_ACT) : (act_cond_pre[11] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[6]    = eligible3[12] | eligible3[13];
    assign t3_idx_L1[6]  = eligible3[12] ? 4'd12 : 4'd13;
    assign t3_type_L1[6] = eligible3[12] ? (act_cond_pre[12] ? CMD_PRE : CMD_ACT) : (act_cond_pre[13] ? CMD_PRE : CMD_ACT);
    assign t3_v_L1[7]    = eligible3[14] | eligible3[15];
    assign t3_idx_L1[7]  = eligible3[14] ? 4'd14 : 4'd15;
    assign t3_type_L1[7] = eligible3[14] ? (act_cond_pre[14] ? CMD_PRE : CMD_ACT) : (act_cond_pre[15] ? CMD_PRE : CMD_ACT);
    assign t3_v_L2[0]    = t3_v_L1[0] | t3_v_L1[1];
    assign t3_idx_L2[0]  = t3_v_L1[0] ? t3_idx_L1[0] : t3_idx_L1[1];
    assign t3_type_L2[0] = t3_v_L1[0] ? t3_type_L1[0] : t3_type_L1[1];
    assign t3_v_L2[1]    = t3_v_L1[2] | t3_v_L1[3];
    assign t3_idx_L2[1]  = t3_v_L1[2] ? t3_idx_L1[2] : t3_idx_L1[3];
    assign t3_type_L2[1] = t3_v_L1[2] ? t3_type_L1[2] : t3_type_L1[3];
    assign t3_v_L2[2]    = t3_v_L1[4] | t3_v_L1[5];
    assign t3_idx_L2[2]  = t3_v_L1[4] ? t3_idx_L1[4] : t3_idx_L1[5];
    assign t3_type_L2[2] = t3_v_L1[4] ? t3_type_L1[4] : t3_type_L1[5];
    assign t3_v_L2[3]    = t3_v_L1[6] | t3_v_L1[7];
    assign t3_idx_L2[3]  = t3_v_L1[6] ? t3_idx_L1[6] : t3_idx_L1[7];
    assign t3_type_L2[3] = t3_v_L1[6] ? t3_type_L1[6] : t3_type_L1[7];
    assign t3_v_L3[0]    = t3_v_L2[0] | t3_v_L2[1];
    assign t3_idx_L3[0]  = t3_v_L2[0] ? t3_idx_L2[0] : t3_idx_L2[1];
    assign t3_type_L3[0] = t3_v_L2[0] ? t3_type_L2[0] : t3_type_L2[1];
    assign t3_v_L3[1]    = t3_v_L2[2] | t3_v_L2[3];
    assign t3_idx_L3[1]  = t3_v_L2[2] ? t3_idx_L2[2] : t3_idx_L2[3];
    assign t3_type_L3[1] = t3_v_L2[2] ? t3_type_L2[2] : t3_type_L2[3];
    assign t3_v_L4[0]    = t3_v_L3[0] | t3_v_L3[1];
    assign t3_idx_L4[0]  = t3_v_L3[0] ? t3_idx_L3[0] : t3_idx_L3[1];
    assign t3_type_L4[0] = t3_v_L3[0] ? t3_type_L3[0] : t3_type_L3[1];
    wire                t3_valid = t3_v_L4[0];
    wire [IDX_BITS-1:0] t3_idx   = t3_idx_L4[0];
    wire [3:0]          t3_type  = t3_type_L4[0];

    always_comb begin
        sel_valid      = 1'b0;
        sel_idx        = '0;
        sel_onehot     = '0;
        sel_type       = CMD_NOP;
        sel_is_ref     = 1'b0;
        sel_from_queue = 1'b1;
        sel_bank       = '0;

        // Priority 1: Urgent refresh. JEDEC requires every bank precharged
        // before REF -- if any bank is still open, force-precharge it
        // (lowest-numbered active + precharge-ready bank) instead of
        // issuing REF early; only issue REF once all_banks_idle. If the
        // active bank(s) aren't precharge-ready yet (tRAS/tWR/etc. still
        // counting down), this cycle is a NOP and the next cycle retries --
        // never a raw un-gated REF (see Defect 5 in
        // Frontend2/VALIDATION_INTEGRATION_PLAN.md).
        if (ref_urgent) begin
            if (ref_ok) begin
                sel_valid  = 1'b1;
                sel_type   = CMD_REF;
                sel_is_ref = 1'b1;
            end else begin
                for (int b = 0; b < NUM_BANKS; b++) begin
                    if (bank_is_active[b] && bank_pre_allowed[b] && !inflight_any[b] && !inflight_ref && !sel_valid) begin
                        sel_valid      = 1'b1;
                        sel_type       = CMD_PRE;
                        sel_from_queue = 1'b0;
                        sel_bank       = b[BANK_BITS-1:0];
                    end
                end
            end
        end
        // Age priority (Validation, 2026-11-09): the oldest request past
        // cmd_queue's STARVE_CYCLES (q_urgent, one-hot) wins whichever tier
        // it is eligible for this cycle -- its CAS over other row hits, its
        // ACT/PRE over other misses. When its own bank's timing makes it
        // eligible for neither, the normal tiers run so other banks are not
        // idled. FR-FCFS with no age bound starved a write for 480 cycles
        // (drop 2a18a7929dce) and the tree's fixed index order could do the
        // same to a row hit at a high index.
        // Priority 2: Row-hit CAS (first-come = lowest index), priority 3:
        // ACT for row-miss -- both resolved above by their own tree, run
        // concurrently; this is just "which tier wins."
        else begin
            if (urg_valid && is_cas_ready[urg_idx]) begin
                sel_valid            = 1'b1;
                sel_idx               = urg_idx;
                sel_onehot            = q_urgent;
                sel_type              = q_we[urg_idx] ? CMD_WR : CMD_RD;
            end else if (urg_valid && eligible3[urg_idx]) begin
                sel_valid            = 1'b1;
                sel_idx               = urg_idx;
                sel_onehot            = q_urgent;
                sel_type              = act_cond_pre[urg_idx] ? CMD_PRE : CMD_ACT;
            end else if (t2_valid) begin
                sel_valid            = 1'b1;
                sel_idx               = t2_idx;
                sel_onehot[t2_idx]    = 1'b1;
                sel_type              = t2_type;
            end else if (t3_valid) begin
                sel_valid            = 1'b1;
                sel_idx               = t3_idx;
                sel_onehot[t3_idx]    = 1'b1;
                sel_type              = t3_type;
            end
            // Priority 4: Normal refresh (when no other work) -- same
            // idle-gate / force-precharge-first behavior as urgent refresh.
            if (!sel_valid && ref_required) begin
                if (ref_ok) begin
                    sel_valid  = 1'b1;
                    sel_type   = CMD_REF;
                    sel_is_ref = 1'b1;
                end else begin
                    for (int b = 0; b < NUM_BANKS; b++) begin
                        if (bank_is_active[b] && bank_pre_allowed[b] && !inflight_any[b] && !inflight_ref && !sel_valid) begin
                            sel_valid      = 1'b1;
                            sel_type       = CMD_PRE;
                            sel_from_queue = 1'b0;
                            sel_bank       = b[BANK_BITS-1:0];
                        end
                    end
                end
            end
        end
    end

    // cas_spacing_ctr's own update, now that sel_valid/sel_type above
    // exist to read -- see its declaration by is_cas_ready for why.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)
            cas_spacing_ctr <= '0;
        else if (sel_valid && (sel_type == CMD_RD || sel_type == CMD_WR))
            cas_spacing_ctr <= WORD_BEATS[7:0] - 8'd1;
        else if (cas_spacing_ctr != 0)
            cas_spacing_ctr <= cas_spacing_ctr - 1'b1;

    // ════════════════════════════════════════════════════
    // Pipeline stage: register the selection (timing fix, 2026-10-27)
    // ════════════════════════════════════════════════════
    // Backend finding scheduler/TIMING/cmd_row: the old single-cycle chain
    // (classify all DEPTH entries -> prioritize -> mux q_*[sel_idx] on the
    // just-computed sel_idx -> register cmd_*) measured 36 logic levels,
    // WNS -1.04ns at 200MHz. This register ends the classify+prioritize
    // half; the q_*[sel_idx_r] mux and cmd_* registration below are the
    // second half, one cycle later -- splitting the chain roughly in half.
    // Costs one extra cycle of scheduling latency (candidate-ready to
    // cmd_valid), not throughput (a new decision still pipelines in every
    // cycle). cmd_queue needs no change: it only invalidates an entry on
    // deq_grant (now delayed to match), and entries are a flat array with
    // per-index valid bits, never shifted/compacted, so q_*[sel_idx_r] is
    // still the right data one cycle after sel_idx was first computed.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sel_valid_r      <= 1'b0;
            sel_idx_r        <= '0;
            sel_onehot_r     <= '0;
            sel_type_r       <= CMD_NOP;
            sel_is_ref_r     <= 1'b0;
            sel_from_queue_r <= 1'b1;
            sel_bank_r       <= '0;
        end else begin
            sel_valid_r      <= sel_valid;
            sel_idx_r        <= sel_idx;
            sel_onehot_r     <= sel_onehot;
            sel_type_r       <= sel_type;
            sel_is_ref_r     <= sel_is_ref;
            sel_from_queue_r <= sel_from_queue;
            sel_bank_r       <= sel_bank;
        end
    end

    // ════════════════════════════════════════════════════
    // Output registration (reads the registered sel_*_r, not sel_*)
    // ════════════════════════════════════════════════════
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cmd_valid <= 1'b0;
            cmd_type  <= CMD_NOP;
            cmd_row   <= '0;
            cmd_col   <= '0;
            cmd_bank  <= '0;
            cmd_we    <= 1'b0;
            cmd_aux   <= '0;
            deq_grant <= 1'b0;
            deq_idx   <= '0;
            ref_ack   <= 1'b0;
        end else begin
            cmd_valid <= sel_valid_r;
            cmd_type  <= sel_type_r;
            deq_grant <= 1'b0;
            ref_ack   <= 1'b0;

            if (sel_valid_r) begin
                if (sel_is_ref_r) begin
                    ref_ack  <= 1'b1;
                    cmd_bank <= '0;
                    cmd_row  <= '0;
                    cmd_col  <= '0;
                    cmd_we   <= 1'b0;
                    cmd_aux  <= '0;
                end else if (!sel_from_queue_r) begin
                    // Forced precharge ahead of refresh -- bank only, no
                    // backing queue entry, so nothing to dequeue.
                    cmd_bank <= sel_bank_r;
                    cmd_row  <= '0;
                    cmd_col  <= '0;
                    cmd_we   <= 1'b0;
                    cmd_aux  <= '0;
                end else begin
                    cmd_row  <= q_row[sel_idx_r];
                    cmd_col  <= q_col[sel_idx_r];
                    cmd_bank <= q_bank[sel_idx_r];
                    cmd_we   <= q_we[sel_idx_r];
                    cmd_aux  <= q_aux[sel_idx_r];
                    // Dequeue only on CAS (RD/WR) — ACT/PRE don't consume entry
                    if (sel_type_r == CMD_RD || sel_type_r == CMD_WR) begin
                        deq_grant <= 1'b1;
                        deq_idx   <= sel_idx_r;
                    end
                end
            end
        end
    end

endmodule
