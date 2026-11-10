# Handoff to Frontend -- 2026-11-09: the current drop misses 200 MHz by 0.80 ns

From Backend (Dawson) to Frontend (Lehana), with a section for Validation
(Jacob). First backend build of drop `e4794e87a8c1`.

**The chip is physically correct -- DRC 0, LVS match -- and misses the 200 MHz
spec by 0.798 ns with TNS -350.2. The design also grew 60% in cells and 75% in
power.** Nothing on the backend side can close this; the numbers and the reason
are below.

This is not a complaint about the `wb_port` fixes. They closed real bugs that
real simulation found, and we would rather have a correct controller than a
fast broken one. But the current drop cannot be signed off at 200 MHz, and you
should see the cost before Wednesday.

## 1. The measurement

Same spec, same utilisation, same flow. Only the RTL differs.

| | `56ca186bf893` (signed off 11-05) | **`e4794e87a8c1`** (today) |
|---|---|---|
| WNS | **+0.0220** | **-0.798531** |
| TNS | **0** | **-350.242** |
| Fmax | **200 MHz met** | ~172 MHz |
| cells | 20,183 | **32,321** (+12,138, **+60%**) |
| core area um2 | 445,715 | **663,295** (+49%) |
| power mW | 99.46 | **174.09** (+75%) |
| achieved utilisation | 42.09% | 43.63% |
| DRC | 0 | **0** |
| LVS | match | **match** |

Build took 47.6 minutes at `CORE_UTILIZATION 35`, the value that signed off the
previous drop. RTL `cmp`-verified byte-identical to
`Frontend2/OutputFolders/TOPRTL` before the build, and the drop hashes to
`e4794e87a8c1` / design `ae80be01ac4f` -- the drop Validation passed tonight.

**TNS -350 is the number to look at, not WNS.** It is the same order as the
32-bit-deadline regression we chased on 11-02 (-348.6). A WNS of -0.8 with TNS
-350 means hundreds of endpoints failing, which is a structural cost, not one
slow path.

## 2. What we ruled out on our side first

We did not bring this to you until the backend levers were exhausted.

**Utilisation cannot fix it.** We swept 20/30/35/40 on the previous drop and the
*entire* curve is worth 0.141 ns (util 20 -0.1216 -> util 35 +0.0220, with 40
going negative again on congestion). The gap here is 0.80 ns, nearly six times
the whole dynamic range of the lever. There is no utilisation value that closes
this, so sweeping would only burn hours.

**The SDC I/O budget cannot fix it either.** Our SDC budgets 20% of the period
(1.0 ns at 5.0 ns) to logic outside the block on every port -- an ORFS
convention, not a spec requirement, and the worst path ends at the output port
`wb_port_wb_dat_o[31]`, so relaxing it looked promising. It does not work: the
violators include **register-to-register** paths that the output budget does not
touch, for instance

```
u_data_path.wr_pend_rptr[0]  ->  u_cmd_queue.queue_count[4]    -0.53
u_data_path.rd_aux_r[1]      ->  u_data_path.rd_aux_push[1]
```

Relaxing the output budget would move WNS from -0.80 to about -0.53 and still
fail. We are not going to weaken a constraint to make a number look better
anyway, but it is worth recording that we checked.

## 3. Where the time and the area went

The worst path is the one your own commit message describes:

```
u_data_path.rd_rptr[0]  ->  wb_port_wb_dat_o[31]   (output port)   -0.80
```

From `de7661a`:

> Fix: a same-cycle `rsp_is_head` bypass (`rsp_valid && rsp_aux == rd_head_idx`)
> lets `rd_ack`/`wb_dat_o` fire off the incoming response directly when it's for
> the current head ... while still buffering genuinely-reordered responses by tag.

That is exactly the path STA found. And the structures that came with it are
where the 12,138 cells went -- current `wb_port.sv` carries, and the signed-off
one did not:

```systemverilog
logic                  ord_mem     [0:ORD_DEPTH-1];        // 32 entries
logic [DATA_WIDTH-1:0] rd_data_buf [0:TAG_FIFO_DEPTH-1];   // 16 x 32 bits
logic                  rd_pending  [0:TAG_FIFO_DEPTH-1];   // 16
```

Two things compound there. `rd_data_buf` is 16 entries x 32 bits, and your own
comment says `wb_dat_o` reads `rd_data_buf[rd_head_idx]` **continuously, not
only when acking** -- so a 16-to-1 32-bit mux sits permanently in the output
path, in front of an endpoint that already gets only ~4.0 ns of the 5.0 ns
period. Then the `rsp_is_head` bypass puts a comparison and a second mux in
front of that, on the same output.

We are not asking you to undo either. We are saying the combination lands on
the single most timing-penalised endpoint class on the chip.

## 4. The conflict, stated plainly

This is the part worth putting in front of both of you, because neither drop is
simply "better":

| | STA at 200 MHz | Validation |
|---|---|---|
| `56ca186bf893` | **PASS** (+0.0220, DRC 0, LVS match) | **FAIL** -- `DATA_001` X/Z on `wb_dat_o`, 45 `HOST_002` violations |
| `e4794e87a8c1` | **FAIL** (-0.798, TNS -350) | **PASS** -- 20/20 paths, no finding |

**There is currently no drop that passes both.** The registered read path met
timing and added a cycle of latency to every read, which `HOST_002` correctly
rejects. The same-cycle bypass fixes the protocol and misses timing. That is a
real engineering conflict, not a mistake by anyone, and it is exactly the kind
of thing an integrated pipeline exists to surface -- your simulation could not
see the timing cost, and our build could not see the protocol bug.

## 5. The ask

**Keep the protocol fix. Get the decision off the output port's critical
path.** We are not asking for the latency back.

There is a precedent in this design that worked, from 11-02: `wr_data_ready`
was failing on the same output-port budget, and the fix was not to weaken the
race fix but to make the decision **knowable a cycle early** and register it --
"because the countdown is monotonic, the head entry being due is knowable a
cycle early, so a registered due flag preserves the same-cycle behaviour the
race fix exists for." That bought the whole violation back and the path never
returned.

The analogous shapes here, in the order we would try them:

1. **Register the head-data mux, not the decision.** `rd_data_buf[rd_head_idx]`
   does not need to be selected combinationally every cycle -- `rd_head_idx`
   is registered, so `rd_data_head_r` can be maintained as a registered copy
   updated when the head advances. `wb_dat_o` then reads a flop, and only the
   `rsp_is_head` bypass mux remains in the output path.
2. **Narrow the bypass.** The bypass only has to cover "the response arriving
   this cycle is for the current head". If `rsp_aux == rd_head_idx` is computed
   from registered state one cycle ahead where possible, the comparison leaves
   the output path.
3. **Sizing.** 16 x 32 bits of read buffer plus 32 entries of `ord_mem` is a
   lot of storage for a 16-deep tag space. If the reorder window genuinely
   needs to be 32, say so and we will budget for it -- but if `ORD_DEPTH 32`
   was chosen to clear `WB-011 x319` with margin rather than from a spec
   requirement, it is worth knowing what the minimum is.

We will build whatever you send and tell you the number, same as always.

## 6. What we are doing tonight regardless

We are running the **full flow end to end anyway**, with the backend enabled, and
letting the backend-to-frontend edge try to close this itself. That edge is the
point of the system and it has never run on a real failure.

Expect it to halt. Stage 6 will fail STA, stage 7 will route the finding to the
phase agents as a change request, validation will re-judge, and the backend will
run again -- twice, then halt on the round cap. We do not think the repair
agents will recover 0.80 ns and TNS -350 by local edits, because the cost is
architectural. But a recorded halt with a correctly-routed finding is a true
demonstration of the loop, and it is better evidence than a clean run on RTL
that fails validation.

If you land a fix tonight or Tuesday morning, send it and we will rebuild
immediately -- a build is 48 minutes and we have the config pinned.

## 7. For Jacob

- The drop you passed tonight (`e4794e87a8c1`, 20/20) is **physically clean**:
  DRC 0 violations, LVS netlists match. The only failure is STA at the spec
  frequency, so nothing in your sign-off is contradicted.
- Three Windows-only bugs blocked the single-machine flow and are fixed and
  pushed: `_py()` passed `sys.executable` as a regex *replacement*, so
  `C:\Users` raised `re.PatternError: bad escape \U` in **8 files including
  `validate_drop.py`** -- that is your stage 4, and a flow run from this
  machine would have crashed there twenty minutes in (`1d85d24`). Also
  `flow.py`'s `log()` wrote with the locale codec and could not encode the
  U+FFFD that its own `errors="replace"` produced (`090c061`).
- `run_path.py --netlist` is verified working from this machine after that fix:
  stimulus generation, `chain_harness` build, 10-file upload, `xrun`
  elaboration all succeed. It then fails on the **committed** netlist's ports
  (`rd_ack`, `wr_data_ready` invalid on `u_gate`), which is the staleness you
  flagged as "4 stale" -- `backend/outputs/` is drop `5f56adc7b7f5` from 10-28
  and those are exactly the ports `de7661a` and `98c259c` changed. Not a
  stage-8 defect. `flow.py --per-block-netlists` cuts bundles from the run's
  own drop for this reason.

## Summary

| | |
|---|---|
| Drop `e4794e87a8c1` physical | **DRC 0, LVS match** |
| Drop `e4794e87a8c1` timing | **FAIL** -- WNS -0.798, TNS -350.2, ~172 MHz |
| Cost vs the signed-off drop | **+60% cells, +49% area, +75% power** |
| Backend levers | **exhausted** -- utilisation worth 0.141 ns total, I/O budget leaves reg-to-reg violations |
| Cause | the `rd_data_buf` 16x32 mux driving `wb_dat_o` continuously, plus the `rsp_is_head` bypass, on the chip's most penalised endpoint |
| Ask | keep the protocol fix, register the head-data mux so `wb_dat_o` reads a flop |
| Precedent | the 11-02 `wr_data_ready` fix: make the decision knowable a cycle early |
| Tonight | full flow run, letting the backend-to-frontend edge attempt it |
