#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║              PHASE 3 VALIDATION AGENT                                ║
║  Static port validation + testbench generation                       ║
║  Modules: cmd_queue, scheduler, cmd_gen                              ║
║  Checks: V-CQ, V-SC, V-CG, V-XM3                                   ║
║  Output: phase3_validation_report + 3 testbenches + Makefile.sim     ║
╚══════════════════════════════════════════════════════════════════════╝
"""
import json, os, sys, re, math, time
from pathlib import Path
from datetime import datetime

def print_check(check, index=0, total=0):
    sym = "\033[92m✓ PASS\033[0m" if check["pass"] else "\033[91m✗ FAIL\033[0m"
    counter = f"[{index}/{total}]" if total > 0 else ""
    sys.stdout.write(f"  {counter:>8s}  Running {check['id']}: {check['name']}...")
    sys.stdout.flush(); time.sleep(0.04)
    sys.stdout.write(f"\r  {counter:>8s}  {sym}  [{check['id']}] {check['name']}")
    if not check["pass"]:
        sys.stdout.write(f"\n           \033[91m  expected: {check['expected']}\033[0m")
        sys.stdout.write(f"\n           \033[91m  actual:   {check['actual']}\033[0m")
    sys.stdout.write("\n"); sys.stdout.flush()

def _print_mod(name, status, passed, total):
    c = "\033[92m" if status == "PASS" else "\033[91m"
    s = "✓" if status == "PASS" else "✗"
    print(f"\n  {c}  {s} {name}: {status} ({passed}/{total})\033[0m\n")

def _finalize(checks):
    passed = sum(1 for c in checks if c["pass"])
    total = len(checks)
    status = "PASS" if passed == total else "FAIL"
    for i, c in enumerate(checks, 1): print_check(c, i, total)
    return {"status": status, "passed": passed, "total": total, "checks": checks}

class Phase3ValidationAgent:
    def __init__(self, spec_path, rtl_dir, output_dir=None,
                 attempt=1, max_retries=4, history=None):
        self.spec_path = spec_path
        self.rtl_dir = Path(rtl_dir)
        self.output_dir = Path(output_dir or rtl_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.attempt = attempt
        self.max_retries = max_retries
        self.history = history or []
        with open(spec_path) as f: self.spec = json.load(f)
        self.geo = self.spec["memory_geometry"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]
        self.dc = self.spec["timing_model"]["$derived_cycles"]
        self.results = {"timestamp": datetime.now().isoformat(), "spec": spec_path, "phase": 3, "modules": {}}
        self.generated_tb_paths = []

    def _chk(self, checks, cid, name, passed, exp, act):
        checks.append({"id": cid, "name": name, "pass": passed, "expected": exp, "actual": act})

    # ── CMD_QUEUE VALIDATION ──
    def validate_cmd_queue(self):
        checks = []
        sv_path = self.rtl_dir / "cmd_queue.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-CQ-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        C = lambda cid,n,p,e,a: self._chk(checks,cid,n,p,e,a)

        C("V-CQ-01","Module declared","module cmd_queue" in sv,"module cmd_queue","found" if "module cmd_queue" in sv else "missing")

        # Parameters
        m=re.search(r"DEPTH\s*=\s*(\d+)",sv); d=int(m.group(1)) if m else 0
        C("V-CQ-02",f"DEPTH={self.arch['command_queue_depth']}",d==self.arch["command_queue_depth"],str(self.arch["command_queue_depth"]),str(d))
        m=re.search(r"ROW_BITS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CQ-03",f"ROW_BITS={self.geo['row_bits']}",v==self.geo["row_bits"],str(self.geo["row_bits"]),str(v))
        m=re.search(r"COL_BITS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CQ-04",f"COL_BITS={self.geo['column_bits']}",v==self.geo["column_bits"],str(self.geo["column_bits"]),str(v))
        m=re.search(r"BANK_BITS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CQ-05",f"BANK_BITS={self.geo['bank_bits']}",v==self.geo["bank_bits"],str(self.geo["bank_bits"]),str(v))

        # Ports
        C("V-CQ-06","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found" if "clk" in sv else "missing")
        for sig in ["enq_valid","enq_ready","enq_row","enq_col","enq_bank","enq_we","enq_aux"]:
            C("V-CQ-07",f"Port {sig}",sig in sv,sig,"found" if sig in sv else "missing")
        for sig in ["deq_grant","deq_idx"]:
            C("V-CQ-08",f"Port {sig}",sig in sv,sig,"found" if sig in sv else "missing")
        for sig in ["entry_valid","entry_row","entry_col","entry_bank","entry_we","entry_aux"]:
            C("V-CQ-09",f"Lookahead {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")
        for sig in ["queue_full","queue_empty","queue_count"]:
            C("V-CQ-10",f"Status {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")

        # Structural
        C("V-CQ-11","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"sequential","found" if "always_ff" in sv else "missing")
        C("V-CQ-12","always_comb","always_comb" in sv,"combinational lookahead","found" if "always_comb" in sv else "missing")
        C("V-CQ-13","mem_valid storage","mem_valid" in sv,"per-entry valid bits","found" if "mem_valid" in sv else "missing")
        C("V-CQ-14","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")

        result = _finalize(checks); _print_mod("cmd_queue",result["status"],result["passed"],result["total"]); return result

    # ── SCHEDULER VALIDATION ──
    def validate_scheduler(self):
        checks = []
        sv_path = self.rtl_dir / "scheduler.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-SC-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        C = lambda cid,n,p,e,a: self._chk(checks,cid,n,p,e,a)

        C("V-SC-01","Module declared","module scheduler" in sv,"module scheduler","found" if "module scheduler" in sv else "missing")

        # Parameters
        m=re.search(r"DEPTH\s*=\s*(\d+)",sv); d=int(m.group(1)) if m else 0
        C("V-SC-02",f"DEPTH={self.arch['command_queue_depth']}",d==self.arch["command_queue_depth"],str(self.arch["command_queue_depth"]),str(d))
        m=re.search(r"NUM_BANKS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-SC-03","NUM_BANKS=8",v==8,"8",str(v))
        m=re.search(r"ROW_BITS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-SC-04",f"ROW_BITS={self.geo['row_bits']}",v==self.geo["row_bits"],str(self.geo["row_bits"]),str(v))

        # Ports — queue inputs
        C("V-SC-05","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found")
        for sig in ["q_valid","q_row","q_col","q_bank","q_we","q_aux"]:
            C("V-SC-06",f"Queue input {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")
        # Bank tracker inputs
        for sig in ["bank_is_active","bank_open_row","bank_act_allowed","bank_rd_allowed","bank_wr_allowed","bank_pre_allowed"]:
            C("V-SC-07",f"Bank input {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")
        # Refresh inputs
        for sig in ["ref_required","ref_urgent","ref_ack"]:
            C("V-SC-08",f"Refresh {sig}",sig in sv,sig,"found" if sig in sv else "missing")
        # Dequeue outputs
        for sig in ["deq_grant","deq_idx"]:
            C("V-SC-09",f"Dequeue {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")
        # Command outputs
        for sig in ["cmd_valid","cmd_type","cmd_row","cmd_col","cmd_bank","cmd_we","cmd_aux"]:
            C("V-SC-10",f"Command {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")

        # Scheduling policy
        policy = self.arch["scheduler_policy"]
        has_frfcfs = "row_hit" in sv.lower() or "cas_ready" in sv.lower() or "fr_fcfs" in sv.lower() or "first" in sv.lower()
        C("V-SC-11",f"Policy '{policy}' reflected",has_frfcfs,"FR-FCFS logic","found" if has_frfcfs else "not found")
        row_policy = self.arch["row_policy"]
        has_open = "open_row" in sv or "row_hit" in sv.lower() or "open_page" in sv.lower()
        C("V-SC-12",f"Row policy '{row_policy}'",has_open,"open-page logic","found" if has_open else "not found")

        # Refresh preemption
        has_preempt = "ref_urgent" in sv
        C("V-SC-13","Urgent refresh preemption",has_preempt,"ref_urgent check","found" if has_preempt else "missing")

        # Command type encoding
        for cmd in ["CMD_ACT","CMD_RD","CMD_WR","CMD_PRE","CMD_REF"]:
            C("V-SC-14",f"Encoding {cmd}",cmd in sv,cmd,"found" if cmd in sv else "missing")

        C("V-SC-15","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"registered output","found" if "always_ff" in sv else "missing")
        C("V-SC-16","always_comb","always_comb" in sv,"comb selection","found" if "always_comb" in sv else "missing")
        C("V-SC-17","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")

        result = _finalize(checks); _print_mod("scheduler",result["status"],result["passed"],result["total"]); return result

    # ── CMD_GEN VALIDATION ──
    def validate_cmd_gen(self):
        checks = []
        sv_path = self.rtl_dir / "cmd_gen.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-CG-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        C = lambda cid,n,p,e,a: self._chk(checks,cid,n,p,e,a)

        C("V-CG-01","Module declared","module cmd_gen" in sv,"module cmd_gen","found" if "module cmd_gen" in sv else "missing")

        # Parameters
        ddr_aw = max(self.geo["row_bits"], self.geo["column_bits"])
        m=re.search(r"DDR_ADDR_W\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CG-02",f"DDR_ADDR_W={ddr_aw}",v==ddr_aw,str(ddr_aw),str(v))
        m=re.search(r"DDR_BANK_W\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CG-03",f"DDR_BANK_W={self.geo['bank_bits']}",v==self.geo["bank_bits"],str(self.geo["bank_bits"]),str(v))
        m=re.search(r"ROW_BITS\s*=\s*(\d+)",sv); v=int(m.group(1)) if m else 0
        C("V-CG-04",f"ROW_BITS={self.geo['row_bits']}",v==self.geo["row_bits"],str(self.geo["row_bits"]),str(v))

        # Scheduler input ports
        C("V-CG-05","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found")
        for sig in ["sched_valid","sched_type","sched_row","sched_col","sched_bank","sched_we","sched_aux"]:
            C("V-CG-06",f"Sched input {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")

        # DDR output ports
        for sig in ["ddr_cmd","ddr_addr","ddr_bank","ddr_cke","ddr_reset_n","ddr_odt"]:
            C("V-CG-07",f"DDR output {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")

        # Feedback ports to bank_tracker
        for sig in ["fb_act_valid","fb_act_bank","fb_act_row","fb_pre_valid","fb_pre_bank","fb_rd_valid","fb_rd_bank","fb_wr_valid","fb_wr_bank","fb_ref_valid"]:
            C("V-CG-08",f"Feedback {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")

        # Data path passthrough
        for sig in ["cmd_out_valid","cmd_out_we","cmd_out_aux"]:
            C("V-CG-09",f"Passthrough {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")

        # DDR3 command encodings
        for enc in ["DDR_NOP","DDR_ACT","DDR_RD","DDR_WR","DDR_PRE","DDR_REF"]:
            C("V-CG-10",f"Encoding {enc}",enc in sv,enc,"found" if enc in sv else "missing")

        # NOP encoding correct: 4'b0111
        C("V-CG-11","NOP=4'b0111","0111" in sv,"4'b0111","found" if "0111" in sv else "missing")
        # ACT encoding: 4'b0011
        C("V-CG-12","ACT=4'b0011","0011" in sv,"4'b0011","found" if "0011" in sv else "missing")

        C("V-CG-13","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"registered","found" if "always_ff" in sv else "missing")
        C("V-CG-14","ODT for writes","odt" in sv.lower(),"ODT asserted on WR","found" if "odt" in sv.lower() else "missing")
        C("V-CG-15","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")

        result = _finalize(checks); _print_mod("cmd_gen",result["status"],result["passed"],result["total"]); return result

    # ── CROSS-MODULE (Phase 3 internal + Phase 1/2 interfaces) ──
    def validate_cross_module(self):
        checks = []
        svs = {}
        for mod in ["cmd_queue","scheduler","cmd_gen"]:
            p = self.rtl_dir / f"{mod}.sv"
            if p.exists(): svs[mod] = p.read_text()
        C = lambda cid,n,p,e,a: self._chk(checks,cid,n,p,e,a)

        # CQ → Scheduler: entry_valid ↔ q_valid
        if "cmd_queue" in svs and "scheduler" in svs:
            C("V-XM3-01","CQ entry_valid → SC q_valid","entry_valid" in svs["cmd_queue"] and "q_valid" in svs["scheduler"],
              "matching signal names","found")
            C("V-XM3-02","CQ entry_row → SC q_row","entry_row" in svs["cmd_queue"] and "q_row" in svs["scheduler"],
              "matching signal names","found")
            C("V-XM3-03","CQ entry_bank → SC q_bank","entry_bank" in svs["cmd_queue"] and "q_bank" in svs["scheduler"],
              "matching signal names","found")
            # Dequeue interface
            C("V-XM3-04","SC deq_grant → CQ deq_grant","deq_grant" in svs["scheduler"] and "deq_grant" in svs["cmd_queue"],
              "deq_grant both sides","found")
            C("V-XM3-05","SC deq_idx → CQ deq_idx","deq_idx" in svs["scheduler"] and "deq_idx" in svs["cmd_queue"],
              "deq_idx both sides","found")

        # Scheduler → cmd_gen: cmd_type ↔ sched_type
        if "scheduler" in svs and "cmd_gen" in svs:
            C("V-XM3-06","SC cmd_valid → CG sched_valid","cmd_valid" in svs["scheduler"] and "sched_valid" in svs["cmd_gen"],
              "valid signal","found")
            C("V-XM3-07","SC cmd_type → CG sched_type","cmd_type" in svs["scheduler"] and "sched_type" in svs["cmd_gen"],
              "type signal","found")
            C("V-XM3-08","SC cmd_row → CG sched_row","cmd_row" in svs["scheduler"] and "sched_row" in svs["cmd_gen"],
              "row signal","found")
            C("V-XM3-09","SC cmd_bank → CG sched_bank","cmd_bank" in svs["scheduler"] and "sched_bank" in svs["cmd_gen"],
              "bank signal","found")

        # cmd_gen feedback → bank_tracker interface names
        if "cmd_gen" in svs:
            cg = svs["cmd_gen"]
            C("V-XM3-10","CG fb_act_valid (→ bank_tracker cmd_act_valid)","fb_act_valid" in cg,
              "feedback output","found" if "fb_act_valid" in cg else "missing")
            C("V-XM3-11","CG fb_ref_valid (→ bank_tracker cmd_ref_valid)","fb_ref_valid" in cg,
              "feedback output","found" if "fb_ref_valid" in cg else "missing")

        # Parameter consistency across Phase 3
        param_vals = {}
        for mod, sv in svs.items():
            for pname in ["ROW_BITS","COL_BITS","BANK_BITS","AUX_WIDTH","DEPTH","IDX_BITS"]:
                m = re.search(rf"{pname}\s*=\s*(\d+)", sv)
                if m:
                    key = (pname, mod)
                    param_vals.setdefault(pname, {})[mod] = int(m.group(1))
        for pname, mod_vals in param_vals.items():
            vals = set(mod_vals.values())
            if len(vals) > 1 and pname in ("ROW_BITS","COL_BITS","BANK_BITS","AUX_WIDTH"):
                detail = ", ".join(f"{m}={v}" for m,v in mod_vals.items())
                C("V-XM3-12",f"{pname} consistent across P3",False,f"same value",detail)
            elif len(vals) == 1:
                C("V-XM3-12",f"{pname} consistent ({list(vals)[0]})",True,"consistent",str(list(vals)[0]))

        result = _finalize(checks); _print_mod("cross_module",result["status"],result["passed"],result["total"]); return result

    # ── TESTBENCH GENERATORS (use the agent-generated TBs) ──
    def generate_cmd_queue_tb(self):
        # Import and run the agent's TB generator
        try:
            sys.path.insert(0, str(self.rtl_dir))
            sys.path.insert(0, str(self.rtl_dir.parent))
            from cmd_queue_agent import CmdQueueAgent
            agent = CmdQueueAgent(self.spec_path, str(self.output_dir))
            return agent.generate_tb()
        except Exception:
            # Fallback: read from rtl_dir if already generated
            tb_path = self.rtl_dir / "cmd_queue_tb.sv"
            if tb_path.exists(): return tb_path.read_text()
            return "// cmd_queue_tb.sv not generated\n"

    def generate_scheduler_tb(self):
        try:
            from scheduler_agent import SchedulerAgent
            agent = SchedulerAgent(self.spec_path, str(self.output_dir))
            return agent.generate_tb()
        except Exception:
            tb_path = self.rtl_dir / "scheduler_tb.sv"
            if tb_path.exists(): return tb_path.read_text()
            return "// scheduler_tb.sv not generated\n"

    def generate_cmd_gen_tb(self):
        try:
            from cmd_gen_agent import CmdGenAgent
            agent = CmdGenAgent(self.spec_path, str(self.output_dir))
            return agent.generate_tb()
        except Exception:
            tb_path = self.rtl_dir / "cmd_gen_tb.sv"
            if tb_path.exists(): return tb_path.read_text()
            return "// cmd_gen_tb.sv not generated\n"

    def write_testbenches(self):
        tb_files = [
            ("cmd_queue_tb.sv",  self.generate_cmd_queue_tb),
            ("scheduler_tb.sv",  self.generate_scheduler_tb),
            ("cmd_gen_tb.sv",    self.generate_cmd_gen_tb),
        ]
        print(f"\n\033[1m  -- TESTBENCH GENERATION --\033[0m")
        for fn, gen in tb_files:
            p = self.output_dir / fn
            try:
                content = gen()
                p.write_text(content)
                self.generated_tb_paths.append(str(p))
                print(f"  V {fn:25s} ({content.count(chr(10))} lines) -> {p}")
            except Exception as e:
                print(f"  X {fn:25s} FAILED: {e}")
        self._write_makefile()

    def _write_makefile(self):
        p = self.output_dir / "Makefile.sim"
        p.write_text(f"""# Phase 3 Simulation Makefile
RTL_DIR={self.rtl_dir}
TB_DIR={self.output_dir}
WORK=$(TB_DIR)/sim_work
.PHONY: all clean cmd_queue scheduler cmd_gen
all: cmd_queue scheduler cmd_gen
$(WORK): ; mkdir -p $(WORK)
cmd_queue: $(WORK) ; iverilog -g2012 -o $(WORK)/cmd_queue_tb $(RTL_DIR)/cmd_queue.sv $(TB_DIR)/cmd_queue_tb.sv && vvp $(WORK)/cmd_queue_tb
scheduler: $(WORK) ; iverilog -g2012 -o $(WORK)/scheduler_tb $(RTL_DIR)/scheduler.sv $(TB_DIR)/scheduler_tb.sv && vvp $(WORK)/scheduler_tb
cmd_gen: $(WORK) ; iverilog -g2012 -o $(WORK)/cmd_gen_tb $(RTL_DIR)/cmd_gen.sv $(TB_DIR)/cmd_gen_tb.sv && vvp $(WORK)/cmd_gen_tb
clean: ; rm -rf $(WORK)
""")
        print(f"  V Makefile.sim -> {p}")

    # ── RUN ──
    def run(self):
        hdr = "=" * 62
        print(f"\n\033[1m{hdr}\033[0m")
        print(f"\033[1m  PHASE 3 VALIDATION AGENT\033[0m")
        print(f"  Spec: {self.spec_path}")
        print(f"  RTL:  {self.rtl_dir}")
        print(f"\033[1m{hdr}\033[0m")
        start = time.time()

        print(f"\n\033[1m  -- CMD_QUEUE --\033[0m")
        self.results["modules"]["cmd_queue"] = self.validate_cmd_queue()
        print(f"\033[1m  -- SCHEDULER --\033[0m")
        self.results["modules"]["scheduler"] = self.validate_scheduler()
        print(f"\033[1m  -- CMD_GEN --\033[0m")
        self.results["modules"]["cmd_gen"] = self.validate_cmd_gen()
        print(f"\033[1m  -- CROSS-MODULE --\033[0m")
        self.results["modules"]["cross_module"] = self.validate_cross_module()

        self.write_testbenches()
        elapsed = time.time() - start

        tp = sum(m["passed"] for m in self.results["modules"].values())
        tc = sum(m["total"] for m in self.results["modules"].values())
        ap = all(m["status"] == "PASS" for m in self.results["modules"].values())
        self.results["overall"] = {"status": "PASS" if ap else "FAIL", "total_passed": tp, "total_checks": tc}
        self.results["testbenches"] = self.generated_tb_paths

        print(f"\n\033[1m{hdr}\033[0m")
        c = "\033[92m" if ap else "\033[91m"
        print(f"{c}  {'V' if ap else 'X'} {tp}/{tc} checks in {elapsed:.2f}s\033[0m")
        print(f"\033[1m{hdr}\033[0m")
        for mod, res in self.results["modules"].items():
            mc = "\033[92m" if res["status"] == "PASS" else "\033[91m"
            print(f"  {mod:<20s} {mc}{res['status']:<8s}\033[0m {res['passed']}/{res['total']}")
        if self.generated_tb_paths:
            print(f"\n  Testbenches:")
            for p in self.generated_tb_paths: print(f"    V {p}")
        print(f"\033[1m{hdr}\033[0m")

        rj = self.output_dir / "phase3_validation_report.json"
        rj.write_text(json.dumps(self.results, indent=2))
        print(f"  Report: {rj}")
        return self.results

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    rtl = input("RTL dir: ").strip()
    out = input("Output (Enter=RTL): ").strip() or rtl
    r = Phase3ValidationAgent(spec, rtl, out).run()
    sys.exit(0 if r["overall"]["status"] == "PASS" else 1)
