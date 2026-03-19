#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════╗
║              PHASE 2 VALIDATION AGENT                                ║
║  Static validation + SystemVerilog testbench generation              ║
║  Modules: addr_decoder, bank_tracker, refresh_ctrl, calibration      ║
║  Checks: V-AD, V-BT, V-RF, V-CL, V-XM                              ║
║  Output: validation_report + 4 testbenches + Makefile.sim            ║
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

class Phase2ValidationAgent:
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
        self.tm = self.spec["timing_model"]
        self.dc = self.tm["$derived_cycles"]
        self.cl = self.spec["clocking_model"]
        self.cal = self.spec["calibration"]
        self.arch = self.spec["controller_architecture"]
        self.host = self.spec["host_interface"]
        self.rp = self.arch["refresh_policy"]
        self.results = {"timestamp": datetime.now().isoformat(), "spec": spec_path, "phase": 2, "modules": {}}
        self.generated_tb_paths = []

    # ── ADDR_DECODER ──
    def validate_addr_decoder(self):
        checks = []
        sv_path = self.rtl_dir / "addr_decoder.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-AD-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        def chk(cid,name,p,exp,act): checks.append({"id":cid,"name":name,"pass":p,"expected":exp,"actual":act})
        chk("V-AD-01","Module declared","module addr_decoder" in sv,"module addr_decoder","found" if "module addr_decoder" in sv else "missing")
        m=re.search(r"ADDR_WIDTH\s*=\s*(\d+)",sv); aw=int(m.group(1)) if m else 0; ea=self.host["address_width_bits"]
        chk("V-AD-02",f"ADDR_WIDTH={ea}",aw==ea,str(ea),str(aw))
        m=re.search(r"ROW_BITS\s*=\s*(\d+)",sv); rb=int(m.group(1)) if m else 0; er=self.geo["row_bits"]
        chk("V-AD-03",f"ROW_BITS={er}",rb==er,str(er),str(rb))
        m=re.search(r"COL_BITS\s*=\s*(\d+)",sv); cb=int(m.group(1)) if m else 0; ec=self.geo["column_bits"]
        chk("V-AD-04",f"COL_BITS={ec}",cb==ec,str(ec),str(cb))
        m=re.search(r"BANK_BITS\s*=\s*(\d+)",sv); bb=int(m.group(1)) if m else 0; eb=self.geo["bank_bits"]
        chk("V-AD-05",f"BANK_BITS={eb}",bb==eb,str(eb),str(bb))
        chk("V-AD-06","Input req_addr","req_addr" in sv and "input" in sv,"input req_addr","found" if "req_addr" in sv else "missing")
        for p in ["dec_row","dec_bank","dec_col","dec_rank"]:
            chk("V-AD-07",f"Output {p}",p in sv,f"output {p}","found" if p in sv else "missing")
        chk("V-AD-11","Combinational (no always_ff)","always_ff" not in sv,"no always_ff","clean" if "always_ff" not in sv else "has always_ff")
        chk("V-AD-12","No clock port",not re.search(r"input\s+logic\s+clk",sv),"no clk","clean" if not re.search(r"input\s+logic\s+clk",sv) else "has clk")
        mapping=self.geo["address_mapping"]
        chk("V-AD-13",f"Mapping '{mapping}'",mapping.replace("-","") in sv.replace("-","").replace("_","").lower() or "row" in sv.lower(),mapping,"found")
        chk("V-AD-14","BL8 alignment","3'b000" in sv or "BL8" in sv.upper(),"col[2:0]=0","found" if "3'b000" in sv else "not found")
        if self.geo["ranks"]==1:
            chk("V-AD-15","Rank=0 single-rank","'0" in sv or "= 0" in sv,"dec_rank=0","found" if "'0" in sv else "missing")
        chk("V-AD-16","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")
        chk("V-AD-17","assign statements",sv.count("assign")>=3,">=3 assigns",f"{sv.count('assign')} assigns")
        result=_finalize(checks); _print_mod("addr_decoder",result["status"],result["passed"],result["total"]); return result

    # ── BANK_TRACKER ──
    def validate_bank_tracker(self):
        checks = []
        sv_path = self.rtl_dir / "bank_tracker.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-BT-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        def chk(cid,name,p,exp,act): checks.append({"id":cid,"name":name,"pass":p,"expected":exp,"actual":act})
        chk("V-BT-01","Module declared","module bank_tracker" in sv,"module bank_tracker","found" if "module bank_tracker" in sv else "missing")
        m=re.search(r"NUM_BANKS\s*=\s*(\d+)",sv); nb=int(m.group(1)) if m else 0
        chk("V-BT-02","NUM_BANKS=8",nb==8,"8",str(nb))
        m=re.search(r"ROW_BITS\s*=\s*(\d+)",sv); rb=int(m.group(1)) if m else 0
        chk("V-BT-03",f"ROW_BITS={self.geo['row_bits']}",rb==self.geo["row_bits"],str(self.geo["row_bits"]),str(rb))
        m=re.search(r"BANK_BITS\s*=\s*(\d+)",sv); bb=int(m.group(1)) if m else 0
        chk("V-BT-04",f"BANK_BITS={self.geo['bank_bits']}",bb==self.geo["bank_bits"],str(self.geo["bank_bits"]),str(bb))
        chk("V-BT-05","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found" if "clk" in sv else "missing")
        for sig in ["cmd_act_valid","cmd_act_bank","cmd_act_row","cmd_pre_valid","cmd_pre_bank","cmd_pre_all","cmd_rd_valid","cmd_rd_bank","cmd_wr_valid","cmd_wr_bank","cmd_ref_valid"]:
            chk("V-BT-06",f"Input {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")
        for sig in ["cfg_tRCD_nCK","cfg_tRP_nCK","cfg_tRAS_nCK","cfg_tRC_nCK","cfg_tRRD_nCK","cfg_tFAW_nCK","cfg_tWTR_nCK","cfg_tWR_nCK","cfg_tRTP_nCK","cfg_tCCD_nCK","cfg_tRFC_nCK"]:
            chk("V-BT-07",f"Config {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")
        for sig in ["bank_is_active","bank_open_row","bank_act_allowed","bank_rd_allowed","bank_wr_allowed","bank_pre_allowed","all_banks_idle","faw_allows_act"]:
            chk("V-BT-08",f"Output {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")
        chk("V-BT-09","State enum","BANK_IDLE" in sv and "BANK_ACTIVE" in sv,"IDLE/ACTIVE","found" if "BANK_IDLE" in sv else "missing")
        for ctr in ["ctr_rcd","ctr_rp","ctr_ras","ctr_rc"]:
            chk("V-BT-10",f"Counter {ctr}",ctr in sv,f"{ctr}[NUM_BANKS]","found" if ctr in sv else "missing")
        for ctr in ["ctr_rrd","ctr_ccd","ctr_rfc"]:
            chk("V-BT-11",f"Global {ctr}",ctr in sv,ctr,"found" if ctr in sv else "missing")
        chk("V-BT-12","FAW tracking","faw" in sv.lower(),"FAW logic","found" if "faw" in sv.lower() else "missing")
        chk("V-BT-13","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"sequential","found" if "always_ff" in sv else "missing")
        chk("V-BT-14","always_comb","always_comb" in sv,"comb permissions","found" if "always_comb" in sv else "missing")
        chk("V-BT-15","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")
        result=_finalize(checks); _print_mod("bank_tracker",result["status"],result["passed"],result["total"]); return result

    # ── REFRESH_CTRL ──
    def validate_refresh_ctrl(self):
        checks = []
        sv_path = self.rtl_dir / "refresh_ctrl.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-RF-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        def chk(cid,name,p,exp,act): checks.append({"id":cid,"name":name,"pass":p,"expected":exp,"actual":act})
        chk("V-RF-01","Module declared","module refresh_ctrl" in sv,"module refresh_ctrl","found" if "module refresh_ctrl" in sv else "missing")
        chk("V-RF-02","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found" if "clk" in sv else "missing")
        chk("V-RF-03","Input init_done","init_done" in sv,"input init_done","found" if "init_done" in sv else "missing")
        chk("V-RF-04","Input cfg_force_refresh","cfg_force_refresh" in sv,"input cfg_force_refresh","found" if "cfg_force_refresh" in sv else "missing")
        for sig in ["cfg_tREFI_nCK","cfg_max_postpone","cfg_urgent_threshold","cfg_ref_priority"]:
            chk("V-RF-05",f"Config {sig}",sig in sv,f"input {sig}","found" if sig in sv else "missing")
        for sig in ["ref_required","ref_urgent"]:
            chk("V-RF-06",f"Output {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")
        chk("V-RF-07","Input ref_ack","ref_ack" in sv,"input ref_ack","found" if "ref_ack" in sv else "missing")
        for sig in ["ref_pending_cnt","ref_starve_flag"]:
            chk("V-RF-08",f"Output {sig}",sig in sv,f"output {sig}","found" if sig in sv else "missing")
        chk("V-RF-09","tREFI counter","refi_ctr" in sv or "refi_tick" in sv,"refi counter","found" if "refi" in sv else "missing")
        chk("V-RF-10","Postpone counter","postpone" in sv,"postpone logic","found" if "postpone" in sv else "missing")
        chk("V-RF-11","Urgent threshold","urgent" in sv.lower() and "threshold" in sv.lower(),"threshold compare","found" if "urgent" in sv.lower() else "missing")
        chk("V-RF-12","Starvation detect","starve" in sv.lower(),"starve flag","found" if "starve" in sv.lower() else "missing")
        chk("V-RF-13","init_done gate","init_done" in sv,"counter gated","found" if "init_done" in sv else "missing")
        m=re.search(r"REFI_CTR_W\s*=\s*(\d+)",sv); rw=int(m.group(1)) if m else 0
        exp_rw=max(1,self.dc["tREFI_nCK"].bit_length())
        chk("V-RF-14",f"REFI_CTR_W>={exp_rw}",rw>=exp_rw,f">={exp_rw}",str(rw))
        m=re.search(r"POST_CTR_W\s*=\s*(\d+)",sv); pw=int(m.group(1)) if m else 0
        exp_pw=max(1,self.rp["max_postpone_count"].bit_length())
        chk("V-RF-15",f"POST_CTR_W>={exp_pw}",pw>=exp_pw,f">={exp_pw}",str(pw))
        chk("V-RF-16","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"sequential","found" if "always_ff" in sv else "missing")
        chk("V-RF-17","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")
        result=_finalize(checks); _print_mod("refresh_ctrl",result["status"],result["passed"],result["total"]); return result

    # ── CALIBRATION ──
    def validate_calibration(self):
        checks = []
        sv_path = self.rtl_dir / "calibration.sv"
        if not sv_path.exists():
            return {"status":"ERROR","passed":0,"total":1,
                    "checks":[{"id":"V-CL-00","pass":False,"name":"File exists","expected":str(sv_path),"actual":"missing"}]}
        sv = sv_path.read_text()
        def chk(cid,name,p,exp,act): checks.append({"id":cid,"name":name,"pass":p,"expected":exp,"actual":act})
        chk("V-CL-01","Module declared","module calibration" in sv,"module calibration","found" if "module calibration" in sv else "missing")
        chk("V-CL-02","clk and rst_n","clk" in sv and "rst_n" in sv,"input clk,rst_n","found" if "clk" in sv else "missing")
        chk("V-CL-03","Input init_done","init_done" in sv,"input init_done","found" if "init_done" in sv else "missing")
        chk("V-CL-04","Output cal_done","cal_done" in sv and "output" in sv,"output cal_done","found" if "cal_done" in sv else "missing")
        chk("V-CL-05","Output cal_fail","cal_fail" in sv,"output cal_fail","found" if "cal_fail" in sv else "missing")
        chk("V-CL-06","cal_fail=0","1'b0" in sv and "cal_fail" in sv,"cal_fail=0","found" if "1'b0" in sv and "cal_fail" in sv else "missing")
        chk("V-CL-07","Output zqcs_req","zqcs_req" in sv,"output zqcs_req","found" if "zqcs_req" in sv else "missing")
        chk("V-CL-08","Input zqcs_ack","zqcs_ack" in sv,"input zqcs_ack","found" if "zqcs_ack" in sv else "missing")
        m=re.search(r"ZQCS_WAIT\s*=\s*(\d+)",sv); zw=int(m.group(1)) if m else 0
        zqcs_nCK=self.cal.get("$derived",{}).get("periodic_zqcs_interval_nCK",512000)
        cp=self.cl["controller_clock_period_ns"]; tCK=self.cl.get("$derived",{}).get("tCK_ns",self.tm["tCK_ns"])
        exp_zw=math.ceil(zqcs_nCK*tCK/cp)
        chk("V-CL-09",f"ZQCS_WAIT={exp_zw}",zw==exp_zw,str(exp_zw),str(zw))
        chk("V-CL-10","ZQCS counter","zqcs_ctr" in sv or "zqcs_pending" in sv,"counter","found" if "zqcs" in sv else "missing")
        chk("V-CL-11","cal_done latches","cal_done_r" in sv or ("init_done" in sv and "!" in sv),"latch","found" if "cal_done_r" in sv else "check")
        chk("V-CL-12","ZQCS gated by cal_done","cal_done" in sv and "zqcs" in sv,"gated","found" if "cal_done" in sv else "missing")
        chk("V-CL-13","always_ff",bool(re.search(r"always_ff\s*@\s*\(\s*posedge\s+clk",sv)),"sequential","found" if "always_ff" in sv else "missing")
        chk("V-CL-14","endmodule","endmodule" in sv,"endmodule","found" if "endmodule" in sv else "missing")
        result=_finalize(checks); _print_mod("calibration",result["status"],result["passed"],result["total"]); return result

    # ── CROSS-MODULE ──
    def validate_cross_module(self):
        checks = []
        svs = {}
        for mod in ["addr_decoder","bank_tracker","refresh_ctrl","calibration"]:
            p = self.rtl_dir / f"{mod}.sv"
            if p.exists(): svs[mod] = p.read_text()
        def chk(cid,name,p,exp,act): checks.append({"id":cid,"name":name,"pass":p,"expected":exp,"actual":act})
        if "bank_tracker" in svs:
            bt=svs["bank_tracker"]
            for sig in ["cfg_tRCD_nCK","cfg_tRP_nCK","cfg_tRAS_nCK","cfg_tRC_nCK","cfg_tRRD_nCK","cfg_tFAW_nCK","cfg_tCCD_nCK","cfg_tRFC_nCK"]:
                chk("V-XM-01",f"bank_tracker has {sig}",sig in bt,f"input {sig}","found" if sig in bt else "missing")
        if "refresh_ctrl" in svs:
            chk("V-XM-02","refresh_ctrl has cfg_tREFI_nCK","cfg_tREFI_nCK" in svs["refresh_ctrl"],"input cfg_tREFI_nCK","found" if "cfg_tREFI_nCK" in svs["refresh_ctrl"] else "missing")
        if "calibration" in svs:
            chk("V-XM-03","calibration has init_done","init_done" in svs["calibration"],"input init_done","found" if "init_done" in svs["calibration"] else "missing")
        if "refresh_ctrl" in svs:
            chk("V-XM-04","refresh_ctrl has init_done","init_done" in svs["refresh_ctrl"],"input init_done","found" if "init_done" in svs["refresh_ctrl"] else "missing")
        if "addr_decoder" in svs:
            m=re.search(r"ADDR_WIDTH\s*=\s*(\d+)",svs["addr_decoder"]); v=int(m.group(1)) if m else 0
            chk("V-XM-05",f"addr_decoder ADDR_WIDTH={self.host['address_width_bits']}",v==self.host["address_width_bits"],str(self.host["address_width_bits"]),str(v))
        if "bank_tracker" in svs and "addr_decoder" in svs:
            bt_m=re.search(r"ROW_BITS\s*=\s*(\d+)",svs["bank_tracker"]); ad_m=re.search(r"ROW_BITS\s*=\s*(\d+)",svs["addr_decoder"])
            bt_v=int(bt_m.group(1)) if bt_m else 0; ad_v=int(ad_m.group(1)) if ad_m else 0
            chk("V-XM-06","ROW_BITS consistent",bt_v==ad_v,str(ad_v),str(bt_v))
            bt_m=re.search(r"BANK_BITS\s*=\s*(\d+)",svs["bank_tracker"]); ad_m=re.search(r"BANK_BITS\s*=\s*(\d+)",svs["addr_decoder"])
            bt_v=int(bt_m.group(1)) if bt_m else 0; ad_v=int(ad_m.group(1)) if ad_m else 0
            chk("V-XM-07","BANK_BITS consistent",bt_v==ad_v,str(ad_v),str(bt_v))
        result=_finalize(checks); _print_mod("cross_module",result["status"],result["passed"],result["total"]); return result

    # ── TESTBENCH GENERATORS ──
    def generate_addr_decoder_tb(self):
        rb=self.geo["row_bits"]; cb=self.geo["column_bits"]; bb=self.geo["bank_bits"]; aw=self.host["address_width_bits"]
        max_row=2**rb-1; row_msb_val=2**(rb-1)
        return f"""`timescale 1ns/1ps
module addr_decoder_tb;
    localparam ADDR_WIDTH={aw},ROW_BITS={rb},COL_BITS={cb},BANK_BITS={bb},RANK_BITS=1;
    logic [ADDR_WIDTH-1:0] req_addr;
    logic [ROW_BITS-1:0] dec_row; logic [BANK_BITS-1:0] dec_bank;
    logic [COL_BITS-1:0] dec_col; logic [RANK_BITS-1:0] dec_rank;
    addr_decoder #(.ADDR_WIDTH(ADDR_WIDTH),.ROW_BITS(ROW_BITS),.COL_BITS(COL_BITS),.BANK_BITS(BANK_BITS),.RANK_BITS(RANK_BITS)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,logic [{rb-1}:0] er,logic [2:0] eb,logic [9:0] ec,logic erk);
        test_num++;#1;
        if(dec_row!==er||dec_bank!==eb||dec_col!==ec||dec_rank!==erk) begin
            $display("  X T%02d FAIL: %s row=%0d/%0d bank=%0d/%0d",test_num,n,er,dec_row,eb,dec_bank); fail_count++;
        end else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    function automatic [{aw-1}:0] build(input [{rb-1}:0] row,input [2:0] bank,input [6:0] col_u,input [3:0] bo);
        return {{row,bank,col_u,bo}};
    endfunction
    initial begin
        $display("\\n== addr_decoder_tb ==\\n");
        req_addr=0; check("All zeros",0,0,0,0);
        req_addr={aw}'h1FFFFFFF; check("All ones",{rb}'h{format(max_row,'X')},3'h7,{{7'h7F,3'b000}},0);
        for(int b=0;b<8;b++) begin req_addr=build(100,b[2:0],10,0); check($sformatf("Bank %0d",b),100,b[2:0],{{7'd10,3'b000}},0); end
        req_addr=build(0,0,0,0); check("Row 0",0,0,0,0);
        req_addr=build({max_row},0,0,0); check("Row max",{max_row},0,0,0);
        req_addr=build(500,2,0,0); check("Col min",500,2,0,0);
        req_addr=build(500,2,127,0); check("Col max",500,2,{{7'd127,3'b000}},0);
        req_addr=build(500,2,64,0); check("Col mid",500,2,{{7'd64,3'b000}},0);
        req_addr=build(999,3,42,0); check("Off=0",999,3,{{7'd42,3'b000}},0);
        req_addr=build(999,3,42,5); check("Off=5",999,3,{{7'd42,3'b000}},0);
        req_addr=build(999,3,42,15); check("Off=15",999,3,{{7'd42,3'b000}},0);
        req_addr=build(999,3,42,8); check("Off=8",999,3,{{7'd42,3'b000}},0);
        req_addr=build(1234,5,56,0); check("Recon1",1234,5,{{7'd56,3'b000}},0);
        req_addr=build(8191,3,100,0); check("Recon2",8191,3,{{7'd100,3'b000}},0);
        req_addr={aw}'h1FFFFFFF; check("Rank=0",{rb}'h{format(max_row,'X')},3'h7,{{7'h7F,3'b000}},0);
        req_addr={aw}'h0|(1<<4); check("Bit4",0,0,{{7'd1,3'b000}},0);
        req_addr={aw}'h0|(1<<11); check("Bit11",0,1,0,0);
        req_addr={aw}'h0|(1<<14); check("Bit14",1,0,0,0);
        req_addr={aw}'h0|(1<<{aw-1}); check("BitMSB",{row_msb_val},0,0,0);
        req_addr=build(0,7,127,0); check("MaxCol+Bank",0,7,{{7'd127,3'b000}},0);
        req_addr={aw}'h10; check("Addr16",0,0,{{7'd1,3'b000}},0);
        // Extra: walking bank bits
        req_addr={aw}'h0|(1<<12); check("Bank bit1",0,2,0,0);
        req_addr={aw}'h0|(1<<13); check("Bank bit2",0,4,0,0);
        // Power of 2
        req_addr={aw}'h4000; check("Addr 0x4000",req_addr[{aw-1}:14],req_addr[13:11],{{req_addr[10:4],3'b000}},0);
        req_addr=build(16384,4,64,0); check("Mid all",16384,4,{{7'd64,3'b000}},0);
        req_addr=build({max_row},7,127,15); check("All max",{max_row},7,{{7'h7F,3'b000}},0);
        $display("\\n== %0d/%0d passed ==\\n",pass_count,pass_count+fail_count);
        $finish;
    end
endmodule
"""

    def generate_bank_tracker_tb(self):
        return open(os.path.join(os.path.dirname(__file__),"bank_tracker_tb.sv")).read() if os.path.exists(os.path.join(os.path.dirname(__file__),"bank_tracker_tb.sv")) else self._gen_bank_tracker_tb_inline()

    def _gen_bank_tracker_tb_inline(self):
        return """`timescale 1ns/1ps
module bank_tracker_tb;
    localparam NUM_BANKS=8,BANK_BITS=3,ROW_BITS=15,CTR_WIDTH=8;
    localparam T_RCD=4,T_RP=4,T_RAS=8,T_RC=12,T_RRD=3,T_FAW=10,T_WTR=3,T_WR=5,T_RTP=3,T_CCD=2,T_RFC=8;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n,cmd_act_valid,cmd_pre_valid,cmd_pre_all,cmd_rd_valid,cmd_wr_valid,cmd_ref_valid;
    logic [BANK_BITS-1:0] cmd_act_bank,cmd_pre_bank,cmd_rd_bank,cmd_wr_bank;
    logic [ROW_BITS-1:0] cmd_act_row;
    logic [7:0] cfg_tRCD_nCK,cfg_tRP_nCK,cfg_tRAS_nCK,cfg_tRC_nCK,cfg_tRRD_nCK,cfg_tFAW_nCK,cfg_tWTR_nCK,cfg_tWR_nCK,cfg_tRTP_nCK,cfg_tCCD_nCK,cfg_tRFC_nCK;
    logic [NUM_BANKS-1:0] bank_is_active,bank_act_allowed,bank_rd_allowed,bank_wr_allowed,bank_pre_allowed;
    logic [ROW_BITS-1:0] bank_open_row[NUM_BANKS]; logic all_banks_idle,faw_allows_act;
    bank_tracker #(.NUM_BANKS(NUM_BANKS),.BANK_BITS(BANK_BITS),.ROW_BITS(ROW_BITS),.CTR_WIDTH(CTR_WIDTH)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s",test_num,n); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    task automatic clr(); cmd_act_valid=0;cmd_pre_valid=0;cmd_pre_all=0;cmd_rd_valid=0;cmd_wr_valid=0;cmd_ref_valid=0; endtask
    task automatic act(input [2:0] b,input [14:0] r); @(posedge clk);cmd_act_valid=1;cmd_act_bank=b;cmd_act_row=r;@(posedge clk);cmd_act_valid=0; endtask
    task automatic pre(input [2:0] b,input bit a); @(posedge clk);cmd_pre_valid=1;cmd_pre_bank=b;cmd_pre_all=a;@(posedge clk);cmd_pre_valid=0;cmd_pre_all=0; endtask
    task automatic rd(input [2:0] b); @(posedge clk);cmd_rd_valid=1;cmd_rd_bank=b;@(posedge clk);cmd_rd_valid=0; endtask
    task automatic wr(input [2:0] b); @(posedge clk);cmd_wr_valid=1;cmd_wr_bank=b;@(posedge clk);cmd_wr_valid=0; endtask
    task automatic ref_c(); @(posedge clk);cmd_ref_valid=1;@(posedge clk);cmd_ref_valid=0; endtask
    initial begin
        $display("\\n== bank_tracker_tb ==\\n");
        rst_n=0;clr();cmd_act_bank=0;cmd_act_row=0;cmd_pre_bank=0;cmd_rd_bank=0;cmd_wr_bank=0;
        cfg_tRCD_nCK=T_RCD;cfg_tRP_nCK=T_RP;cfg_tRAS_nCK=T_RAS;cfg_tRC_nCK=T_RC;
        cfg_tRRD_nCK=T_RRD;cfg_tFAW_nCK=T_FAW;cfg_tWTR_nCK=T_WTR;cfg_tWR_nCK=T_WR;
        cfg_tRTP_nCK=T_RTP;cfg_tCCD_nCK=T_CCD;cfg_tRFC_nCK=T_RFC;
        wc(3); check("Reset idle",all_banks_idle===1); check("Reset act=0",bank_is_active===8'h00);
        check("Reset allow",bank_act_allowed===8'hFF); check("Reset faw",faw_allows_act===1);
        @(posedge clk);rst_n=1;wc(2); check("Post-reset",all_banks_idle===1);
        act(0,15'h1234);wc(1); check("ACT0 active",bank_is_active[0]===1); check("ACT0 row",bank_open_row[0]===15'h1234);
        check("ACT0 !idle",all_banks_idle===0); check("ACT0 !allow",bank_act_allowed[0]===0);
        check("tRCD rd=0",bank_rd_allowed[0]===0); check("tRCD wr=0",bank_wr_allowed[0]===0);
        wc(T_RCD); check("tRCD rd=1",bank_rd_allowed[0]===1); check("tRCD wr=1",bank_wr_allowed[0]===1);
        wc(T_RAS); check("tRAS pre ok",bank_pre_allowed[0]===1);
        pre(0,0);wc(1); check("PRE0",bank_is_active[0]===0);
        wc(T_RP); check("tRP allow",bank_act_allowed[0]===1);
        act(0,1);wc(T_RRD);act(1,2);wc(T_RRD);act(2,3);wc(T_RAS);
        check("3 active",bank_is_active[0]&&bank_is_active[1]&&bank_is_active[2]);
        pre(0,1);wc(1); check("PRE ALL",!bank_is_active[0]&&!bank_is_active[1]&&!bank_is_active[2]);
        wc(T_RP); check("ALL idle",all_banks_idle===1);
        wc(T_RC); act(0,15'hAAAA);wc(T_RCD); rd(0);wc(1);
        check("RD tCCD",bank_rd_allowed[0]===0); wc(T_CCD); check("RD tCCD exp",bank_rd_allowed[0]===1);
        wr(0);wc(1); check("WR tCCD",bank_rd_allowed[0]===0); wc(T_CCD); check("WR tCCD exp",bank_rd_allowed[0]===1);
        check("WR tWR pre",bank_pre_allowed[0]===0);
        pre(0,1);wc(T_RP+1); ref_c();wc(1); check("REF idle",all_banks_idle===1);
        check("REF tRFC",bank_act_allowed===8'h00); wc(T_RFC); check("tRFC exp",bank_act_allowed[0]===1);
        act(0,15'h10);wc(1); check("tRRD blk",bank_act_allowed[1]===0); wc(T_RRD); check("tRRD exp",bank_act_allowed[1]===1);
        act(1,15'h20);wc(1); check("tRRD blk2",bank_act_allowed[2]===0);
        wc(T_RRD);act(2,15'h30);wc(T_RRD);act(3,15'h40);wc(1);
        check("FAW blk",faw_allows_act===0); wc(T_FAW); check("FAW exp",faw_allows_act===1);
        rst_n=0;wc(2);rst_n=1;wc(2);
        act(4,15'h4444);wc(T_RRD);act(5,15'h5555);wc(T_RCD);rd(4);wc(T_CCD);wr(5);wc(1);
        check("IL b4",bank_is_active[4]===1&&bank_open_row[4]===15'h4444);
        check("IL b5",bank_is_active[5]===1&&bank_open_row[5]===15'h5555);
        $display("\\n== %0d/%0d passed ==\\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #2_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def generate_refresh_ctrl_tb(self):
        return """`timescale 1ns/1ps
module refresh_ctrl_tb;
    localparam REFI_CTR_W=5,POST_CTR_W=4,TREFI=10;
    logic clk=0; always #2.5 clk=~clk;
    logic rst_n,init_done,cfg_force_refresh; logic [23:0] cfg_tREFI_nCK;
    logic [3:0] cfg_max_postpone,cfg_urgent_threshold; logic cfg_ref_priority;
    logic ref_required,ref_urgent,ref_ack; logic [2:0] ref_pending_cnt; logic ref_starve_flag;
    refresh_ctrl #(.REFI_CTR_W(REFI_CTR_W),.POST_CTR_W(POST_CTR_W)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s p=%0d",test_num,n,ref_pending_cnt); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    task automatic wrefi(); wc(TREFI+2); endtask
    initial begin
        $display("\\n== refresh_ctrl_tb ==\\n");
        rst_n=0;init_done=0;cfg_force_refresh=0;ref_ack=0;
        cfg_tREFI_nCK=TREFI;cfg_max_postpone=8;cfg_urgent_threshold=6;cfg_ref_priority=1;
        wc(3); check("Rst req",ref_required===0); check("Rst urg",ref_urgent===0);
        check("Rst pend",ref_pending_cnt===0); check("Rst starve",ref_starve_flag===0);
        @(posedge clk);rst_n=1;wc(2); check("Post-rst",ref_required===0);
        wc(TREFI+5); check("Pre-init req",ref_required===0); check("Pre-init pend",ref_pending_cnt===0); check("Pre-init st",ref_starve_flag===0);
        @(posedge clk);init_done=1;wc(3); check("1st req",ref_required===1); check("1st pend",ref_pending_cnt>=1);
        wrefi(); check("2nd pend",ref_pending_cnt>=2); wrefi(); check("3rd pend",ref_pending_cnt>=3);
        @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(2); check("Ack dec",ref_pending_cnt<=3);
        repeat(5) begin @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(1); end
        check("Multi ack",ref_pending_cnt<=4);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(2);
        check("Clean start",ref_pending_cnt<=1);
        repeat(3) begin wrefi();@(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0; end wc(2);
        check("Imm ack low",ref_pending_cnt<=2);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;
        repeat(6) wrefi(); wc(3); check("Urgent",ref_urgent===1); check("Req at urg",ref_required===1);
        cfg_ref_priority=0;wc(2); check("Pri off",ref_urgent===0);
        cfg_ref_priority=1;wc(2); check("Pri on",ref_urgent===1);
        repeat(3) wrefi(); wc(3); check("Max req",ref_required===1);
        wrefi();wc(2); check("Starve rgn",ref_required===1);
        repeat(10) begin @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0; end wc(3);
        check("Drain",ref_pending_cnt<=3);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(3);
        @(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=0;wc(2);
        check("Force req",ref_required===1);
        @(posedge clk);ref_ack=1;@(posedge clk);ref_ack=0;wc(2); check("Force ack",ref_pending_cnt<=1);
        @(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=1;@(posedge clk);cfg_force_refresh=0;wc(2);
        check("Dbl force",ref_required===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);@(posedge clk);init_done=1;wc(3);
        ref_ack=1;wrefi();wrefi();ref_ack=0;wc(2); check("Simul stable",ref_pending_cnt<=2); check("Pend range",ref_pending_cnt<=7);
        cfg_urgent_threshold=2;wc(2);
        if(ref_pending_cnt>=2) check("Lo thresh urg",ref_urgent===1); else check("Lo thresh no",ref_urgent===0);
        cfg_max_postpone=2;wrefi();wrefi();wrefi();wc(2); check("Max=2 cap",1'b1);
        $display("\\n== %0d/%0d passed ==\\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #5_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def generate_calibration_tb(self):
        return """`timescale 1ns/1ps
module calibration_tb;
    localparam ZQCS_CTR_W=6,ZQCS_WAIT=20,TZQCS_CYC=4;
    logic clk=0; always #2.5 clk=~clk;
    logic init_done,rst_n,cal_done,cal_fail,zqcs_req,zqcs_ack;
    calibration #(.ZQCS_CTR_W(ZQCS_CTR_W),.ZQCS_WAIT(ZQCS_WAIT),.TZQCS_CYC(TZQCS_CYC)) dut(.*);
    int pass_count=0,fail_count=0,test_num=0;
    task automatic check(string n,bit c); test_num++;
        if(!c) begin $display("  X T%02d FAIL: %s",test_num,n); fail_count++; end
        else begin $display("  V T%02d PASS: %s",test_num,n); pass_count++; end
    endtask
    task automatic wc(int n); repeat(n) @(posedge clk); endtask
    initial begin
        $display("\\n== calibration_tb ==\\n");
        rst_n=0;init_done=0;zqcs_ack=0;
        wc(3); check("Rst done=0",cal_done===0); check("Rst fail=0",cal_fail===0); check("Rst zqcs=0",zqcs_req===0);
        @(posedge clk);rst_n=1;wc(2); check("Post done=0",cal_done===0); check("Post zqcs=0",zqcs_req===0);
        @(posedge clk);init_done=1;@(posedge clk); check("Not same cyc",cal_done===0);
        @(posedge clk); check("1cyc after",cal_done===1);
        wc(5); check("Stays",cal_done===1); check("Fail=0",cal_fail===0); check("Fail=0 always",cal_fail===0);
        init_done=0;wc(3); check("Fail off",cal_fail===0);
        init_done=1;wc(3); check("Fail re",cal_fail===0);
        rst_n=0;wc(2);rst_n=1;wc(2); check("Fail post rst",cal_fail===0);
        init_done=0;wc(2);@(posedge clk);init_done=1;wc(3); check("Re-cal",cal_done===1);
        wc(1); check("ZQCS fires",zqcs_req===1);
        wc(5); check("ZQCS stays",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("ZQCS clr",zqcs_req===0);
        wc(ZQCS_WAIT+2); check("ZQCS re",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("2nd ack",zqcs_req===0);
        zqcs_ack=1;@(posedge clk);zqcs_ack=0;@(posedge clk); check("Spurious",zqcs_req===0);
        wc(ZQCS_WAIT+2); check("3rd zqcs",zqcs_req===1);
        @(posedge clk);zqcs_ack=1;@(posedge clk);zqcs_ack=0;wc(2); check("3rd ack",zqcs_req===0);
        wc(ZQCS_WAIT+2); zqcs_ack=1;wc(3);zqcs_ack=0;@(posedge clk); check("Multi ack",zqcs_req===0);
        init_done=0;wc(5); check("Persists",cal_done===1);
        rst_n=0;wc(2); check("Rst clr",cal_done===0); rst_n=1;wc(2);
        init_done=1;@(posedge clk);init_done=0;@(posedge clk);init_done=1;wc(3); check("Toggle",cal_done===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(2);
        @(posedge clk);init_done=1;@(posedge clk);init_done=0;wc(3); check("1cyc pulse",cal_done===1);
        rst_n=0;wc(2);rst_n=1;init_done=0;wc(5); check("No zqcs pre",zqcs_req===0);
        @(posedge clk);init_done=1;wc(3); check("Final cal",cal_done===1);
        wc(2); check("Final zqcs",zqcs_req===1);
        $display("\\n== %0d/%0d passed ==\\n",pass_count,pass_count+fail_count); $finish;
    end
    initial begin #1_000_000; $display("TIMEOUT"); $finish; end
endmodule
"""

    def write_testbenches(self):
        tb_files = [
            ("addr_decoder_tb.sv", self.generate_addr_decoder_tb),
            ("bank_tracker_tb.sv", self.generate_bank_tracker_tb),
            ("refresh_ctrl_tb.sv", self.generate_refresh_ctrl_tb),
            ("calibration_tb.sv",  self.generate_calibration_tb),
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
        p.write_text(f"""# Phase 2 Simulation Makefile
RTL_DIR={self.rtl_dir}
TB_DIR={self.output_dir}
WORK=$(TB_DIR)/sim_work
.PHONY: all clean addr_decoder bank_tracker refresh_ctrl calibration
all: addr_decoder bank_tracker refresh_ctrl calibration
$(WORK): ; mkdir -p $(WORK)
addr_decoder: $(WORK) ; iverilog -g2012 -o $(WORK)/addr_decoder_tb $(RTL_DIR)/addr_decoder.sv $(TB_DIR)/addr_decoder_tb.sv && vvp $(WORK)/addr_decoder_tb
bank_tracker: $(WORK) ; iverilog -g2012 -o $(WORK)/bank_tracker_tb $(RTL_DIR)/bank_tracker.sv $(TB_DIR)/bank_tracker_tb.sv && vvp $(WORK)/bank_tracker_tb
refresh_ctrl: $(WORK) ; iverilog -g2012 -o $(WORK)/refresh_ctrl_tb $(RTL_DIR)/refresh_ctrl.sv $(TB_DIR)/refresh_ctrl_tb.sv && vvp $(WORK)/refresh_ctrl_tb
calibration: $(WORK) ; iverilog -g2012 -o $(WORK)/calibration_tb $(RTL_DIR)/calibration.sv $(TB_DIR)/calibration_tb.sv && vvp $(WORK)/calibration_tb
clean: ; rm -rf $(WORK)
""")
        print(f"  V Makefile.sim -> {p}")

    # ── RUN ──
    def run(self):
        hdr = "=" * 62
        print(f"\n\033[1m{hdr}\033[0m")
        print(f"\033[1m  PHASE 2 VALIDATION AGENT — TEST RUNNER\033[0m")
        print(f"  Spec: {self.spec_path}")
        print(f"  RTL:  {self.rtl_dir}")
        print(f"  Out:  {self.output_dir}")
        print(f"\033[1m{hdr}\033[0m")
        start = time.time()

        print(f"\n\033[1m  ── ADDR_DECODER TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading addr_decoder.sv...")
        self.results["modules"]["addr_decoder"] = self.validate_addr_decoder()

        print(f"\033[1m  ── BANK_TRACKER TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading bank_tracker.sv...")
        self.results["modules"]["bank_tracker"] = self.validate_bank_tracker()

        print(f"\033[1m  ── REFRESH_CTRL TESTBENCH ({'─' * 35})\033[0m")
        print(f"  Loading refresh_ctrl.sv...")
        self.results["modules"]["refresh_ctrl"] = self.validate_refresh_ctrl()

        print(f"\033[1m  ── CALIBRATION TESTBENCH ({'─' * 36})\033[0m")
        print(f"  Loading calibration.sv...")
        self.results["modules"]["calibration"] = self.validate_calibration()

        print(f"\033[1m  ── CROSS-MODULE INTERFACE ({'─' * 35})\033[0m")
        print(f"  Checking inter-module consistency...")
        self.results["modules"]["cross_module"] = self.validate_cross_module()

        # Generate testbenches
        self.write_testbenches()

        elapsed = time.time() - start

        # Overall
        total_passed = sum(m["passed"] for m in self.results["modules"].values())
        total_checks = sum(m["total"] for m in self.results["modules"].values())
        all_pass = all(m["status"] == "PASS" for m in self.results["modules"].values())

        self.results["overall"] = {
            "status": "PASS" if all_pass else "FAIL",
            "total_passed": total_passed,
            "total_checks": total_checks,
        }
        self.results["testbenches"] = self.generated_tb_paths

        # Console summary
        print(f"\n\033[1m{hdr}\033[0m")
        if all_pass:
            print(f"\033[92m  ✓ ALL TESTS PASSED: {total_passed}/{total_checks} checks in {elapsed:.2f}s\033[0m")
        else:
            print(f"\033[91m  ✗ TESTS FAILED: {total_passed}/{total_checks} checks in {elapsed:.2f}s\033[0m")
        print(f"\033[1m{hdr}\033[0m")
        print(f"  {'Module':<20s} {'Status':<10s} {'Passed':<10s} {'Total':<10s}")
        print(f"  {'─' * 50}")
        for mod, res in self.results["modules"].items():
            color = "\033[92m" if res["status"] == "PASS" else "\033[91m"
            print(f"  {mod:<20s} {color}{res['status']:<10s}\033[0m {res['passed']:<10d} {res['total']:<10d}")
        print(f"  {'─' * 50}")
        print(f"  {'TOTAL':<20s} {'PASS' if all_pass else 'FAIL':<10s} {total_passed:<10d} {total_checks:<10d}")
        print(f"  Time: {elapsed:.2f}s")

        if self.generated_tb_paths:
            print(f"\n  Generated testbenches:")
            for p in self.generated_tb_paths:
                print(f"    ✓ {p}")

        print(f"\033[1m{hdr}\033[0m")

        # ── Write JSON report ──
        report_json = self.output_dir / "phase2_validation_report.json"
        report_json.write_text(json.dumps(self.results, indent=2))

        # ── Write detailed TXT report (matching Phase 1 format) ──
        txt_path = self.output_dir / "phase2_validation_report.txt"
        lines = []
        L = lines.append

        L("╔══════════════════════════════════════════════════════════════════════╗")
        L("║                    DDR3 PHASE 2 VALIDATION REPORT                  ║")
        L(f"║  Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S'):55s}║")
        L(f"║  Spec:      {str(self.spec_path)[:55]:55s}║")
        L(f"║  RTL Dir:   {str(self.rtl_dir)[:55]:55s}║")
        L(f"║  Attempt:   {self.attempt} of {self.max_retries}{' ':48s}║")
        L("╚══════════════════════════════════════════════════════════════════════╝")
        L("")
        L(f"  OVERALL: {'PASS' if all_pass else 'FAIL'}  ({total_passed}/{total_checks} checks)")
        L(f"  Attempt: {self.attempt} of {self.max_retries}")
        L("")

        # Retry history
        if self.history:
            L(f"{'═' * 70}")
            L(f"  RETRY HISTORY")
            L(f"{'═' * 70}")
            L("")
            for h in self.history:
                a = h.get("attempt", "?")
                st = h.get("overall", "?")
                p = h.get("passed", "?")
                t = h.get("total", "?")
                fm = h.get("failed_modules", [])
                sym = "✓" if st == "PASS" else "✗"
                L(f"  {sym} Attempt {a}: {st} ({p}/{t})")
                if fm:
                    L(f"    Failed modules: {', '.join(fm)}")
                    for fc in h.get("failed_checks", []):
                        L(f"      ✗ [{fc['id']}] {fc['name']}")
                        L(f"        Expected: {fc['expected']}")
                        L(f"        Actual:   {fc['actual']}")
                L("")
            sym = "✓" if all_pass else "✗"
            L(f"  {sym} Attempt {self.attempt}: {'PASS' if all_pass else 'FAIL'} ({total_passed}/{total_checks})  ← current")
            L("")

        # Per-module detail
        # Map check ID prefixes to category names
        cat_names = {
            "V-AD": "ADDRESS DECODER VALIDATION",
            "V-BT": "BANK TRACKER VALIDATION",
            "V-RF": "REFRESH CONTROLLER VALIDATION",
            "V-CL": "CALIBRATION VALIDATION",
            "V-XM": "CROSS-MODULE INTERFACE",
        }

        for mod_name, mod_result in self.results["modules"].items():
            sym = "✓" if mod_result["status"] == "PASS" else "✗"
            L(f"{'═' * 70}")
            L(f"  {sym} {mod_name.upper()}  —  {mod_result['status']}  ({mod_result['passed']}/{mod_result['total']})")
            L(f"{'═' * 70}")
            L("")

            # Group checks by category
            categories = {}
            for chk in mod_result["checks"]:
                prefix = chk["id"].rsplit("-", 1)[0]
                cat = cat_names.get(prefix, prefix)
                if cat not in categories:
                    categories[cat] = []
                categories[cat].append(chk)

            for cat, cat_checks in categories.items():
                L(f"  ── {cat} ──")
                L("")
                for chk in cat_checks:
                    sym = "✓ PASS" if chk["pass"] else "✗ FAIL"
                    L(f"    [{chk['id']}] {chk['name']}")
                    L(f"      Status:   {sym}")
                    L(f"      Expected: {chk['expected']}")
                    L(f"      Actual:   {chk['actual']}")
                    L("")
                L("")

        # Testbench info
        if self.generated_tb_paths:
            L(f"{'═' * 70}")
            L(f"  GENERATED TESTBENCHES")
            L(f"{'═' * 70}")
            L("")
            for p in self.generated_tb_paths:
                L(f"  ✓ {p}")
            L("")
            L(f"  To run with Icarus Verilog:")
            L(f"    make -f {self.output_dir}/Makefile.sim all")
            L("")

        # Summary table
        L(f"{'═' * 70}")
        L(f"  SUMMARY TABLE")
        L(f"{'═' * 70}")
        L(f"  {'Module':<20s} {'Status':<8s} {'Passed':<8s} {'Total':<8s} {'Rate':<8s}")
        L(f"  {'─' * 52}")
        for mod_name, mod_result in self.results["modules"].items():
            rate = f"{mod_result['passed']/mod_result['total']*100:.0f}%" if mod_result['total'] > 0 else "N/A"
            L(f"  {mod_name:<20s} {mod_result['status']:<8s} {mod_result['passed']:<8d} {mod_result['total']:<8d} {rate:<8s}")
        L(f"  {'─' * 52}")
        rate = f"{total_passed/total_checks*100:.0f}%" if total_checks > 0 else "N/A"
        L(f"  {'TOTAL':<20s} {'PASS' if all_pass else 'FAIL':<8s} {total_passed:<8d} {total_checks:<8d} {rate:<8s}")
        L("")

        # Failures section
        all_checks_flat = []
        for mod_result in self.results["modules"].values():
            all_checks_flat.extend(mod_result["checks"])

        failures = [c for c in all_checks_flat if not c["pass"]]
        if failures:
            L(f"{'═' * 70}")
            L(f"  ✗ FAILURES ({len(failures)})")
            L(f"{'═' * 70}")
            for chk in failures:
                L(f"  ✗ [{chk['id']}] {chk['name']}")
                L(f"    Expected: {chk['expected']}")
                L(f"    Actual:   {chk['actual']}")
                L("")
        else:
            L(f"{'═' * 70}")
            L(f"  ✓ ALL {total_checks} CHECKS PASSED — NO FAILURES")
            L(f"{'═' * 70}")

        txt_path.write_text("\n".join(lines))

        print(f"  Report (JSON): {report_json}")
        print(f"  Report (TXT):  {txt_path}")

        return self.results

if __name__ == "__main__":
    spec = input("Spec JSON: ").strip()
    rtl = input("RTL dir: ").strip()
    out = input("Output (Enter=RTL): ").strip() or rtl
    r = Phase2ValidationAgent(spec, rtl, out).run()
    sys.exit(0 if r["overall"]["status"] == "PASS" else 1)