"""
Agent 4 - Simulation Runner
=============================
SSH into TAMU olympus cluster, run Xcelium simulations via Slurm.

    Server:    olympus.ece.tamu.edu (Slurm head node)
    Simulator: Cadence Xcelium 24.03 (xrun)
    Path:      /opt/coe/cadence/XCELIUM240/tools/bin/xrun
    License:   5280@coe-vtls2.engr.tamu.edu

Usage (validation flow):
    python3 sim_runner.py --scope config_regs \
        --rtl ./path/to/config_regs.sv \
        --tb  ./path/to/config_regs_tb.sv \
        --vectors ./path/to/config_regs_vectors.hex
"""

import paramiko
import getpass
import time
import os
import re
import json
import argparse
from datetime import datetime


# CONFIGURATION
SSH_CONFIG = {
    "hostname": "olympus.ece.tamu.edu",
    "port": 22,
    "username": "jacobz",
    "key_path": None,
}

SLURM_CONFIG = {
    "partition": "adademic",          
    "qos": "olympus-academic",
    "cpus_per_task": 1,
    "job_name": "ecen-454-agent",
}

CADENCE_ENV = (
    "export DISPLAY='' && "
    "source /opt/coe/ncsu/ncsu-cdk-1.6.0.beta/ncsu.sh 2>/dev/null && "
    "export PATH=/opt/coe/cadence/XCELIUM240/tools/bin:"
    "/opt/coe/cadence/XCELIUM240/tools.lnx86/bin:$PATH"
)



class CadenceSSHAgent:

    def __init__(self, ssh_config=SSH_CONFIG, slurm_config=SLURM_CONFIG):
        self.ssh = ssh_config
        self.slurm = slurm_config
        self.client = paramiko.SSHClient()
        self.client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        self.connected = False
        self.work_dir = None

    # --- Connection ---

    def connect(self, password=None):
        kwargs = {
            "hostname": self.ssh["hostname"],
            "port": self.ssh["port"],
            "username": self.ssh["username"],
        }
        if self.ssh.get("key_path"):
            kwargs["key_filename"] = self.ssh["key_path"]
        else:
            # Check env var, then explicit password, then prompt
            pw = password or os.environ.get("OLYMPUS_PASSWORD")
            if pw:
                kwargs["password"] = pw

        self.client.connect(**kwargs)
        self.connected = True

        result = self._head_exec("echo $HOME")
        home = result["stdout"].strip() or f"/home/{self.ssh['username']}"
        self.work_dir = f"{home}/cadence_agent_work"
        self._head_exec(f"mkdir -p {self.work_dir}")

    def disconnect(self):
        if self.connected:
            self.client.close()
            self.connected = False

    # --- Command execution ---

    def _head_exec(self, cmd, timeout=30):
        stdin, stdout, stderr = self.client.exec_command(cmd, timeout=timeout)
        exit_code = stdout.channel.recv_exit_status()
        return {
            "stdout": stdout.read().decode("utf-8").strip(),
            "stderr": stderr.read().decode("utf-8").strip(),
            "exit_code": exit_code,
        }

    def srun(self, cmd, timeout=300):
        srun_cmd = (
            f'srun '
            f'--job-name={self.slurm["job_name"]} '
            f'--cpus-per-task={self.slurm["cpus_per_task"]} '
            f'--partition={self.slurm["partition"]} '
            f'--qos={self.slurm["qos"]} '
            f'bash -l -c "{CADENCE_ENV} && {cmd}"'
        )
        return self._head_exec(srun_cmd, timeout=timeout)

    def run_sim(self, command, timeout=300):
        """Run a simulation command on a compute node. Primary entry point."""
        return self.srun(f"cd {self.work_dir} && {command}", timeout=timeout)

    # --- Batch jobs (long simulations) ---

    def submit_batch(self, command, job_name="sim", time_min=30):
        script = f"""#!/bin/bash
#SBATCH --job-name={job_name}
#SBATCH --partition={self.slurm['partition']}
#SBATCH --qos={self.slurm['qos']}
#SBATCH --cpus-per-task={self.slurm['cpus_per_task']}
#SBATCH --time={time_min}
#SBATCH --output={self.work_dir}/{job_name}_%j.out
#SBATCH --error={self.work_dir}/{job_name}_%j.err

{CADENCE_ENV.replace(' && ', chr(10))}

cd {self.work_dir}
{command}
"""
        script_path = f"{self.work_dir}/{job_name}_job.sh"
        self._head_exec(f"cat > {script_path} << 'BATCHEOF'\n{script}\nBATCHEOF")
        result = self._head_exec(f"sbatch {script_path}")

        if "Submitted batch job" in result["stdout"]:
            return result["stdout"].split()[-1]
        return None

    def wait_for_job(self, job_id, poll_interval=5, max_wait=600):
        elapsed = 0
        while elapsed < max_wait:
            result = self._head_exec(f"squeue -j {job_id} -h -o '%T' 2>/dev/null")
            state = result["stdout"].strip()

            if not state:
                result = self._head_exec(
                    f"sacct -j {job_id} --format=State --noheader -P 2>/dev/null"
                )
                return result["stdout"].strip().split("\n")[0]

            if state in ("FAILED", "CANCELLED", "TIMEOUT"):
                return state

            time.sleep(poll_interval)
            elapsed += poll_interval

        return "TIMEOUT"

    def read_job_output(self, job_id, job_name="sim"):
        out = self._head_exec(f"cat {self.work_dir}/{job_name}_{job_id}.out 2>/dev/null")
        err = self._head_exec(f"cat {self.work_dir}/{job_name}_{job_id}.err 2>/dev/null")
        return {"stdout": out["stdout"], "stderr": err["stdout"]}

    # --- File operations ---

    def write_remote_file(self, filename, content):
        remote_path = f"{self.work_dir}/{filename}"
        self._head_exec(f"cat > {remote_path} << 'FILEEOF'\n{content}\nFILEEOF")
        return remote_path

    def read_remote_file(self, filename):
        result = self._head_exec(f"cat {self.work_dir}/{filename}")
        return result["stdout"]

    def upload_file(self, local_path, remote_filename=None):
        if remote_filename is None:
            remote_filename = os.path.basename(local_path)
        remote_path = f"{self.work_dir}/{remote_filename}"
        sftp = self.client.open_sftp()
        sftp.put(local_path, remote_path)
        sftp.close()
        return remote_path

    def upload_files(self, file_list):
        sftp = self.client.open_sftp()
        remote_paths = []
        for local_path in file_list:
            remote_path = f"{self.work_dir}/{os.path.basename(local_path)}"
            sftp.put(local_path, remote_path)
            remote_paths.append(remote_path)
        sftp.close()
        return remote_paths

    def download_file(self, remote_filename, local_path):
        sftp = self.client.open_sftp()
        sftp.get(f"{self.work_dir}/{remote_filename}", local_path)
        sftp.close()

    def list_work_dir(self):
        return self._head_exec(f"ls -la {self.work_dir}")["stdout"]

    def clean_work_dir(self):
        self._head_exec(
            f"rm -rf {self.work_dir}/INCA_libs {self.work_dir}/xcelium.d "
            f"{self.work_dir}/*.log {self.work_dir}/*.key "
            f"{self.work_dir}/*.out {self.work_dir}/*.err "
            f"{self.work_dir}/*_job.sh 2>/dev/null"
        )

    # --- Status (for Agent 1 / Planner) ---

    def get_status_report(self):
        return {
            "connected": self.connected,
            "server": self.ssh["hostname"],
            "simulator": "Cadence Xcelium 24.03 (xrun)",
            "work_dir": self.work_dir,
        }

    # =========================================================================
    # Validation flow: run_scope()
    # =========================================================================

    def run_scope(self, scope, rtl_files, tb_file, vector_file,
                  extra_args="", timeout=180):
        """
        Full validation flow for a scope:
          1. Clean work directory
          2. Upload RTL, testbench, and vector files
          3. Run xrun simulation
          4. Parse output for pass/fail
          5. Return structured report

        Args:
            scope:       Validation scope name (e.g. "config_regs")
            rtl_files:   List of RTL source file paths (can be 1 or many)
            tb_file:     Path to testbench .sv file
            vector_file: Path to .hex vector file
            extra_args:  Additional xrun arguments (optional)
            timeout:     Simulation timeout in seconds (default 180)

        Returns:
            dict with: scope, status, pass_count, fail_count, total_tests,
                       compile_errors, stdout, stderr, timestamp
        """
        report = {
            "scope": scope,
            "status": "unknown",
            "pass_count": 0,
            "fail_count": 0,
            "total_tests": 0,
            "compile_errors": [],
            "mismatches": [],
            "stdout": "",
            "stderr": "",
            "timestamp": datetime.now().isoformat(),
        }

        print(f"[SimRunner][{scope}] Starting validation flow...")

        # --- Step 1: Clean ---
        print(f"[SimRunner][{scope}] Cleaning work directory...")
        self.clean_work_dir()

        # --- Step 2: Upload ---
        all_files = []
        if isinstance(rtl_files, str):
            rtl_files = [rtl_files]
        all_files.extend(rtl_files)
        all_files.append(tb_file)
        all_files.append(vector_file)

        print(f"[SimRunner][{scope}] Uploading {len(all_files)} files...")
        for f in all_files:
            if not os.path.exists(f):
                report["status"] = "error"
                report["compile_errors"].append(f"File not found: {f}")
                print(f"[SimRunner][{scope}] ERROR: File not found: {f}")
                return report

        self.upload_files(all_files)

        # --- Step 3: Build xrun command ---
        rtl_names = " ".join(os.path.basename(f) for f in rtl_files)
        tb_name = os.path.basename(tb_file)
        vec_name = os.path.basename(vector_file)

        xrun_cmd = (
            f"xrun {rtl_names} {tb_name} "
            f"+VECTORS={vec_name} "
            f"-timescale 1ns/1ps -clean "
            f"{extra_args} 2>&1"
        )

        print(f"[SimRunner][{scope}] Running: {xrun_cmd}")

        # --- Step 4: Run simulation ---
        result = self.run_sim(xrun_cmd, timeout=timeout)
        report["stdout"] = result["stdout"]
        report["stderr"] = result["stderr"]

        print(f"[SimRunner][{scope}] Exit code: {result['exit_code']}")
        print(f"[SimRunner][{scope}] stdout length: {len(result['stdout'])} chars")
        print(f"[SimRunner][{scope}] stderr length: {len(result['stderr'])} chars")
        # Print last 500 chars of stdout for debugging
        if result['stdout']:
            print(f"[SimRunner][{scope}] stdout tail:\n{result['stdout'][-500:]}")
        else:
            print(f"[SimRunner][{scope}] WARNING: stdout is EMPTY")
        if result['stderr']:
            print(f"[SimRunner][{scope}] stderr:\n{result['stderr'][:500]}")

        # --- Step 5: Parse results ---
        stdout = result["stdout"]

        # Check for compile errors (xmvlog/xmelab only — NOT xmsim runtime errors)
        compile_errors = re.findall(r'(?:xmvlog|xmelab): \*E.*', stdout)
        report["compile_errors"] = compile_errors

        if compile_errors:
            report["status"] = "compile_error"
            print(f"[SimRunner][{scope}] COMPILE ERROR: {len(compile_errors)} errors")
            for err in compile_errors[:5]:
                print(f"  {err}")
            return report

        # Check for SVA assertion failures (runtime, not compile errors)
        sva_failures = re.findall(r'xmsim: \*E,ASRTST.*', stdout)
        report["sva_failures"] = len(sva_failures)

        # Parse pass/fail from testbench output
        # Format 1: "PASS: X/Y" or "FAIL: X/Y"
        pass_match = re.search(r'PASS:\s*(\d+)/(\d+)', stdout)
        fail_match = re.search(r'FAIL:\s*(\d+)/(\d+)', stdout)
        # Format 2: "PASS: N  FAIL: M" on one line (init_sequence style)
        summary_line = re.search(r'PASS:\s*(\d+)\s+FAIL:\s*(\d+)', stdout)
        # Format 3: "Passed: X" / "Pass: X" + "Failed: Y" / "Fail: Y" (with optional whitespace before colon)
        passed_line = re.search(r'(?:pass_count|Pass(?:ed)?|PASS(?:ED)?)\s*:\s*(\d+)', stdout)
        failed_line = re.search(r'(?:fail_count|Fail(?:ed)?|FAIL(?:ED)?)\s*:\s*(\d+)', stdout)
        # Format 4: "Total tests: X" or "Total vectors: X" (with optional whitespace before colon)
        total_line = re.search(r'Total\s+(?:tests|vectors)\s*:\s*(\d+)', stdout)
        # Format 5: Comma-separated: "Tests: 29, Passed: 27, Failed: 2"
        comma_summary = re.search(r'(?:Total\s+)?[Tt]ests\s*:\s*(\d+)\s*,\s*Pass(?:ed)?\s*:\s*(\d+)\s*,\s*Fail(?:ed)?\s*:\s*(\d+)', stdout)
        # Format 6: "All N tests passed" or "PASS: All N tests passed"
        all_pass = re.search(r'All\s+(\d+)\s+tests\s+passed', stdout)

        if re.search(r'RESULT:\s*FAIL', stdout):
            report["status"] = "fail"
        elif re.search(r'RESULT:\s*PASS', stdout) and report.get("status") == "unknown":
            report["status"] = "pass"

        if comma_summary:
            report["total_tests"] = int(comma_summary.group(1))
            report["pass_count"] = int(comma_summary.group(2))
            report["fail_count"] = int(comma_summary.group(3))
            report["status"] = "pass" if report["fail_count"] == 0 else "fail"
        elif summary_line:
            report["pass_count"] = int(summary_line.group(1))
            report["fail_count"] = int(summary_line.group(2))
            report["total_tests"] = report["pass_count"] + report["fail_count"]
            report["status"] = "pass" if report["fail_count"] == 0 else "fail"
        elif all_pass:
            report["total_tests"] = int(all_pass.group(1))
            report["pass_count"] = report["total_tests"]
            report["fail_count"] = 0
            report["status"] = "pass"
        elif pass_match:
            report["pass_count"] = int(pass_match.group(1))
            report["total_tests"] = int(pass_match.group(2))
            report["fail_count"] = 0
            report["status"] = "pass"
        elif fail_match:
            report["pass_count"] = int(fail_match.group(1))
            report["total_tests"] = int(fail_match.group(2))
            report["fail_count"] = report["total_tests"] - report["pass_count"]
            report["status"] = "fail"
        elif passed_line and failed_line:
            report["pass_count"] = int(passed_line.group(1))
            report["fail_count"] = int(failed_line.group(1))
            report["total_tests"] = report["pass_count"] + report["fail_count"]
            if total_line:
                report["total_tests"] = int(total_line.group(1))
            report["status"] = "pass" if report["fail_count"] == 0 else "fail"

        # Collect individual mismatches — handle both with and without addr field
        mismatches = re.findall(
            r'MISMATCH\s+vec[= ]*(\d+)\s+.*?expected=0x([0-9A-Fa-f]+)\s+actual=0x([0-9A-Fa-f]+)',
            stdout
        )
        report["mismatches"] = [
            {"vector": int(m[0]), "addr": "0", "expected": m[1], "actual": m[2]}
            for m in mismatches
        ]

        # If we found mismatches but no test counts were parsed, count from mismatches
        if mismatches and report["status"] == "unknown":
            report["status"] = "fail"
            report["fail_count"] = len(mismatches)
        # If test counts show 0/0 but we have mismatches, override
        if mismatches and report["total_tests"] == 0:
            report["fail_count"] = len(mismatches)
            report["status"] = "fail"

        # Check for watchdog / timeout
        if "Watchdog" in stdout or "WATCHDOG" in stdout:
            report["status"] = "timeout"

        # Check for simulation finishing at all
        if report["status"] == "unknown":
            if "$finish" in stdout or "Simulation complete" in stdout:
                report["status"] = "pass"  # No failures found
            else:
                report["status"] = "error"

        # --- Print summary ---
        print(f"\n{'='*60}")
        print(f"  Scope:   {scope}")
        print(f"  Status:  {report['status']}")
        print(f"  Tests:   {report['total_tests']}")
        print(f"  Passed:  {report['pass_count']}")
        print(f"  Failed:  {report['fail_count']}")
        if report["mismatches"]:
            print(f"  Mismatches ({len(report['mismatches'])}):")
            for m in report["mismatches"][:10]:
                print(f"    vec={m['vector']} addr=0x{m['addr']} "
                      f"exp=0x{m['expected']} got=0x{m['actual']}")
            if len(report["mismatches"]) > 10:
                print(f"    ... and {len(report['mismatches'])-10} more")
        if report["compile_errors"]:
            print(f"  Compile errors: {len(report['compile_errors'])}")
        if report.get("sva_failures", 0) > 0:
            print(f"  SVA assertions: {report['sva_failures']} failures")
        print(f"{'='*60}")

        return report


# =============================================================================
# CLI — supports both sanity test and scope-based validation
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Simulation Runner Agent")
    subparsers = parser.add_subparsers(dest="command")

    # --- Sanity test ---
    sanity_parser = subparsers.add_parser("sanity", help="Run sanity test")

    # --- Run a validation scope ---
    scope_parser = subparsers.add_parser("scope", help="Run validation scope")
    scope_parser.add_argument("--scope", required=True, help="Scope name (e.g. config_regs)")
    scope_parser.add_argument("--rtl", required=True, nargs="+", help="RTL source file(s)")
    scope_parser.add_argument("--tb", required=True, help="Testbench file")
    scope_parser.add_argument("--vectors", required=True, help="Vector hex file")
    scope_parser.add_argument("--extra-args", default="", help="Extra xrun arguments")
    scope_parser.add_argument("--timeout", type=int, default=180, help="Sim timeout (seconds)")
    scope_parser.add_argument("--report-dir", default=".", help="Directory to save report JSON")

    args = parser.parse_args()

    # Default to sanity if no command given
    if args.command is None:
        args.command = "sanity"

    password = os.environ.get("OLYMPUS_PASSWORD")
    if not password:
        password = getpass.getpass("Enter Olympus password: ")
    agent = CadenceSSHAgent()

    try:
        agent.connect(password=password)
        print(f"Connected. Work dir: {agent.work_dir}")

        if args.command == "sanity":
            # Verify xrun
            result = agent.srun("xrun -version 2>&1 | head -1")
            print(f"xrun: {result['stdout']}")

            # Sanity test
            agent.write_remote_file("sanity_test.sv", """module sanity_test(
    input logic clk, input logic rst_n, output logic [7:0] count);
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) count <= 8'h00; else count <= count + 1;
endmodule""")

            agent.write_remote_file("sanity_tb.sv", """module sanity_tb;
    logic clk = 0, rst_n = 0;
    logic [7:0] count;
    sanity_test dut(.clk(clk), .rst_n(rst_n), .count(count));
    always #5 clk = ~clk;
    initial begin
        #20 rst_n = 1; #200;
        if (count > 0) $display("SANITY_PASS: count = %0d", count);
        else $display("SANITY_FAIL: count = %0d", count);
        $finish;
    end
endmodule""")

            result = agent.run_sim(
                "xrun sanity_test.sv sanity_tb.sv -timescale 1ns/1ps -clean 2>&1"
            )
            passed = "SANITY_PASS" in result["stdout"]
            print(f"Sanity test: {'PASSED' if passed else 'FAILED'}")
            if not passed:
                print(result["stdout"])

            agent.clean_work_dir()

        elif args.command == "scope":
            report = agent.run_scope(
                scope=args.scope,
                rtl_files=args.rtl,
                tb_file=args.tb,
                vector_file=args.vectors,
                extra_args=args.extra_args,
                timeout=args.timeout,
            )

            # Save report
            os.makedirs(args.report_dir, exist_ok=True)
            report_path = os.path.join(
                args.report_dir, f"{args.scope}_sim_report.json"
            )
            with open(report_path, "w") as f:
                # Don't save full stdout/stderr to report file (too big)
                save_report = {k: v for k, v in report.items()
                              if k not in ("stdout", "stderr")}
                json.dump(save_report, f, indent=2)
            print(f"\nReport saved: {report_path}")

            # Save full log
            log_path = os.path.join(
                args.report_dir, f"{args.scope}_sim.log"
            )
            with open(log_path, "w") as f:
                f.write(report["stdout"])
                if report["stderr"]:
                    f.write("\n\n=== STDERR ===\n")
                    f.write(report["stderr"])
            print(f"Full log saved: {log_path}")

            agent.clean_work_dir()

    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
    finally:
        agent.disconnect()


if __name__ == "__main__":
    main()