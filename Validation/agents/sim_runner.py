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
import socket
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
    # NOT a typo — "adademic" is the real partition name on Olympus, however
    # it looks. Proven by working runs: sim logs show `srun: job 322215 has
    # been allocated resources` and real Xcelium output from n01-zeus /
    # n03-poseidon with this exact value.
    #
    # Frontend/Agents/cadence_ssh_agent.py has "academic" with a comment
    # claiming it fixes a typo. That copy is wrong; "corrections" here have
    # broken every srun (empty stdout, no allocation). Do not change this
    # without a successful srun to back it up.
    "partition": "adademic",
    "qos": "olympus-academic",
    "cpus_per_task": 1,
    "job_name": "ecen-454-agent",
}

# NOTE: the Cadence tree is mounted on COMPUTE nodes only, not the Slurm head
# node. Anything that needs xrun/imc must go through srun(); a bare
# _head_exec() will report the tools as missing when they are simply not
# visible from there.
#
# VMANAGER supplies imc, the coverage merge/report tool. It was previously
# absent from PATH, which made `which imc` fail and looked like a missing
# install — it is present at /opt/coe/cadence/VMANAGER/tools.lnx86/bin/imc.
VMANAGER_ROOT = "/opt/coe/cadence/VMANAGER"

CADENCE_ENV = (
    "export DISPLAY='' && "
    "source /opt/coe/ncsu/ncsu-cdk-1.6.0.beta/ncsu.sh 2>/dev/null && "
    "export PATH=/opt/coe/cadence/XCELIUM240/tools/bin:"
    "/opt/coe/cadence/XCELIUM240/tools.lnx86/bin:"
    f"{VMANAGER_ROOT}/tools.lnx86/bin:"
    f"{VMANAGER_ROOT}/bin:$PATH"
)



# =============================================================================
# Result parsing
# =============================================================================
# Pure function: no SSH, no filesystem, no simulator. Unit-testable by feeding
# it recorded xrun logs.
#
# THE CONTRACT: a run is reported "pass" only when ALL of the following hold:
#   1. the testbench emitted a summary this parser recognised,
#   2. that summary reports zero failures,
#   3. no assertion fired, no mismatch was printed, no watchdog tripped.
# Every other outcome is compile_error / timeout / fail / unknown / error.
# "unknown" is NEVER upgraded to "pass" — an unparseable run is a harness
# failure, not a passing design.



def _password_from_setup_env():
    """OLYMPUS_PASSWORD from Validation/setup.env when it is not exported.
    The file is written by hand as `KEY = "value"` (spaces, quotes), which a
    shell cannot `source`, so tolerate that form here rather than require an
    export nobody remembers to do."""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "setup.env")
    try:
        with open(path) as f:
            txt = f.read()
    except OSError:
        return None
    m = re.search(r'^\s*OLYMPUS_PASSWORD\s*=\s*"?([^"\n]*?)"?\s*$', txt, re.M)
    return m.group(1) if m and m.group(1) else None

class CadenceSSHAgent:

    def __init__(self, ssh_config=SSH_CONFIG, slurm_config=SLURM_CONFIG,
                 work_subdir=None):
        # work_subdir gives a run its OWN remote directory. Two runs sharing
        # cadence_agent_work clobber each other's worklib (xmelab DLPKFL,
        # "failed to flush library worklib") the moment they overlap.
        self.work_subdir = work_subdir
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
            pw = (password or os.environ.get("OLYMPUS_PASSWORD")
                  or _password_from_setup_env())
            if pw:
                kwargs["password"] = pw

        self.client.connect(**kwargs)
        self.connected = True

        result = self._head_exec("echo $HOME")
        home = result["stdout"].strip() or f"/home/{self.ssh['username']}"
        self.work_dir = f"{home}/cadence_agent_work"
        if self.work_subdir:
            self.work_dir += f"/{self.work_subdir}"
        self._head_exec(f"mkdir -p {self.work_dir}")

    def disconnect(self):
        if self.connected:
            self.client.close()
            self.connected = False

    # --- Command execution ---

    def _head_exec(self, cmd, timeout=120):
        """Run a command on the head node and return stdout/stderr/exit_code.

        Drains both streams BEFORE asking for the exit status: paramiko's
        channel window is finite (~2 MB), so a process that fills it while we
        block in recv_exit_status() stalls on write, never exits, and hangs us
        forever. xrun output on an elaborated design exceeds that routinely.

        Draining first has a consequence worth knowing: it makes `timeout`
        real. recv_exit_status() waits on an event and ignores the channel
        timeout, so the previous ordering let arbitrarily long commands finish
        regardless of what timeout said. read() honours it, so a command that
        outlives `timeout` now raises instead of silently succeeding. That is
        the correct behaviour, but it must not crash the caller — a timeout is
        returned as a normal result with timed_out=True and exit_code -1.
        Callers running slow commands should pass a larger timeout explicitly.
        """
        try:
            stdin, stdout, stderr = self.client.exec_command(cmd, timeout=timeout)
            out = stdout.read().decode("utf-8", errors="replace").strip()
            err = stderr.read().decode("utf-8", errors="replace").strip()
            exit_code = stdout.channel.recv_exit_status()
            return {
                "stdout": out,
                "stderr": err,
                "exit_code": exit_code,
                "timed_out": False,
            }
        except (socket.timeout, paramiko.buffered_pipe.PipeTimeout):
            return {
                "stdout": "",
                "stderr": (f"command exceeded the {timeout}s channel timeout "
                           f"and was abandoned: {cmd[:120]}"),
                "exit_code": -1,
                "timed_out": True,
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
        """Run a simulation command on a compute node. Primary entry point.

        The timeout is enforced remotely with `timeout(1)` so a hung xrun is
        killed on the cluster rather than hanging this process. The local
        paramiko timeout is set higher so the remote guard always fires first;
        a killed command comes back with exit_code 124.
        """
        guarded = f"cd {self.work_dir} && timeout {timeout}s {command}"
        return self.srun(guarded, timeout=timeout + 30)

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
        # All verdict logic lives in parse_sim_output() so it can be unit
        # tested against recorded logs without SSH or a simulator.
        report.update(parse_sim_output(result["stdout"], result.get("exit_code", 0)))

        if report["status"] == "compile_error":
            print(f"[SimRunner][{scope}] COMPILE ERROR: {len(report['compile_errors'])} errors")
            for err in report["compile_errors"][:5]:
                print(f"  {err}")
            return report

        if report["status"] == "unknown":
            print(f"[SimRunner][{scope}] WARNING: simulation ran but printed no "
                  f"summary this parser recognises. Reporting 'unknown', NOT 'pass'.")

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

    password = os.environ.get("OLYMPUS_PASSWORD") or _password_from_setup_env()
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