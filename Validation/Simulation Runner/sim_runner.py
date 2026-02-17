"""
Agent 4 - Simulation Runner
=============================
SSH into TAMU olympus cluster, run Xcelium simulations via Slurm.

    Server:    olympus.ece.tamu.edu (Slurm head node)
    Simulator: Cadence Xcelium 24.03 (xrun)
    Path:      /opt/coe/cadence/XCELIUM240/tools/bin/xrun
    License:   5280@coe-vtls2.engr.tamu.edu

Prerequisites: pip3 install paramiko
"""

import paramiko
import getpass
import time
import os


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
        elif password:
            kwargs["password"] = password

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

    def srun(self, cmd, timeout=120):
        srun_cmd = (
            f'srun '
            f'--job-name={self.slurm["job_name"]} '
            f'--cpus-per-task={self.slurm["cpus_per_task"]} '
            f'--partition={self.slurm["partition"]} '
            f'--qos={self.slurm["qos"]} '
            f'bash -l -c "{CADENCE_ENV} && {cmd}"'
        )
        return self._head_exec(srun_cmd, timeout=timeout)

    def run_sim(self, command, timeout=120, logfile="xrun.log"):
        """Run a simulation command on a compute node. Primary entry point."""
        log_flag = f" -logfile {self.work_dir}/{logfile}" if logfile else ""
        return self.srun(f"cd {self.work_dir} && {command}{log_flag}", timeout=timeout)

    def read_sim_log(self, logfile="xrun.log"):
        """Read the simulation log from the work directory."""
        return self.read_remote_file(logfile)

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
            f"{self.work_dir}/*.key "
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


# MAIN
if __name__ == "__main__":
    password = getpass.getpass("Enter your password: ")
    agent = CadenceSSHAgent()

    try:
        agent.connect(password=password)
        print(f"Connected. Work dir: {agent.work_dir}")

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

        result = agent.run_sim("xrun sanity_test.sv sanity_tb.sv -timescale 1ns/1ps -clean 2>&1")
        passed = "SANITY_PASS" in result["stdout"]
        print(f"Sanity test: {'PASSED' if passed else 'FAILED'}")

        log = agent.read_sim_log()

        agent.clean_work_dir()

    except Exception as e:
        print(f"Error: {e}")
    finally:
        agent.disconnect()