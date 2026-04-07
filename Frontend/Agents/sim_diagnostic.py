#!/usr/bin/env python3
"""
UberDDR3 Sim Gate Diagnostic
==============================
Run this standalone to figure out where the SSH -> Slurm -> xrun chain breaks.
Tests each step independently and prints exactly what's happening.
"""
import getpass
import sys
import os

try:
    import paramiko
except ImportError:
    print("ERROR: pip install paramiko")
    sys.exit(1)

HOST = "olympus.ece.tamu.edu"
PORT = 22

CADENCE_ENV = (
    "export DISPLAY='' && "
    "source /opt/coe/ncsu/ncsu-cdk-1.6.0.beta/ncsu.sh 2>/dev/null && "
    "export PATH=/opt/coe/cadence/XCELIUM240/tools/bin:"
    "/opt/coe/cadence/XCELIUM240/tools.lnx86/bin:$PATH"
)

SLURM_PARTITION = "academic"
SLURM_QOS = "olympus-academic"


def ssh_exec(client, cmd, timeout=60):
    """Execute command and return stdout, stderr, exit_code."""
    stdin, stdout, stderr = client.exec_command(cmd, timeout=timeout)
    exit_code = stdout.channel.recv_exit_status()
    out = stdout.read().decode("utf-8")
    err = stderr.read().decode("utf-8")
    return out, err, exit_code


def main():
    username = input(f"Username for {HOST}: ").strip()
    password = getpass.getpass(f"Password for {username}@{HOST}: ")

    client = paramiko.SSHClient()
    client.set_missing_host_key_policy(paramiko.AutoAddPolicy())

    # ============================================================
    # STEP 1: SSH connection
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 1: SSH connection to {HOST}")
    print(f"{'=' * 60}")
    try:
        client.connect(hostname=HOST, port=PORT, username=username, password=password)
        print(f"  OK: Connected")
    except Exception as e:
        print(f"  FAIL: {e}")
        sys.exit(1)

    # ============================================================
    # STEP 2: Basic command execution on head node
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 2: Head node command execution")
    print(f"{'=' * 60}")

    out, err, code = ssh_exec(client, "echo HELLO_FROM_HEAD && hostname && pwd")
    print(f"  stdout: {out.strip()}")
    print(f"  stderr: {err.strip()}")
    print(f"  exit:   {code}")
    if "HELLO_FROM_HEAD" in out:
        print(f"  OK: Head node commands work")
    else:
        print(f"  FAIL: Head node not responding properly")

    # Get home dir
    out, _, _ = ssh_exec(client, "echo $HOME")
    home = out.strip()
    work_dir = f"{home}/cadence_agent_diag"
    print(f"  Home: {home}")
    print(f"  Work: {work_dir}")
    ssh_exec(client, f"mkdir -p {work_dir}")

    # ============================================================
    # STEP 3: Slurm availability
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 3: Slurm availability")
    print(f"{'=' * 60}")

    out, err, code = ssh_exec(client, "which srun && srun --version")
    print(f"  stdout: {out.strip()}")
    print(f"  exit:   {code}")
    if code != 0:
        print(f"  FAIL: srun not available")
        print(f"  stderr: {err.strip()}")

    out, err, code = ssh_exec(client, "sinfo -p academic --noheader -o '%P %a %D %N' 2>&1 | head -5")
    print(f"  Partitions: {out.strip()}")

    # ============================================================
    # STEP 4: Simple srun test (no xrun)
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 4: Simple srun execution")
    print(f"{'=' * 60}")

    srun_cmd = (
        f"srun --job-name=diag --cpus-per-task=1 "
        f"--partition={SLURM_PARTITION} --qos={SLURM_QOS} "
        f'bash -l -c "echo HELLO_FROM_COMPUTE && hostname && pwd"'
    )
    print(f"  Command: {srun_cmd[:100]}...")
    out, err, code = ssh_exec(client, srun_cmd, timeout=120)
    print(f"  stdout: {out.strip()[:300]}")
    if err.strip():
        print(f"  stderr: {err.strip()[:300]}")
    print(f"  exit:   {code}")
    if "HELLO_FROM_COMPUTE" in out:
        print(f"  OK: srun works, compute node responds")
    else:
        print(f"  FAIL: srun not returning output")
        print(f"  This is likely the root cause.")
        print(f"")
        print(f"  Trying without --qos flag...")
        srun_cmd2 = (
            f"srun --job-name=diag --cpus-per-task=1 "
            f"--partition={SLURM_PARTITION} "
            f'bash -l -c "echo HELLO_NO_QOS && hostname"'
        )
        out2, err2, code2 = ssh_exec(client, srun_cmd2, timeout=120)
        print(f"  stdout: {out2.strip()[:300]}")
        if err2.strip():
            print(f"  stderr: {err2.strip()[:300]}")
        if "HELLO_NO_QOS" in out2:
            print(f"  OK: Works without --qos. The QOS setting is wrong.")
        else:
            print(f"  Trying with default partition...")
            srun_cmd3 = f'srun --job-name=diag bash -l -c "echo HELLO_DEFAULT && hostname"'
            out3, err3, code3 = ssh_exec(client, srun_cmd3, timeout=120)
            print(f"  stdout: {out3.strip()[:300]}")
            if err3.strip():
                print(f"  stderr: {err3.strip()[:300]}")

    # ============================================================
    # STEP 5: Cadence environment on compute node
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 5: Cadence environment on compute node")
    print(f"{'=' * 60}")

    srun_cmd = (
        f"srun --job-name=diag --cpus-per-task=1 "
        f"--partition={SLURM_PARTITION} --qos={SLURM_QOS} "
        f'bash -l -c "{CADENCE_ENV} && which xrun && xrun -version 2>&1 | head -3"'
    )
    out, err, code = ssh_exec(client, srun_cmd, timeout=120)
    print(f"  stdout: {out.strip()[:500]}")
    if err.strip():
        print(f"  stderr: {err.strip()[:300]}")
    print(f"  exit:   {code}")
    if "xrun" in out.lower():
        print(f"  OK: xrun is accessible")
    else:
        print(f"  FAIL: xrun not found on compute node")

    # ============================================================
    # STEP 6: File visibility between head and compute
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 6: File visibility (head -> compute)")
    print(f"{'=' * 60}")

    # Write a test file on head node
    ssh_exec(client, f"echo 'TEST_FILE_CONTENT' > {work_dir}/diag_test.txt")
    out, _, _ = ssh_exec(client, f"cat {work_dir}/diag_test.txt")
    print(f"  Head node read: {out.strip()}")

    # Read it from compute node via srun
    srun_cmd = (
        f"srun --job-name=diag --cpus-per-task=1 "
        f"--partition={SLURM_PARTITION} --qos={SLURM_QOS} "
        f'bash -l -c "cat {work_dir}/diag_test.txt"'
    )
    out, err, code = ssh_exec(client, srun_cmd, timeout=120)
    print(f"  Compute read: {out.strip()}")
    print(f"  exit: {code}")
    if "TEST_FILE_CONTENT" in out:
        print(f"  OK: Files are shared (NFS)")
    else:
        print(f"  FAIL: Compute node cannot see head node files")
        if err.strip():
            print(f"  stderr: {err.strip()[:300]}")

    # ============================================================
    # STEP 7: Write a tiny SV file and run xrun
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 7: Minimal xrun simulation")
    print(f"{'=' * 60}")

    # Write minimal SV files on head node
    ssh_exec(client, f"""cat > {work_dir}/tiny.sv << 'EOF'
module tiny(input logic clk, output logic q);
    always_ff @(posedge clk) q <= ~q;
endmodule
EOF""")

    ssh_exec(client, f"""cat > {work_dir}/tiny_tb.sv << 'EOF'
module tiny_tb;
    logic clk = 0, q;
    tiny dut(.clk(clk), .q(q));
    always #5 clk = ~clk;
    initial begin
        #100;
        if (q !== 1'bx) $display("[PASS] 1: tiny works q=%b", q);
        else $display("[FAIL] 1: tiny broken");
        $display("ALL 1 TESTS PASSED");
        $finish;
    end
endmodule
EOF""")

    # Verify files exist
    out, _, _ = ssh_exec(client, f"ls -la {work_dir}/tiny*.sv")
    print(f"  Files: {out.strip()}")

    # Run xrun via srun, cat the output back
    srun_cmd = (
        f"srun --job-name=diag --cpus-per-task=1 "
        f"--partition={SLURM_PARTITION} --qos={SLURM_QOS} "
        f'bash -l -c "'
        f"{CADENCE_ENV} && "
        f"cd {work_dir} && "
        f"xrun tiny.sv tiny_tb.sv -timescale 1ns/1ps -sysv -access +rw -Q -unbuffered "
        f"> {work_dir}/tiny_xrun.log 2>&1 ; "
        f"echo EXIT_CODE=$? ; "
        f"echo === LOG START === ; "
        f"cat {work_dir}/tiny_xrun.log ; "
        f'echo === LOG END ==="'
    )
    print(f"  Running xrun via srun...")
    out, err, code = ssh_exec(client, srun_cmd, timeout=180)
    print(f"  srun exit: {code}")
    print(f"  stdout length: {len(out)} chars")
    if err.strip():
        print(f"  stderr: {err.strip()[:500]}")

    if "LOG START" in out and "LOG END" in out:
        log_start = out.index("LOG START") + len("LOG START")
        log_end = out.index("LOG END")
        log_content = out[log_start:log_end].strip()
        print(f"  Log content ({len(log_content)} chars):")
        for line in log_content.split("\n"):
            print(f"    {line}")
        if "[PASS]" in log_content:
            print(f"\n  OK: xrun simulation works end-to-end!")
        elif log_content:
            print(f"\n  PARTIAL: Got output but no [PASS] -- check for errors above")
        else:
            print(f"\n  FAIL: Log file was empty on compute node")
    else:
        print(f"  FAIL: Markers not found in output")
        print(f"  Raw output:")
        for line in out.strip().split("\n")[:20]:
            print(f"    {line}")

    # ============================================================
    # STEP 8: Try without srun (head node directly)
    # ============================================================
    print(f"\n{'=' * 60}")
    print(f"STEP 8: xrun directly on head node (no Slurm)")
    print(f"{'=' * 60}")

    direct_cmd = (
        f'bash -l -c "{CADENCE_ENV} && '
        f"cd {work_dir} && "
        f"xrun tiny.sv tiny_tb.sv -timescale 1ns/1ps -sysv -Q -unbuffered "
        f'2>&1 | head -50"'
    )
    out, err, code = ssh_exec(client, direct_cmd, timeout=120)
    print(f"  exit: {code}")
    print(f"  stdout ({len(out)} chars):")
    for line in out.strip().split("\n")[:20]:
        print(f"    {line}")
    if "[PASS]" in out:
        print(f"\n  OK: xrun works on head node directly")
        print(f"  --> The problem is Slurm, not xrun")
    elif "xrun" in out.lower() or "xcelium" in out.lower():
        print(f"\n  PARTIAL: xrun ran but tests didn't pass")
    else:
        print(f"\n  FAIL: xrun didn't produce output on head node either")
        print(f"  --> The problem is the Cadence environment setup")

    # Cleanup
    ssh_exec(client, f"rm -rf {work_dir}")
    client.close()

    print(f"\n{'=' * 60}")
    print(f"DIAGNOSTIC COMPLETE")
    print(f"{'=' * 60}")
    print(f"If Step 8 works but Step 7 doesn't: problem is Slurm config")
    print(f"If Step 8 also fails: problem is Cadence env on this machine")
    print(f"If Step 4 fails: problem is Slurm partition/QOS names")


if __name__ == "__main__":
    main()
