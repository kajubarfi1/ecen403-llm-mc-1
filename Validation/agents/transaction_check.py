#!/usr/bin/env python3
"""
transaction_check.py — Transaction-level verification post-processor
=====================================================================

Runs after simulation to verify DDR3 protocol properties at the
transaction level, independent of cycle-exact checking.

For each queue entry driven as stimulus, verifies:
  1. An ACT command was eventually issued to the matching bank and row
  2. A CAS command (RD or WR) was issued after the ACT to same bank/row
  3. No other ACT to the same bank appeared between ACT and CAS
  4. The CAS operation type matched the request (RD vs WR)

These properties come from the DDR3 protocol, not the reference model —
so this check is independent of cycle-exact behavioral prediction.

Usage:
    python3 agents/transaction_check.py \
        --scope path_04_scheduler_bank_loop \
        --project-root ~/Capstone/ecen403-llm-mc-1
"""

import argparse
import json
import os
import re
import sys


# DDR command encoding (from RTL cmd_gen.sv)
DDR_NOP = 0b0111   # 7
DDR_ACT = 0b0011   # 3
DDR_RD  = 0b0101   # 5
DDR_WR  = 0b0100   # 4
DDR_PRE = 0b0010   # 2
DDR_REF = 0b0001   # 1

CMD_NAME = {
    DDR_NOP: "NOP", DDR_ACT: "ACT", DDR_RD: "RD",
    DDR_WR: "WR", DDR_PRE: "PRE", DDR_REF: "REF",
}


def unpack_output(val):
    """Unpack a 32-bit packed output into individual signals.
    Based on the packing: bit[9:6]=ddr_cmd, bit[24:10]=ddr_addr,
    bit[27:25]=ddr_bank, bit[1]=deq_grant, bit[0]=ref_ack
    """
    return {
        "ref_ack": (val >> 0) & 0x1,
        "deq_grant": (val >> 1) & 0x1,
        "deq_idx": (val >> 2) & 0xF,
        "ddr_cmd": (val >> 6) & 0xF,
        "ddr_addr": (val >> 10) & 0x7FFF,
        "ddr_bank": (val >> 25) & 0x7,
    }


def parse_mismatches(sim_log_path):
    """Extract vec_number -> actual_value from MISMATCH lines."""
    captured = {}
    pattern = r'MISMATCH\s+vec[= ]*(\d+)\s+expected=0x([0-9A-Fa-f]+)\s+actual=0x([0-9A-Fa-f]+)'
    with open(sim_log_path) as f:
        for line in f:
            m = re.search(pattern, line)
            if m:
                vec_num = int(m.group(1))
                captured[vec_num] = int(m.group(3), 16)
    return captured


def reconstruct_rtl_outputs(hex_path, mismatches):
    """Reconstruct the actual RTL output at each check vector.
    For passing checks, actual = expected. For failing, use MISMATCH value.
    """
    outputs = {}
    vec_num = 0
    with open(hex_path) as f:
        for line in f:
            parts = line.strip().split()
            if len(parts) != 4:
                continue
            vec_num += 1
            opcode = parts[0].lower()
            if opcode == "02":  # check
                expected = int(parts[3], 16)
                if vec_num in mismatches:
                    outputs[vec_num] = mismatches[vec_num]
                else:
                    outputs[vec_num] = expected
    return outputs


def extract_queue_entries(testplan_path):
    """Extract all queue entries driven as stimulus from the test plan.
    Returns list of (vec_num, bank, row, col, is_write) for each valid request.
    """
    with open(testplan_path) as f:
        ops = json.load(f)

    entries = []
    vec_num = 0
    current = {"q_valid_0": 0, "q_bank_0": 0, "q_row_0": 0,
               "q_col_0": 0, "q_we_0": 0}

    for op in ops:
        if op["op"] in ("reset", "drive", "check", "step"):
            vec_num += 1

        if op["op"] == "drive":
            signals = op.get("signals", {})
            for key in current:
                if key in signals:
                    current[key] = signals[key]
            if current["q_valid_0"] == 1:
                entries.append({
                    "vec_num": vec_num,
                    "bank": current["q_bank_0"],
                    "row": current["q_row_0"],
                    "col": current["q_col_0"],
                    "is_write": current["q_we_0"],
                    "comment": op.get("comment", "")[:50],
                })

    return entries


def extract_rtl_command_stream(outputs):
    """Extract the sequence of non-NOP DDR commands from reconstructed outputs."""
    stream = []
    for vec_num in sorted(outputs.keys()):
        unpacked = unpack_output(outputs[vec_num])
        if unpacked["ddr_cmd"] != DDR_NOP:
            stream.append({
                "vec_num": vec_num,
                "cmd": unpacked["ddr_cmd"],
                "cmd_name": CMD_NAME.get(unpacked["ddr_cmd"], "?"),
                "bank": unpacked["ddr_bank"],
                "addr": unpacked["ddr_addr"],
                "deq_grant": unpacked["deq_grant"],
                "ref_ack": unpacked["ref_ack"],
            })
    return stream


def verify_transaction_properties(entries, command_stream):
    """Check transaction-level properties for each queue entry.
    
    Properties:
    1. An ACT to matching bank/row appeared after the entry was driven
    2. A CAS (RD or WR) to same bank appeared after the ACT
    3. The CAS type matches the request (RD vs WR)
    4. No intervening ACT to same bank between our ACT and CAS
    """
    results = []

    for entry in entries:
        # Find the first ACT to matching bank/row after this entry was driven
        act_cmd = None
        for cmd in command_stream:
            if cmd["vec_num"] < entry["vec_num"]:
                continue
            if cmd["cmd"] == DDR_ACT and cmd["bank"] == entry["bank"] and cmd["addr"] == entry["row"]:
                act_cmd = cmd
                break

        if act_cmd is None:
            results.append({
                "entry": entry,
                "status": "FAIL",
                "reason": f"No ACT to bank={entry['bank']} row=0x{entry['row']:x} found",
            })
            continue

        # Find the first CAS to matching bank after the ACT
        cas_cmd = None
        for cmd in command_stream:
            if cmd["vec_num"] <= act_cmd["vec_num"]:
                continue
            if cmd["cmd"] in (DDR_RD, DDR_WR) and cmd["bank"] == entry["bank"]:
                cas_cmd = cmd
                break
            # If another ACT to same bank appears first, sequence is broken
            if cmd["cmd"] == DDR_ACT and cmd["bank"] == entry["bank"]:
                break

        if cas_cmd is None:
            results.append({
                "entry": entry,
                "status": "FAIL",
                "reason": f"ACT found at vec={act_cmd['vec_num']} but no subsequent CAS to bank {entry['bank']}",
            })
            continue

        # Verify CAS type matches request
        expected_cas = DDR_WR if entry["is_write"] else DDR_RD
        if cas_cmd["cmd"] != expected_cas:
            results.append({
                "entry": entry,
                "status": "FAIL",
                "reason": f"Expected {CMD_NAME[expected_cas]} but got {cas_cmd['cmd_name']}",
            })
            continue

        results.append({
            "entry": entry,
            "status": "PASS",
            "act_vec": act_cmd["vec_num"],
            "cas_vec": cas_cmd["vec_num"],
            "cas_type": cas_cmd["cmd_name"],
        })

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Transaction-level verification post-processor")
    parser.add_argument("--scope", required=True, help="Scope name")
    parser.add_argument("--project-root", required=True, help="Project root directory")
    args = parser.parse_args()

    scope = args.scope
    project_root = os.path.expanduser(args.project_root)
    validation_dir = os.path.join(project_root, "Validation")
    scope_dir = os.path.join(validation_dir, "scopes", scope)
    reports_dir = os.path.join(scope_dir, "reports")

    testplan_path = os.path.join(scope_dir, f"{scope}_testplan.json")
    hex_path = os.path.join(scope_dir, f"{scope}_vectors.hex")
    sim_log_path = os.path.join(reports_dir, f"{scope}_sim.log")

    print("=" * 60)
    print(f"  TRANSACTION-LEVEL VERIFICATION — {scope}")
    print("=" * 60)

    for path in [testplan_path, hex_path, sim_log_path]:
        if not os.path.isfile(path):
            print(f"  ERROR: Missing file: {path}")
            sys.exit(1)

    # Extract queue entries from test plan
    entries = extract_queue_entries(testplan_path)
    print(f"\n  Queue entries driven: {len(entries)}")

    # Reconstruct RTL outputs at each check point
    mismatches = parse_mismatches(sim_log_path)
    outputs = reconstruct_rtl_outputs(hex_path, mismatches)
    print(f"  Check points reconstructed: {len(outputs)}")
    print(f"  (Cycle-exact mismatches: {len(mismatches)})")

    # Extract the non-NOP command stream from RTL outputs
    command_stream = extract_rtl_command_stream(outputs)
    print(f"  Non-NOP RTL commands observed: {len(command_stream)}")

    # Count command types
    cmd_counts = {}
    for cmd in command_stream:
        name = cmd["cmd_name"]
        cmd_counts[name] = cmd_counts.get(name, 0) + 1
    print(f"  Command breakdown: {cmd_counts}")

    # Verify transaction properties
    print(f"\n  Verifying DDR3 protocol properties per queue entry...")
    results = verify_transaction_properties(entries, command_stream)

    passed = sum(1 for r in results if r["status"] == "PASS")
    failed = sum(1 for r in results if r["status"] == "FAIL")
    total = len(results)

    print(f"\n  " + "-" * 56)
    print(f"  Queue Entry Verification:")
    for r in results:
        entry = r["entry"]
        if r["status"] == "PASS":
            print(f"    [✓] vec={entry['vec_num']:3d} bank={entry['bank']} "
                  f"row=0x{entry['row']:04x} col=0x{entry['col']:03x} "
                  f"{'WR' if entry['is_write'] else 'RD'} "
                  f"→ ACT@{r['act_vec']} {r['cas_type']}@{r['cas_vec']}")
        else:
            print(f"    [✗] vec={entry['vec_num']:3d} bank={entry['bank']} "
                  f"row=0x{entry['row']:04x} — {r['reason']}")

    print(f"\n  " + "-" * 56)
    if total > 0:
        pct = 100.0 * passed / total
        print(f"  TRANSACTION-LEVEL RESULT: {passed}/{total} ({pct:.1f}%)")
    else:
        print(f"  No queue entries to verify.")

    # Save report
    report_path = os.path.join(reports_dir, f"{scope}_transaction_report.json")
    report = {
        "scope": scope,
        "total_entries": total,
        "passed": passed,
        "failed": failed,
        "pass_rate": passed / total if total > 0 else 0,
        "command_counts": cmd_counts,
        "results": [
            {
                "vec_num": r["entry"]["vec_num"],
                "bank": r["entry"]["bank"],
                "row": r["entry"]["row"],
                "is_write": r["entry"]["is_write"],
                "status": r["status"],
                "detail": r.get("reason", f"ACT@{r.get('act_vec','?')}→{r.get('cas_type','?')}@{r.get('cas_vec','?')}"),
            }
            for r in results
        ],
    }
    with open(report_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\n  Report: {report_path}")
    print("=" * 60)

    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()