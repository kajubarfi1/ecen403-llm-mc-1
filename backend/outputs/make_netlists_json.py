#!/usr/bin/env python3
"""Collect the per-block netlists and write outputs/NETLISTS.json.

Validation's final stage simulates each gate-level netlist in place of its block's
RTL, so what it needs from us is the netlist plus enough provenance to know whether
that netlist still describes the drop being judged.

Staleness is per block, not per drop (their handoff 2026-10-15, addendum 3): a drop
that changes only refresh_ctrl leaves every other netlist current. So each block
carries its own `design_id` - the RTL's identity with timestamps and provenance keys
removed - and the drop-level id is kept only for context.

The ids come from `Validation/structural/rtl_drop.py --block-design-ids`, run as a
subprocess rather than imported. The CLI is a contract; their module internals are
not, and importing it would tie this script to their config layout and stop it
running when the team checkout is not beside us.

RTL currency is checked against the preserved synthesis input under the ORFS design
directory (`designs/<platform>/<block>/src/<block>.sv`) - what the tools actually
read - rather than inferred from build dates or git history. Two provenance claims
made from git archaeology in this project turned out to be comparing the wrong refs.

usage:
  make_netlists_json.py [--repo <team checkout>] [--platform sky130hd] [--dry-run]
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

HERE = Path(__file__).resolve().parent
BACKEND = HERE.parent
PIPELINE_OUT = BACKEND / "agents" / "pipeline_out"

PORT_ORDER_NOTE = ("Synthesis flattens unpacked-array ports (logic [W-1:0] p [D]) into "
                   "[D*W-1:0] with element 0 at the MOST significant end.")


def find_repo(explicit: Optional[str]) -> Optional[Path]:
    """The team checkout, for the drop's RTL and Validation's id tool.

    The backend commonly sits beside the checkout rather than inside it, so look at
    siblings as well as ancestors, bounded so this never walks the whole drive.
    """
    marker = Path("Validation") / "structural" / "rtl_drop.py"
    if explicit:
        p = Path(explicit)
        return p if (p / marker).exists() else None
    for base in [BACKEND, *list(BACKEND.parents)[:3]]:
        cands: List[Path] = [base]
        try:
            cands.extend(c for c in base.iterdir() if c.is_dir())
        except OSError:
            pass
        for cand in cands:
            if (cand / marker).exists():
                return cand
    return None


def drop_ids(repo: Optional[Path]) -> Dict[str, Any]:
    """drop_id, design_id and the per-block design ids, from Validation's own tool."""
    if not repo:
        return {}
    tool = repo / "Validation" / "structural" / "rtl_drop.py"
    out: Dict[str, Any] = {}
    try:
        r = subprocess.run([sys.executable, str(tool), "--block-design-ids"],
                           capture_output=True, text=True, cwd=str(repo), timeout=120)
        if r.returncode == 0:
            out["block_design_ids"] = json.loads(r.stdout.strip())
        else:
            print(f"  ! --block-design-ids exited {r.returncode}")
    except Exception as e:
        print(f"  ! per-block ids unavailable ({type(e).__name__}: {e})")
    try:
        sys.path.insert(0, str(repo / "Validation" / "structural"))
        import rtl_drop                                           # noqa: PLC0415
        out["drop_id"], out["design_id"] = rtl_drop.drop_id(), rtl_drop.design_id()
    except Exception as e:
        print(f"  ! drop/design id unavailable ({type(e).__name__}: {e})")
    return out


def _body(p: Path) -> List[str]:
    """A file's lines without the generated-on comment, line endings normalised.

    The timestamp changes on every regeneration and reaches no gate, so two files
    differing only there describe the same design.
    """
    text = p.read_bytes().replace(b"\r\n", b"\n").decode("utf-8", "ignore")
    return [l for l in text.splitlines() if not l.startswith("// Generated:")]


def rtl_is_current(block: str, repo: Optional[Path], orfs: Optional[Path],
                   platform: str) -> Optional[bool]:
    """Did this netlist come from RTL identical to the drop's?

    None when either side is out of reach - unknown is not the same as current, and
    saying so is the point of the field.
    """
    if not (repo and orfs):
        return None
    built = orfs / "designs" / platform / block / "src" / f"{block}.sv"
    drop = next(iter(sorted((repo / "Frontend2" / "OutputFolders").glob(
        f"PHASE*RTL/{block}.sv"))), None)
    if not (built.exists() and drop and drop.exists()):
        return None
    return _body(built) == _body(drop)


def metrics_for(block: str) -> Dict[str, Any]:
    """What the last build of this block measured."""
    out: Dict[str, Any] = {}
    rep = PIPELINE_OUT / f"pipeline_final_report_{block}.json"
    if rep.exists():
        d = json.loads(rep.read_text(encoding="utf-8"))
        out.update({"sta": d.get("sta_status"), "drc_violations": d.get("drc_violations"),
                    "lvs": d.get("lvs_status")})
    rs = PIPELINE_OUT / "reporter" / block / "reporter_summary.json"
    if rs.exists():
        m = json.loads(rs.read_text(encoding="utf-8")).get("metrics", {})
        out.update({k: m.get(k) for k in ("fmax_mhz", "wns_ns", "cell_count", "area_um2")})
    return out


def resolve_orfs(explicit: Optional[str]) -> Optional[Path]:
    """The ORFS flow directory, which holds the preserved synthesis inputs."""
    val = explicit
    if not val:
        env = BACKEND / "agents" / ".env"
        if env.exists():
            for line in env.read_text(encoding="utf-8", errors="ignore").splitlines():
                if line.startswith("ORFS_DIR="):
                    val = line.split("=", 1)[1].strip().strip('"').strip("'")
                    break
    if not val:
        return None
    flow = Path(val) / "flow"
    return flow if flow.is_dir() else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=None, help="team checkout (default: look beside us)")
    ap.add_argument("--platform", default="sky130hd")
    ap.add_argument("--orfs", default=None, help="ORFS dir (default: ORFS_DIR from agents/.env)")
    ap.add_argument("--spec-revision", default="golden_ddr3_1600k_x8_2lane_1rank")
    ap.add_argument("--period", type=float, default=5.0)
    ap.add_argument("--dry-run", action="store_true",
                    help="report what would be written without copying or writing")
    a = ap.parse_args()

    repo = find_repo(a.repo)
    print(f"team checkout: {repo or '(not found - ids and currency omitted)'}")
    orfs = resolve_orfs(a.orfs)
    print(f"orfs flow    : {orfs or '(not found - currency omitted)'}")

    ids = drop_ids(repo)
    per_block = ids.get("block_design_ids") or {}

    runner = PIPELINE_OUT / "runner"
    if not runner.is_dir():
        print(f"no runner output at {runner}")
        return 1
    # Only the drop's own blocks: the runner directory also holds negative controls
    # and experiments, which are not part of what Validation judges.
    blocks = sorted(d.name for d in runner.iterdir()
                    if d.is_dir() and (d / "6_final.v").exists() and d.name in per_block)
    if not blocks:
        print("no per-block netlists matching the drop's blocks")
        return 1

    doc: Dict[str, Any] = {
        "$comment": "Per-block gate-level netlists for Validation's final stage "
                    "(run_path.py --netlist <block>=<path>). Staleness is per block: "
                    "compare each block's design_id, not the drop id.",
        "generated_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "drop_id": ids.get("drop_id"),
        "design_id": ids.get("design_id"),
        "spec_revision": a.spec_revision,
        "clock_period_ns": a.period,
        "mode": "build",
        "port_order_note": PORT_ORDER_NOTE,
        "blocks": {},
    }

    for b in blocks:
        net = runner / b / "6_final.v"
        if not a.dry_run:
            dest = HERE / b / "6_final.v"
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(net, dest)
        cur = rtl_is_current(b, repo, orfs, a.platform)
        doc["blocks"][b] = {
            "netlist": f"backend/outputs/{b}/6_final.v",
            "design_id": per_block.get(b),
            "built_utc": datetime.fromtimestamp(
                net.stat().st_mtime, timezone.utc).strftime("%Y-%m-%d"),
            "rtl_matches_drop": cur,
            **metrics_for(b),
        }
        flag = {True: "current", False: "STALE", None: "unknown"}[cur]
        fmax = doc["blocks"][b].get("fmax_mhz")
        print(f"  {b:14} {str(fmax):>8} MHz  design={per_block.get(b)}  rtl={flag}")

    if not a.dry_run:
        (HERE / "NETLISTS.json").write_bytes(
            (json.dumps(doc, indent=2) + "\n").encode("utf-8"))

    stale = [b for b, v in doc["blocks"].items() if v["rtl_matches_drop"] is False]
    unknown = [b for b, v in doc["blocks"].items() if v["rtl_matches_drop"] is None]
    print(f"\n{len(blocks)} blocks  drop={ids.get('drop_id')}  design={ids.get('design_id')}")
    if stale:
        print(f"STALE, rebuild: {', '.join(stale)}")
    if unknown:
        print(f"currency unknown: {', '.join(unknown)}")
    if a.dry_run:
        print("(dry run - nothing written)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
