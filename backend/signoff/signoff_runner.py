#!/usr/bin/env python3
"""
signoff_runner.py — DRC + LVS + pin audit for one ORFS design.

Runs INSIDE the ORFS container (called by pipeline.py validator_node) and writes
<out>/signoff_result.json. Standard library only.

  DRC   : KLayout + the platform DRC deck, directly on results/.../6_final.gds
          (same invocation as ORFS's Makefile 'drc' recipe, minus the GDS re-merge)
  LVS   : KLayout + signoff/lvs/<platform>_fixed.lylvs against a reference netlist
          built by signoff/lvs/prep_reference.py
  audit : covers the one thing KLayout's comparison skips — nets that touch only
          pins. Every schematic pin must exist in the layout, and both ends of every
          pin-to-pin assign must be one layout net.

Why each fix exists, and the negative controls proving these checks fail on broken
layouts: signoff/lvs/README.md.

It never reports PASS for something it could not check. A step that cannot run
yields status ERROR with the reason.

Self-test: --mutate swap|delete corrupts the reference netlist (flip-flop CLK<->D,
or one deleted cell). LVS must then FAIL.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path


class StepError(Exception):
    """A prerequisite failed; no check result can be trusted."""


def assert_gds_is_current(base: Path, gds: Path) -> dict:
    """Refuse to sign off a GDS older than the artifacts it will be compared to.

    ORFS writes the final artifacts in a fixed order, the merged GDS last:
    6_final.odb -> 6_final.def -> 6_final.v -> 6_final.gds. So in any complete
    run the GDS is the newest of the four. If one of the others is newer, the
    GDS merge did not run and this GDS belongs to an earlier flow.

    This is not hypothetical. On 2026-09-17 make died at 3_1_place under heavy
    parallel I/O; the flow still rewrote the netlist and DEF, but the merge never
    ran, and DRC and LVS certified week-old geometry for 10 of 11 blocks. The
    runner has its own provenance check now; this one is independent of it, so
    the layout cannot be signed off stale no matter what invoked the flow.
    """
    when = lambda p: time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(p.stat().st_mtime))
    gds_mtime = gds.stat().st_mtime
    newer = [f"{f.name} ({when(f)})" for f in (base / "6_final.odb", base / "6_final.def", base / "6_final.v")
             if f.exists() and f.stat().st_mtime > gds_mtime]
    if newer:
        raise StepError(
            f"refusing to sign off a stale layout: 6_final.gds ({when(gds)}) is older than "
            f"{', '.join(newer)}. The GDS merge did not run, so this layout is not the one "
            f"the current netlist describes. Re-run the flow before signing off."
        )
    return {"gds_written": when(gds), "newer_artifacts": []}


def run(cmd, log: Path, timeout: int, cwd: Path):
    t0 = time.time()
    try:
        p = subprocess.run([str(c) for c in cmd], cwd=cwd, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, timeout=timeout)
        out, rc = p.stdout, p.returncode
    except subprocess.TimeoutExpired as e:
        raw = e.stdout or b""
        out = (raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw) + f"\n[signoff] TIMEOUT after {timeout}s"
        rc = -9
    log.write_text(out, encoding="utf-8", errors="replace")
    return rc, out, round(time.time() - t0, 1)


def parse_kv(s: str) -> dict:
    return {k: (int(v) if v.isdigit() else v) for k, v in re.findall(r"(\w+)=(\[[^\]]*\]|\S+)", s)}


def count_blackboxed(deck: Path, ref: Path) -> int:
    m = re.search(r"%w\[([^\]]+)\]\.each\s*\{\s*\|\w+\|\s*blank_circuit", deck.read_text(errors="ignore"))
    if not m:
        return 0
    names = tuple("__" + n for n in m.group(1).split())
    return sum(1 for l in ref.read_text(errors="ignore").splitlines()
               if l.startswith("X") and l.split()[-1].lower().endswith(names))


def signoff(a, res: dict) -> None:
    d, p, flow, so, out = a.design, a.platform, a.flow, a.signoff, a.out
    base = flow / "results" / p / d / "base"
    gds, netv, cdl = base / "6_final.gds", base / "6_final.v", base / "6_final.cdl"
    deck = so / "lvs" / f"{p}_fixed.lylvs"
    drc_deck = flow / "platforms" / p / "drc" / f"{p}.lydrc"
    plat_cdl = flow / "platforms" / p / "cdl" / f"{p}.cdl"
    for f, what in ((gds, "final GDS"), (netv, "final netlist"), (deck, f"sign-off LVS deck for '{p}'"),
                    (drc_deck, "platform DRC deck"), (plat_cdl, "platform CDL")):
        if not f.exists():
            raise StepError(f"{what} not found: {f}")
    os.environ.setdefault("KLAYOUT_CMD", shutil.which("klayout") or "/usr/bin/klayout")
    kl = flow / "scripts" / "klayout.sh"
    res["gds"] = str(gds)

    # 0. Provenance: is this GDS the one the current netlist describes?
    res["freshness"] = assert_gds_is_current(base, gds)

    # 1. Reference CDL from the final netlist, through make, refusing any upstream rebuild
    cfg, target = f"designs/{p}/{d}/config.mk", str(cdl.relative_to(flow))
    rc, dry, _ = run(["make", "-n", f"DESIGN_CONFIG={cfg}", target], out / "cdl_dryrun.log", 300, flow)
    if rc != 0:
        raise StepError(f"make dry-run for the CDL failed (rc={rc}); see cdl_dryrun.log")
    rebuild = [l for l in dry.splitlines() if re.search(r"yosys|openroad|klayout", l) and "cdl.tcl" not in l]
    if rebuild:
        raise StepError(f"refusing to generate the CDL: make would re-run {len(rebuild)} upstream flow "
                        f"step(s), so the results look stale; see cdl_dryrun.log")
    rc, _, _ = run(["make", f"DESIGN_CONFIG={cfg}", target], out / "cdl.log", 900, flow)
    if rc != 0 or not cdl.exists():
        raise StepError(f"CDL generation failed (rc={rc}); see cdl.log")

    # 2. DRC
    lyrdb = out / "drc.lyrdb"
    rc, _, secs = run([kl, "-zz", "-rd", f"in_gds={gds}", "-rd", f"report_file={lyrdb}", "-r", drc_deck],
                      out / "drc.log", 3600, flow)
    try:
        cats = Counter((it.findtext("category") or "?").strip("'") for it in ET.parse(lyrdb).getroot().iter("item"))
        n = sum(cats.values())
        res["drc"] = {"status": "PASS" if n == 0 else "FAIL", "violations": n, "by_rule": dict(cats.most_common()),
                      "report": str(lyrdb), "deck": str(drc_deck), "seconds": secs}
    except Exception as e:
        res["drc"] = {"status": "ERROR", "detail": f"no readable DRC report (klayout rc={rc}): {e}", "seconds": secs}

    # 3. Reference netlist for LVS
    ref = out / "reference.cdl"
    rc, txt, _ = run([sys.executable, so / "lvs" / "prep_reference.py", cdl, netv, plat_cdl, ref], out / "prep.log", 300, flow)
    m = re.search(r"^PREP (.*)$", txt, re.M)
    if rc != 0 or not m:
        raise StepError(f"reference-netlist prep failed (rc={rc}); see prep.log")
    prep = parse_kv(m.group(1))
    if a.mutate:
        mut = out / f"reference_{a.mutate}.cdl"
        rc, txt, _ = run([sys.executable, so / "lvs" / "negative_controls.py", a.mutate, ref, plat_cdl, mut],
                         out / "mutate.log", 120, flow)
        if rc != 0 or "NOT APPLIED" in txt:
            raise StepError(f"self-test mutation '{a.mutate}' could not be applied; see mutate.log")
        res["mutation"] = txt.strip()
        ref = mut

    # 4. LVS
    lvsdb = out / "lvs.lvsdb"
    rc, log, secs = run([kl, "-b", "-rd", f"in_gds={gds}", "-rd", f"cdl_file={ref}", "-rd", f"report_file={lvsdb}",
                         "-rd", f"target_netlist={out / 'extracted.cir'}", "-r", deck], out / "lvs.log", 3600, flow)
    verdict = "match" if "Congratulations" in log else ("mismatch" if "don't match" in log else None)
    lvs = {"verdict": verdict, "report": str(lvsdb), "deck": str(deck), "seconds": secs, "prep": prep,
           "blackboxed_instances": count_blackboxed(deck, ref)}
    if verdict is None or not lvsdb.exists():
        lvs.update(status="ERROR", detail=f"LVS produced no verdict or database (klayout rc={rc}); see lvs.log")
        res["lvs"] = lvs
        return
    _, xt, _ = run(["klayout", "-b", "-rd", f"lvsdb={lvsdb}", "-rd", f"b={d}", "-r", so / "lvs" / "xref_summary.rb"],
                   out / "xref.log", 600, flow)
    top = re.search(r"XREF top (\S+) compared: devices=(\d+) nets=(\d+) pins=(\d+)", xt)
    cells = re.findall(r"XREF cell (\S+) (\S+)", xt)
    nets, pins = (int(top.group(3)), int(top.group(4))) if top else (0, 0)
    lvs.update(top_status=top.group(1) if top else None, nets_compared=nets, pins_compared=pins,
               cell_mismatches=[f"{c} ({s})" for c, s in cells])
    missing = prep.get("missing_defs", "[]")
    if missing not in ("[]", ""):
        lvs.update(status="ERROR", detail=f"design uses cells with no vendor CDL definition: {missing}")
    elif verdict == "match" and top and top.group(1) == "Match" and nets > 0 and not cells:
        lvs.update(status="PASS", detail=f"netlists match: {nets} nets / {pins} pins compared, "
                                         f"{lvs['blackboxed_instances']} black-boxed cell instance(s)")
    else:
        why = []
        if verdict != "match":
            why.append("KLayout reports the netlists do not match")
        if top is None:
            why.append("top circuit was not compared")
        elif top.group(1) != "Match":
            why.append(f"top circuit status {top.group(1)}")
        if cells:
            why.append("cells not matching: " + ", ".join(lvs["cell_mismatches"][:5]))
        lvs.update(status="FAIL", detail="; ".join(why))
    res["lvs"] = lvs

    # 5. Pin audit (LVS blind spot)
    _, at, _ = run(["klayout", "-b", "-rd", f"lvsdb={lvsdb}", "-rd", f"b={d}", "-rd", f"base={base}",
                    "-r", so / "lvs" / "audit_pins.rb"], out / "audit.log", 600, flow)
    m = re.search(r"AUDIT pins_in_layout=(\d+)/(\d+) pin_to_pin_feedthroughs=(\d+)/(\d+) "
                  r"control_wrong_pairs_accepted=(\d+)", at)
    if not m:
        res["audit"] = {"status": "ERROR", "detail": "pin audit produced no result; see audit.log"}
        return
    pp, pt, fo, ft, cw = map(int, m.groups())
    ok = pt > 0 and pp == pt and fo == ft and cw == 0
    res["audit"] = {"status": "PASS" if ok else "FAIL", "pins_present": pp, "pins_total": pt,
                    "feedthroughs_ok": fo, "feedthroughs_total": ft, "control_wrong_accepted": cw,
                    "detail": f"{pp}/{pt} pins in layout, {fo}/{ft} pin-to-pin feedthroughs on one net, "
                              f"{cw} wrong pairings accepted"}


def main() -> int:
    ap = argparse.ArgumentParser(description="DRC + LVS + pin audit for one ORFS design (run in the ORFS container)")
    ap.add_argument("--design", required=True)
    ap.add_argument("--platform", required=True)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--flow", default=Path("/OpenROAD-flow-scripts/flow"), type=Path)
    ap.add_argument("--signoff", default=Path(__file__).resolve().parent, type=Path)
    ap.add_argument("--mutate", choices=["swap", "delete"], help="self-test: corrupt the reference; LVS must FAIL")
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    res = {"design": a.design, "platform": a.platform, "ran": False, "error": None, "mutate": a.mutate,
           "drc": {"status": "ERROR"}, "lvs": {"status": "ERROR"}, "audit": {"status": "ERROR"}}
    try:
        signoff(a, res)
        res["ran"] = True
    except StepError as e:
        res["error"] = str(e)
    except Exception as e:                      # report, never crash silently
        res["error"] = f"unexpected {type(e).__name__}: {e}"
    (a.out / "signoff_result.json").write_text(json.dumps(res, indent=2))
    print("SIGNOFF " + " ".join(f"{k}={res[k]['status']}" for k in ("drc", "lvs", "audit"))
          + (f" error={res['error']}" if res["error"] else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
