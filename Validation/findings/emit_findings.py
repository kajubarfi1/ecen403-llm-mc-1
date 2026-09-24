#!/usr/bin/env python3
"""
emit_findings.py — turn a drop's path reports into findings v2, by code
=======================================================================
Until now a finding was something written by hand after reading a report.
This derives them: every failing stage, assertion hit and X-valued
observation in Validation/reports/paths becomes a structured record with

  owner_module      the block to patch — the stage's block for an exact
                    stage; the rule's declared owner (stage_invariant_rules
                    `rule_owners`, sva_rules `rule_owners`) for a checker
                    rule or an assertion
  check_id          stable across drops: taxonomy id + rule name
  requirement       from the stage rule, the SVA catalog or the vplan
  expected / actual lifted from the scoreboard's first mismatch line, in
                    the block's own port names
  anchor[]          assignment sites of the failing transaction's ports in
                    the owner's RTL (deterministic search, best first)
  repro             the run that showed it: command, sequence, work dir,
                    log, trace, first failure
  confidence        confirmed for model-free evidence (X, assertion),
                    observed for checker / predictor verdicts
  history           first_seen / introduced_in / resolved_in from the
                    snapshots under reports/drops/, so a regression reads
                    as one and a fix closes the record

One finding per (owner_module, check_id) across all paths; occurrences and
paths are accumulated. Output goes to
findings/outbox/<spec_revision>/<drop>/findings_v2.json, and
retry_adapter.py turns it into the Frontend's retry_instructions.json.

Usage:
    python3 Validation/findings/emit_findings.py
    python3 Validation/findings/emit_findings.py --reports Validation/reports/paths --out <dir>
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "structural"))
sys.path.insert(0, os.path.join(ROOT, "Validation", "faults"))

REPORTS = os.path.join(ROOT, "Validation", "reports", "paths")
DROPS = os.path.join(ROOT, "Validation", "reports", "drops")
OUTBOX = os.path.join(ROOT, "Validation", "findings", "outbox")
STAGE_RULES = os.path.join(ROOT, "Validation", "gates", "stage_invariant_rules.json")
SVA_RULES = os.path.join(ROOT, "Validation", "sva", "sva_rules.json")
SPEC = os.path.join(ROOT, "Validation", "spec", "llmmc_microarchitecturespec_filled.json")
SCHEMAS = os.path.join(ROOT, "Validation", "txn", "generated", "schemas.json")
VPLAN = os.path.join(ROOT, "Validation", "vplan", "vplan.json")

CHECK_RE = re.compile(r"^\s*([A-Z]+_\d{3})(?: \((\w+)\))?: (.*?)(?: @ \[(.*)\])?$")
RULE_RE = re.compile(r"^\s*([a-z_]\w*): (.*?)(?: @ \[(.*)\])?$")
MISMATCH_RE = re.compile(r"^\s*(\w+)\[(\d+)\] (value|missing|unexpected): (.*)$")
PRED_OBS_RE = re.compile(r"predicted \[(.*?)\] but observed \[(.*?)\]")
XVAL_RE = re.compile(r"^\s*x_value: (\w+)\.(\w+) seq=(\d+) carries X/Z on \[(.*?)\]")
ASSERT_RE = re.compile(r"Assertion \S*\.(\w+) has failed.*?(?:at time (\S+))?", re.S)
ASSERT_LINE_RE = re.compile(r"^(.*Assertion \S*\.(\w+) has failed.*)$", re.M)


def load(p, default=None):
    try:
        with open(p) as f:
            return json.load(f)
    except Exception:
        return default


# --------------------------------------------------------------------------
# rule knowledge: owners, requirements, spec refs
# --------------------------------------------------------------------------

class Rules:
    def __init__(self):
        sr = load(STAGE_RULES, {})
        sv = load(SVA_RULES, {})
        vp = load(VPLAN, {"items": []})
        self.stage_owner = {k: v for k, v in sr.get("rule_owners", {}).items()
                            if not k.startswith("$")}
        self.sva_owner = {k: v for k, v in sv.get("rule_owners", {}).items()
                          if not k.startswith("$")}
        self.req, self.spec_ref, self.severity = {}, {}, {}
        for st in sr.get("stages", {}).values():
            for r in st.get("rules", []):
                self.req.setdefault(r["id"], r["requirement"])
        for grp in [sv] + sv.get("command_groups", []):
            for key in ("min_separation_rules", "window_rules",
                        "state_rules", "max_interval_rules"):
                for r in grp.get(key, []):
                    self.req.setdefault(r["id"], r["requirement"])
                    if "param" in r:
                        self.spec_ref.setdefault(r["id"], f"timing_model.{r['param']}")
        spec = load(SPEC, {})
        for c in spec.get("failure_taxonomy", {}).get("categories", []):
            self.req.setdefault(c["id"], c.get("description", c.get("name", "")))
            self.severity[c["id"]] = c.get("severity", "major")
            self.spec_ref.setdefault(c["id"], f"failure_taxonomy.categories[{c['id']}]")
        for it in vp["items"]:
            fr = it.get("failure_ref")
            if fr:
                self.spec_ref.setdefault(fr, it.get("spec_ref"))

    def owners(self, check_id, default):
        tid = check_id.split("/")[0]
        for table in (self.stage_owner, self.sva_owner):
            if tid in table:
                return list(table[tid])
            fam = tid.split("_")[0] + "_*"
            if fam in table:
                return list(table[fam])
        return [default]


# --------------------------------------------------------------------------
# anchors: where the owner's RTL assigns the failing ports
# --------------------------------------------------------------------------

def anchors_for(owner, iface, kind, schemas, limit=4):
    """Assignment sites of the ports behind the failing transaction's fields
    in the owner's RTL, best first. Deterministic text search; the feedback
    agent (or a human) starts reading there. When the failing stream is not
    the owner's own (an assertion on cmd_gen's pins blamed on the scheduler),
    the owner's own output streams are anchored instead."""
    import rtl_drop as RD
    try:
        rtl = RD.rtl_file(owner)
    except Exception:
        return []
    ports = []
    if iface and schemas.get(iface, {}).get("block") == owner:
        fields = schemas[iface].get("kinds", {}).get(kind, {})
        ports = [f["port"] for f in fields.values()
                 if isinstance(f, dict) and "port" in f]
    if not ports:
        for name, sch in schemas.items():
            if sch.get("block") != owner:
                continue
            for kd in sch.get("kinds", {}).values():
                ports += [f["port"] for f in kd.values()
                          if isinstance(f, dict) and f.get("dir") == "output"]
        ports = sorted(set(ports))
    if not ports:
        return []
    with open(rtl, errors="replace") as f:
        lines = f.read().splitlines()
    hits = []
    for i, line in enumerate(lines, 1):
        s = line.strip()
        if s.startswith("//"):
            continue
        for p in ports:
            if re.search(rf"(?<![\w.]){re.escape(p)}\s*(<=|=)(?!=)", s) or \
               re.search(rf"^assign\s+{re.escape(p)}\b", s):
                hits.append({"file": os.path.relpath(rtl, ROOT), "line": i,
                             "signal": p, "text": s[:120]})
    # prefer non-reset assignments (those inside the `else` of a reset)
    hits.sort(key=lambda h: ("'0" in h["text"] or "1'b0" in h["text"], h["line"]))
    return hits[:limit]


# --------------------------------------------------------------------------
# evidence extraction from one path run
# --------------------------------------------------------------------------

def rejudge(stage):
    """Full scoreboard output for a failing stage (the report keeps only the
    last lines)."""
    if not stage.get("model") or not stage.get("trace"):
        return ""
    r = subprocess.run(["python3", "Validation/txn/scoreboard.py",
                        "--scope", stage["scope"], "--strategy",
                        "invariant" if stage["kind"] == "invariant" else "exact",
                        "--trace", stage["trace"], "--model", stage["model"]],
                       cwd=ROOT, capture_output=True, text=True)
    return (r.stdout or "") + (r.stderr or "")


def evidence_from_report(rep, rules, schemas, spec_regs=None):
    """Yield raw evidence records (one per violation line / assertion) with
    enough to build a finding."""
    spec_regs = spec_regs or {}
    path = rep["path"]
    trace = os.path.join(ROOT, rep["observed_trace"]) if rep.get("observed_trace") else None
    for st in rep.get("stages", []):
        if st["verdict"] != "fail":
            continue
        st = dict(st, trace=trace)
        block = st["stage"].split("+")[-1] if st["stage"] != "(path-level)" else None
        out = rejudge(st)
        lines = out.splitlines() if out else st.get("detail", [])
        for ln in lines:
            m = XVAL_RE.match(ln)
            if m:
                iface, kind, seq = m.group(1), m.group(2), int(m.group(3))
                yield {"check_id": "DATA_001", "owner": schemas.get(iface, {}).get("block", block),
                       "iface": iface, "kind": kind, "seq": seq, "detector": f"x_value:{iface}",
                       "expected": f"a defined value on {iface}.{kind} fields {m.group(4)}",
                       "actual": "X/Z driven on a monitored output", "path": path,
                       "confidence": "confirmed", "line": ln.strip()}
                continue
            m = CHECK_RE.match(ln)
            if m and not ln.strip().startswith("scope="):
                tid, rule, detail, txn = m.groups()
                iface, kind = _iface_kind(txn)
                owners = rules.owners(tid, block or "scheduler")
                yield {"check_id": tid, "owner": owners[0],
                       "owner_candidates": owners, "iface": iface, "kind": kind,
                       "detector": f"invariant:{st['stage']}:{rule or tid}",
                       "expected": rules.req.get(tid, ""), "actual": detail,
                       "path": path, "confidence": "observed", "line": ln.strip(),
                       "spec_ref": rules.spec_ref.get(tid)}
                continue
            m = MISMATCH_RE.match(ln)
            if m:
                iface, idx, kind_, rest = m.groups()
                po = PRED_OBS_RE.search(rest)
                exp, act = (po.group(1), po.group(2)) if po else ("", rest)
                kind = _iface_kind(exp or act)[1]
                yield {"check_id": f"MISMATCH/{iface}{_mismatch_discriminator(exp, act, spec_regs)}",
                       "owner": block,
                       "taxonomy_hint": _exact_taxonomy(block),
                       "iface": iface, "kind": kind,
                       "detector": f"exact:{st['stage']}:{kind_}",
                       "expected": exp or f"transaction predicted on {iface}",
                       "actual": act, "path": path, "confidence": "observed",
                       "line": ln.strip(), "seq": None}
                continue
            m = RULE_RE.match(ln)
            if m and m.group(1) not in ("scope", "status"):
                rule, detail, txn = m.groups()
                iface, kind = _iface_kind(txn)
                yield {"check_id": _exact_taxonomy(block), "owner": block or "scheduler",
                       "iface": iface, "kind": kind,
                       "detector": f"invariant:{st['stage']}:{rule}",
                       "expected": "", "actual": detail, "path": path,
                       "confidence": "observed", "line": ln.strip()}
    # independent assertions from the sim log
    lp = os.path.join(ROOT, rep["log"]) if rep.get("log") else None
    if lp and os.path.exists(lp):
        with open(lp, errors="replace") as f:
            log = f.read()
        counts, first = {}, {}
        for whole, name in ASSERT_LINE_RE.findall(log):
            counts[name] = counts.get(name, 0) + 1
            first.setdefault(name, whole.strip()[:200])
        for name, n in counts.items():
            if not name.startswith("a_"):
                continue            # the design's own assertions are corroboration, not ours
            tid = name[2:]
            owners = rules.owners(tid, "scheduler")
            yield {"check_id": tid, "owner": owners[0], "owner_candidates": owners,
                   "iface": "ddr_cmd", "kind": "command", "detector": f"assertion:{name}",
                   "expected": rules.req.get(tid, ""), "actual": f"fired {n}x; first: {first[name]}",
                   "path": path, "confidence": "confirmed", "count": n,
                   "line": first[name], "spec_ref": rules.spec_ref.get(tid)}


def _iface_kind(txn):
    if not txn:
        return None, None
    m = re.match(r"\s*(\w+)\.(\w+)", txn)
    return (m.group(1), m.group(2)) if m else (None, None)


def _fields(txn):
    return dict(re.findall(r"(\w+)=(0x[0-9a-fA-F]+|\d+|None)", txn or ""))


def _mismatch_discriminator(exp, act, spec_regs):
    """One finding per DISTINCT mismatch, not per stream: the fields that
    differ, and — when the stream carries an address that resolves to a
    register in the spec's register map — the register's name. A wrong
    reset value on TIMING_0 and lost reserved-bit masks on REFRESH_CONFIG
    are different defects even though both are csr_rsp.data mismatches."""
    fe, fa = _fields(exp), _fields(act)
    diff = sorted(k for k in set(fe) | set(fa) if fe.get(k) != fa.get(k))
    tag = ""
    addr = fe.get("addr") or fa.get("addr")
    if addr is not None:
        try:
            a = int(addr, 0)
            name = spec_regs.get(a)
            if name:
                tag = f"@{name}"
        except ValueError:
            pass
    return (f"[{','.join(diff)}]" if diff else "") + tag


def _register_names(spec):
    out = {}
    for r in spec.get("csr_register_map", {}).get("registers", []):
        try:
            off = r["offset"]
            out[int(off, 16) if isinstance(off, str) else int(off)] = r["name"]
        except (KeyError, ValueError, TypeError):
            continue
    return out


def _exact_taxonomy(block):
    return {"config_regs": "CSR_001", "data_path": "DATA_001", "wb_port": "DATA_001",
            "addr_decoder": "DATA_001", "cmd_gen": "PROTO_003"}.get(block, "DATA_001")


# --------------------------------------------------------------------------
# history from snapshots
# --------------------------------------------------------------------------

def snapshot_signatures():
    """{drop_head: set(detector keys)} for every snapshot, in time order."""
    from seed_faults import signature
    out = []
    for d in sorted(glob.glob(os.path.join(DROPS, "*"))):
        meta = load(os.path.join(d, "SNAPSHOT.json"), {})
        keys = set()
        for f in glob.glob(os.path.join(d, "*_report.json")):
            p = os.path.basename(f)[:-len("_report.json")]
            sig = signature(d, p) or {}
            keys |= {k for k in sig if k.startswith(("id:", "assert:", "stage:"))}
        out.append((meta.get("drop_head", os.path.basename(d)),
                    meta.get("taken_utc", ""), keys))
    out.sort(key=lambda x: x[1])
    return out



def previous_outbox(spec_rev, head):
    """(drop_head, findings_v2 doc) of the newest outbox drop before `head`
    for this spec revision, by generation time; None when there is none."""
    cands = []
    for f in glob.glob(os.path.join(OUTBOX, spec_rev, "*", "findings_v2.json")):
        d = load(f, {})
        h = d.get("drop") or os.path.basename(os.path.dirname(f))
        if h != head and d.get("generated_utc"):
            cands.append((d["generated_utc"], h, d))
    if not cands:
        return None
    cands.sort()
    _, h, d = cands[-1]
    return h, d

def history_for(check_id, detector, snaps, current_head):
    tid = check_id.split("/")[0]
    keys = {f"id:{tid}", f"id:{check_id.split('/')[-1]}"}
    parts = detector.split(":")
    if parts[0] == "assertion":
        keys.add(f"assert:{parts[1]}")
    elif len(parts) >= 3:
        keys.add(f"id:{parts[2]}")          # checker rule name
    if check_id.startswith("MISMATCH/"):
        keys.add("id:value")
    seen = [h for h, _, k in snaps if keys & k]
    first = seen[0] if seen else current_head
    introduced = None
    prev_absent = False
    for h, _, k in snaps:
        present = bool(keys & k)
        if present and prev_absent:
            introduced = h
        prev_absent = not present
    return first, introduced


# --------------------------------------------------------------------------

def emit(reports_dir, out_dir=None):
    rules = Rules()
    schemas = load(SCHEMAS, {"interfaces": {}})["interfaces"]
    spec = load(SPEC, {})
    reps = [load(f) for f in sorted(glob.glob(os.path.join(reports_dir, "*_report.json")))]
    reps = [r for r in reps if r]
    head = next((r.get("rtl_drop", {}).get("git_head") for r in reps
                 if r.get("rtl_drop", {}).get("git_head")), "unknown")
    snaps = snapshot_signatures()

    findings = {}
    spec_regs = _register_names(spec)
    for rep in reps:
        for ev in evidence_from_report(rep, rules, schemas, spec_regs):
            key = (ev["owner"], ev["check_id"])
            f = findings.get(key)
            if f is None:
                tid = (ev.get("taxonomy_hint") if ev["check_id"].startswith("MISMATCH/")
                       else ev["check_id"])
                first_seen, introduced = history_for(ev["check_id"], ev["detector"], snaps, head)
                f = {
                    "schema": "validation-findings/2",
                    "id": f"{ev['owner']}/{ev['check_id']}",
                    "kind": "rtl_defect",
                    "check_id": ev["check_id"], "taxonomy_id": tid,
                    "detectors": [],
                    "owner_module": ev["owner"],
                    "owner_candidates": ev.get("owner_candidates", [ev["owner"]]),
                    "severity": rules.severity.get(tid, "major"),
                    "confidence": ev["confidence"],
                    "title": f"{ev['owner']}: {ev['check_id']}",
                    "requirement": ev.get("expected") if ev["detector"].startswith(("invariant", "assertion")) else
                                   f"{ev['owner']} must produce the transactions the spec-derived model predicts",
                    "spec_ref": ev.get("spec_ref"),
                    "expected": ev["expected"], "actual": ev["actual"],
                    "detector": ev["detector"],
                    "anchor": anchors_for(ev["owner"], ev.get("iface"), ev.get("kind"), schemas),
                    "mechanism": None,
                    "paths": [], "occurrences": 0,
                    "repro": {
                        "path": rep["path"],
                        "command": f"python3 Validation/tools/run_path.py --path {rep['path']}",
                        "sequence": rep.get("sequence"),
                        "work_dir": f"Validation/sequences/generated/runs/{rep['path']}",
                        "log": rep.get("log"), "trace": rep.get("observed_trace"),
                        "first_failure": {"seq": ev.get("seq"), "line": ev["line"]},
                    },
                    "drop": {"git_head": head, "spec_revision": spec.get("revision"),
                             "rtl": rep.get("rtl_drop", {}).get("blocks", {})
                                    .get(ev["owner"], {}).get("rtl")},
                    "introduced_in": introduced, "first_seen": first_seen,
                    "last_seen": head, "resolved_in": None,
                    "status": "open",
                    "related_manual_findings": manual_related(ev["owner"], tid),
                }
                findings[key] = f
            f["occurrences"] += ev.get("count", 1)
            if rep["path"] not in f["paths"]:
                f["paths"].append(rep["path"])
            if ev["detector"] not in f["detectors"]:
                f["detectors"].append(ev["detector"])
            if f["confidence"] != "confirmed" and ev["confidence"] == "confirmed":
                f["confidence"] = "confirmed"       # the evidence list says why

    # resolved: a finding (owner/check id) that the previous drop's outbox
    # carried as open and this drop no longer raises. Keyed on the finding id,
    # not the taxonomy id — several findings share a taxonomy (every MISMATCH
    # is DATA_001), so a taxonomy key never goes absent while any survive.
    resolved = []
    prev = previous_outbox(spec.get("revision", "unknown"), head)
    if prev:
        prev_head, prev_doc = prev
        now_ids = {f["id"] for f in findings.values()}
        for pf in prev_doc.get("findings", []):
            if pf.get("status", "open") == "open" and pf["id"] not in now_ids:
                resolved.append({**{k: pf[k] for k in ("schema", "id", "kind", "check_id",
                                                        "taxonomy_id", "owner_module",
                                                        "severity", "title", "paths")
                                    if k in pf},
                                 "status": "resolved", "resolved_in": head,
                                 "last_seen": prev_head,
                                 "first_seen": pf.get("first_seen"),
                                 "note": f"open in drop {prev_head}, not raised by drop {head}"})

    order = {"critical": 0, "major": 1, "minor": 2}
    out = sorted(findings.values(),
                 key=lambda f: (order.get(f["severity"], 3), f["owner_module"], f["check_id"]))
    doc = {"schema": "validation-findings/2", "drop": head,
           "spec_revision": spec.get("revision"),
           "generated_utc": datetime.utcnow().isoformat() + "Z",
           "reports": os.path.relpath(reports_dir, ROOT),
           "finding_count": len(out), "findings": out, "resolved": resolved}
    out_dir = out_dir or os.path.join(OUTBOX, spec.get("revision", "unknown"), head)
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "findings_v2.json"), "w") as f:
        json.dump(doc, f, indent=2)
    latest = os.path.join(os.path.dirname(out_dir), "latest")
    with open(latest, "w") as f:
        f.write(os.path.basename(out_dir) + "\n")
    return doc, out_dir


def manual_related(owner, tid):
    out = []
    for f in glob.glob(os.path.join(OUTBOX, "*", "*_findings.json")):
        d = load(f, {})
        for x in d.get("findings", []):
            if x.get("scope") == owner or x.get("taxonomy_id") == tid:
                out.append(os.path.relpath(f, ROOT))
                break
    return sorted(set(out))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--reports", default=REPORTS)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    doc, out_dir = emit(args.reports, args.out)
    print(f"  drop {doc['drop']}: {doc['finding_count']} finding(s), "
          f"{len(doc['resolved'])} resolved since the previous drop")
    for f in doc["findings"]:
        print(f"  {f['severity']:8} {f['confidence']:9} {f['owner_module']:13} "
              f"{f['check_id']:22} x{f['occurrences']:<5} paths={len(f['paths']):<2} "
              f"detectors={len(f['detectors'])} anchors={len(f['anchor'])}"
              + (f"  introduced_in={f['introduced_in']}" if f["introduced_in"] else ""))
    print(f"  wrote {os.path.relpath(os.path.join(out_dir, 'findings_v2.json'), ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
