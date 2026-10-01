#!/usr/bin/env python3
"""
+======================================================================+
|        FRONTEND ORCHESTRATOR AGENT -- LLM-driven router              |
|                                                                      |
|  Sits between the Frontend agents and the Validation subsystem (see  |
|  the pipeline sketch). Reads what Validation/Backend dropped on disk |
|  (outbox JSON + .md notes) and decides, per finding, who acts on it: |
|                                                                      |
|    stage "spec" -> Microarch agent (English revision request; the    |
|                    deterministic compiler still decides validity)    |
|    stage "rtl"  -> Phase 1/2 validation (fix) agents, one dispatch   |
|                    per phase, via their --findings flag              |
|    anything else (Phase 3/4 modules, compiler-constant gaps, unclear |
|    ownership)   -> escalate: recorded in the report, never guessed   |
|                                                                      |
|  The LLM does the routing/triage; every action is a tool call into   |
|  existing code. Auto-dispatch is capped (--max-dispatches). Patch    |
|  approval stays human: the fix agents still require typing 'a'.      |
|                                                                      |
|  Usage:                                                              |
|    python3 Frontend2/scripts/Orchestrator/orchestrator_agent.py \\    |
|        --stage rtl --spec <spec.json> --output-dir <dir>             |
|        [--outbox Validation/findings/outbox] [--max-dispatches 3]    |
|    --stage spec : spec-gap findings -> Microarch agent               |
|                                                                      |
|  Needs ANTHROPIC_API_KEY (Frontend2/.env).                           |
+======================================================================+
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
REPO = SCRIPTS.parents[1]
for p in (HERE, SCRIPTS):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

import drop  # noqa: E402
import ingest  # noqa: E402


def _load_dotenv() -> None:
    for env_path in (SCRIPTS.parent / ".env", REPO / ".env"):
        if not env_path.is_file():
            continue
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, _, v = line.partition("=")
            k = k.strip()
            if k and k not in os.environ:
                os.environ[k] = v.strip().strip('"').strip("'")


_load_dotenv()

MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-5-5")
MAX_TURNS = 30
OUT_SUBDIR = "ORCHESTRATOR"
FIX_AGENT = {1: "Phase1/phase1_validation_agent.py", 2: "Phase2/phase2_validation_agent.py"}

SYSTEM_PROMPT = """You are the Frontend Orchestrator for an automated DDR3 controller \
RTL->GDSII flow. Validation (a separate subsystem) reports findings; you decide which \
Frontend agent should act on each one, then dispatch. You do not edit any file yourself.

Routing rules:
- Spec-stage finding (target "spec": a gap or contradiction in the microarchitecture \
spec) -> the Microarch agent owns every spec change; you never edit or write the spec. \
Two routes into it:
  * forward_spec_findings: for gaps in what the spec STATES (a field the compiler never \
emits, a taxonomy id, a width). The findings go to the Microarch agent verbatim; it \
proposes a compiler patch the human approves, then recompiles the spec. Do not \
paraphrase or pre-solve them, and do not escalate a gap just because it needs a \
compiler edit: that is what this route is for. The agent itself says when a finding \
needs an owner decision instead of guessing.
  * revise_spec: only when a finding is fixed by changing a configuration CHOICE. It \
sends English to the Microarch agent, whose deterministic compiler accepts/rejects the \
result. The agent resolves a request from scratch, so your request MUST restate the \
full desired configuration plus the specific change. Read the current spec with \
read_spec first and state EVERY Frontend-supported setting explicitly, none left to \
defaults: speed grade, density, device width, ranks (1 only), byte lanes, ECC, scheduler \
policy, row policy, queue/lookahead depth, address mapping, burst length, host data \
width, read/write buffer depths, interface type (wishbone_pipelined: the only one the \
generators build), self-refresh mode and target frequency. Copy each value from the \
current spec unless the finding requires changing it.
- RTL-stage finding owned by a Phase 1 or Phase 2 module -> dispatch_phase_fix, one \
call per phase, listing every implicated module of that phase. The fix agent patches \
the generator script (never emitted .sv) and a human approves each patch.
- Phase 3/4 modules have no fix agent yet -> escalate. Unclear owner, conflicting \
findings, or anything you'd have to guess at -> escalate with the reason.
- Check the `drop` block from list_findings first. Validation's result is about ONE \
drop (a content hash of the RTL). If validated_this_drop is false, its findings describe \
older RTL: do not dispatch fixes from them; call run_validation (the human confirms it) \
or escalate. Blocks generated from a different spec revision (spec_consistency.foreign) \
are never fixed by patching a generator: the whole drop must be regenerated from the \
spec it ships, so escalate that. `untested_in_this_drop` findings are still open but \
were not re-checked.
- Group findings that share a root cause; don't dispatch per finding.
- Read before routing: use list_findings, then read_finding / read_md for detail.
- Dispatch budget is limited. Finish with finish(); every finding must end up \
dispatched or escalated."""

TOOLS = [
    {"name": "list_findings", "description": "Summary of all ingested findings (id, target, module, phase, severity, title) plus available .md files.",
     "input_schema": {"type": "object", "properties": {}}},
    {"name": "read_finding", "description": "Full detail of findings for one module (or one spec scope), including expected/actual/anchors.",
     "input_schema": {"type": "object", "required": ["key"], "properties": {"key": {"type": "string", "description": "module name or spec scope"}}}},
    {"name": "read_md", "description": "Read one of the listed .md files.",
     "input_schema": {"type": "object", "required": ["path"], "properties": {"path": {"type": "string"}}}},
    {"name": "read_spec", "description": "Read a top-level section of the current spec JSON (or omit section for the list of section names).",
     "input_schema": {"type": "object", "properties": {"section": {"type": "string"}}}},
    {"name": "revise_spec", "description": "Send a complete plain-English configuration request (with the revision folded in) to the Microarch agent. Writes a NEW spec file; never overwrites the current one.",
     "input_schema": {"type": "object", "required": ["request", "addresses"], "properties": {
         "request": {"type": "string"}, "addresses": {"type": "array", "items": {"type": "string"}, "description": "finding ids this revision is meant to resolve"}}}},
    {"name": "forward_spec_findings", "description": "Hand spec-gap findings VERBATIM to the Microarch agent's spec-gap mode (proposes a compiler patch, human-approved, then recompiles the spec). Interactive. Counts against the dispatch budget.",
     "input_schema": {"type": "object", "required": ["finding_ids"], "properties": {
         "finding_ids": {"type": "array", "items": {"type": "string"}}}}},
    {"name": "dispatch_phase_fix", "description": "Run the Phase 1 or 2 fix agent on the given modules' findings. Interactive: a human approves each patch. Counts against the dispatch budget.",
     "input_schema": {"type": "object", "required": ["phase", "modules"], "properties": {
         "phase": {"type": "integer", "enum": [1, 2]}, "modules": {"type": "array", "items": {"type": "string"}}}}},
    {"name": "run_validation", "description": "Run Validation's validate_drop.py on the current drop (ships generated_spec.json first), then reload its findings. Slow (Olympus sims); the human confirms. Use when the findings are not about this drop.",
     "input_schema": {"type": "object", "properties": {"partial": {"type": "boolean", "description": "true if some blocks are absent"}}}},
    {"name": "escalate", "description": "Record findings that no agent can act on, with the reason, for a human.",
     "input_schema": {"type": "object", "required": ["finding_ids", "reason"], "properties": {
         "finding_ids": {"type": "array", "items": {"type": "string"}}, "reason": {"type": "string"}}}},
    {"name": "finish", "description": "End the session with a short summary.",
     "input_schema": {"type": "object", "required": ["summary"], "properties": {"summary": {"type": "string"}}}},
]


class Orchestrator:
    def __init__(self, stage, spec_path, output_dir, outbox, max_dispatches, allow_stale=False):
        self.stage = stage
        self.spec_path = Path(spec_path)
        self.out = Path(output_dir) / OUT_SUBDIR
        self.out.mkdir(parents=True, exist_ok=True)
        self.max_dispatches = max_dispatches
        self.outbox = Path(outbox)
        self.allow_stale = allow_stale
        self.validations = 0
        self.dispatches = 0
        self.log: list[dict] = []
        self.data = ingest.load_findings(Path(outbox))
        want = "spec" if stage == "spec" else "rtl"
        self.findings = [f for f in self.data["findings"] if f["target"] == want]
        self.spec = json.loads(self.spec_path.read_text())
        self.revisions = 0
        self._refresh_drop()

    def _refresh_drop(self):
        root = self.out.parent
        self.drop_id = drop.compute_drop_id(root)
        self.consistency = drop.spec_consistency(root)
        hf = drop.read_handoff(self.outbox, self.drop_id)
        self.validated = hf["matches"]
        self.handoff = hf.get("handoff")

    def _drop_summary(self):
        ds = self.data.get("drop_status") or {}
        return {"frontend_drop_id": self.drop_id,
                "validation_drop_id": (self.handoff or {}).get("drop_id"),
                "validated_this_drop": self.validated,
                "validation_status": (self.handoff or {}).get("status"),
                "failed_modules": (self.handoff or {}).get("failed_modules"),
                "spec_consistency": self.consistency,
                "blocks_absent": ds.get("blocks_absent"),
                "paths_blocked": len(ds.get("paths_blocked") or {}),
                "untested_in_this_drop": len(self.data.get("untested_in_this_drop") or []),
                "requires_human_review": self.data.get("requires_human_review")}

    # ---- tools -------------------------------------------------------
    def list_findings(self, **_):
        return {"drop": self._drop_summary(), "stage": self.stage, "count": len(self.findings),
                "findings": [{k: f[k] for k in ("id", "target", "module", "phase", "scope", "severity", "title")}
                             for f in self.findings],
                "md_files": self.data["md_files"],
                "dispatches_left": self.max_dispatches - self.dispatches}

    def read_finding(self, key, **_):
        hits = [f for f in self.findings if key in (f["module"], f["scope"], f["id"])]
        return hits[:25] or f"no findings for {key!r}"

    def read_md(self, path, **_):
        if path not in self.data["md_files"]:
            return "not an ingested .md file"
        return Path(path).read_text()[:20000]

    def read_spec(self, section=None, **_):
        if not section:
            return list(self.spec)
        return json.dumps(self.spec.get(section, f"no section {section!r}"))[:20000]

    def revise_spec(self, request, addresses, **_):
        if self.stage != "spec":
            return "revise_spec is only available in --stage spec"
        if self.dispatches >= self.max_dispatches:
            return "dispatch budget exhausted"
        self.dispatches += 1
        sys.path.insert(0, str(SCRIPTS / "Microarch"))
        import microarch_agent as ma
        import dummy_validation_agent as dva
        res = ma.run_english(request, interactive=False)
        entry = {"action": "revise_spec", "request": request, "addresses": addresses,
                 "status": res["status"]}
        if res["status"] != "ok":
            entry["detail"] = {k: res.get(k) for k in ("errors", "open_questions")}
            self.log.append(entry)
            return entry
        self.revisions = len(list(self.out.glob("spec_rev*.json"))) + 1
        out = self.out / f"spec_rev{self.revisions}.json"
        out.write_text(json.dumps(res["compile"]["spec"], indent=2))
        v = dva.validate_spec(res["compile"]["spec"], res["compile"])
        entry.update(spec_path=str(out), validation=v["status"], validation_findings=v["findings"],
                     assumptions=res["proposal"].get("assumptions", []))
        self.log.append(entry)
        return entry

    def forward_spec_findings(self, finding_ids, **_):
        if self.stage != "spec":
            return "forward_spec_findings is only available in --stage spec"
        if self.dispatches >= self.max_dispatches:
            return "dispatch budget exhausted"
        picked = [f["raw"] for f in self.findings if f["id"] in set(finding_ids)]
        if not picked:
            return "no ingested spec finding has those ids (use ids from list_findings)"
        self.dispatches += 1
        fpath = self.out / f"spec_findings_dispatch{self.dispatches}.json"
        fpath.write_text(json.dumps(picked, indent=2))
        print(f"\n  [orchestrator] forwarding {len(picked)} spec finding(s) to the Microarch agent\n")
        rc = subprocess.run([sys.executable, str(SCRIPTS / "Microarch" / "microarch_gap_agent.py"),
                             "--findings", str(fpath), "--spec", str(self.spec_path),
                             "--out-dir", str(self.out)], env=os.environ.copy()).returncode
        rp = self.out / "microarch_gap_report.json"
        rep = json.loads(rp.read_text()) if rp.is_file() else {}
        entry = {"action": "forward_spec_findings", "finding_ids": finding_ids, "exit_code": rc,
                 "status": rep.get("status"), "revised_spec": rep.get("revised_spec"),
                 "owner_decisions": rep.get("decisions", [])}
        self.log.append(entry)
        return entry

    def dispatch_phase_fix(self, phase, modules, **_):
        if phase not in FIX_AGENT:
            return f"no fix agent for phase {phase}; escalate instead"
        if self.dispatches >= self.max_dispatches:
            return "dispatch budget exhausted"
        if not self.validated and not self.allow_stale:
            return ("refused: Validation has not judged this drop (frontend_drop_id != "
                    "validation_drop_id), so these findings may describe older RTL. "
                    "run_validation first, or escalate.")
        mods = {m for m in modules if ingest.MODULE_PHASE.get(m) == phase}
        picked = {m: [c for c in self.data["raw_retry"].get(m, [])] for m in mods}
        picked = {m: c for m, c in picked.items() if c}
        if not picked:
            return f"no failed_checks on file for {sorted(mods)}"
        self.dispatches += 1
        fpath = self.out / f"phase{phase}_findings_dispatch{self.dispatches}.json"
        fpath.write_text(json.dumps({"retry_instructions": {m: {"failed_checks": c} for m, c in picked.items()}}, indent=2))
        print(f"\n  [orchestrator] dispatching Phase {phase} fix agent for {sorted(picked)}\n")
        rc = subprocess.run([sys.executable, str(SCRIPTS / FIX_AGENT[phase]),
                             "--output-dir", str(self.out.parent), "--spec", str(self.spec_path),
                             "--findings", str(fpath)], env=os.environ.copy()).returncode
        fix_report = self.out.parent / "VALIDATIONREPORT" / f"phase{phase}_fix_report.json"
        entry = {"action": "dispatch_phase_fix", "phase": phase, "modules": sorted(picked),
                 "exit_code": rc, "fix_report": str(fix_report) if fix_report.is_file() else None}
        self.log.append(entry)
        return {**entry, "note": "Unit sim re-verify only. Whether Validation's finding is closed is only known from its next drop."}

    def run_validation(self, partial=False, **_):
        if self.stage != "rtl":
            return "run_validation is only available in --stage rtl"
        if self.validations >= 2:
            return "validation-run budget exhausted"
        roots = [os.path.realpath(r if os.path.isabs(r) else str(REPO / r))
                 for r in json.loads((REPO / "Validation/spec/rtl_drop.json").read_text())["roots"]]
        if os.path.realpath(self.out.parent) not in roots:
            return (f"refused: Validation reads {roots}, not {self.out.parent}; run the "
                    f"pipeline with that as its output dir so Validation sees this drop.")
        if input("\n  Run Validation's validate_drop.py on this drop (Olympus sims, slow)? (y/N): "
                 ).strip().lower() != "y":
            return "declined by the human"
        self.validations += 1
        spec = drop.ship_spec(self.spec_path, self.out.parent)
        cmd = [sys.executable, str(REPO / "Validation/tools/validate_drop.py")] + (["--partial"] if partial else [])
        rc = subprocess.run(cmd, cwd=REPO, env={**os.environ, "VALIDATION_SPEC": str(spec)}).returncode
        self.data = ingest.load_findings(self.outbox)
        self.findings = [f for f in self.data["findings"]
                         if f["target"] == ("spec" if self.stage == "spec" else "rtl")]
        self._refresh_drop()
        entry = {"action": "run_validation", "exit_code": rc, "partial": partial}
        self.log.append(entry)
        return {**entry, "drop": self._drop_summary(), "findings": len(self.findings)}

    def escalate(self, finding_ids, reason, **_):
        self.log.append({"action": "escalate", "finding_ids": finding_ids, "reason": reason})
        return "recorded"

    # ---- loop --------------------------------------------------------
    def run(self) -> int:
        try:
            import anthropic
        except ImportError:
            raise SystemExit("pip install anthropic")
        if not os.environ.get("ANTHROPIC_API_KEY"):
            raise SystemExit("ANTHROPIC_API_KEY not set")
        if not self.findings:
            print(f"No {self.stage}-stage findings found in the outbox -- nothing to route.")
            return 0
        client = anthropic.Anthropic()
        messages = [{"role": "user", "content":
                     f"Stage: {self.stage}. {len(self.findings)} finding(s) from Validation drop "
                     f"{self.data['drop']} (validated_this_drop={self.validated}). Dispatch budget: {self.max_dispatches}. Route them."}]
        summary = "(no summary: turn limit reached)"
        done = False
        for _ in range(MAX_TURNS):
            resp = client.messages.create(model=MODEL, max_tokens=4096, system=SYSTEM_PROMPT,
                                          tools=TOOLS, messages=messages)
            messages.append({"role": "assistant", "content": resp.content})
            calls = [b for b in resp.content if b.type == "tool_use"]
            for b in resp.content:
                if b.type == "text" and b.text.strip():
                    print(f"  [orchestrator] {b.text.strip()}")
            if not calls:
                break
            results = []
            for c in calls:
                if c.name == "finish":
                    summary, done = c.input.get("summary", ""), True
                    out = "ok"
                else:
                    try:
                        out = getattr(self, c.name)(**c.input)
                    except Exception as e:  # surface to the model, don't crash the loop
                        out = f"ERROR: {e}"
                results.append({"type": "tool_result", "tool_use_id": c.id,
                                "content": out if isinstance(out, str) else json.dumps(out, default=str)})
            messages.append({"role": "user", "content": results})
            if done:
                break

        report = {"generated_utc": datetime.now(timezone.utc).isoformat(), "stage": self.stage,
                  "drop": self._drop_summary(), "model": MODEL, "dispatches": self.dispatches,
                  "summary": summary, "actions": self.log}
        rp = self.out / f"orchestrator_{self.stage}_report.json"
        rp.write_text(json.dumps(report, indent=2))
        print(f"\n  summary: {summary}\n  wrote {rp}")
        return 0 if done else 1


def main() -> int:
    ap = argparse.ArgumentParser(description="Frontend Orchestrator agent")
    ap.add_argument("--stage", choices=("spec", "rtl"), required=True)
    ap.add_argument("--spec", required=True, help="current spec JSON")
    ap.add_argument("--output-dir", required=True, help="pipeline output dir")
    ap.add_argument("--outbox", default=str(REPO / "Validation" / "findings" / "outbox"))
    ap.add_argument("--max-dispatches", type=int, default=3)
    ap.add_argument("--allow-stale", action="store_true",
                    help="dispatch fixes even when Validation's drop_id != this drop's")
    a = ap.parse_args()
    return Orchestrator(a.stage, a.spec, a.output_dir, a.outbox, a.max_dispatches, a.allow_stale).run()


if __name__ == "__main__":
    sys.exit(main())
