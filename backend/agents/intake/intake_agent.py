
import json, os, re, shutil, subprocess, sys, time
from pathlib import Path
from dotenv import load_dotenv
from anthropic import Anthropic

# ---- Config ----
MODEL = os.getenv("MODEL", "claude-opus-4-6")
HANDOFF_DIR = Path(os.getenv("HANDOFF_DIR", "handoff")).resolve()
OUT_ROOT = Path(os.getenv("OUT_ROOT", "backend/workspace/build")).resolve()
TAG = os.getenv("TAG", time.strftime("%Y-%m-%d_%H%M%S"))

ALLOWED_RTL_EXT = {".sv", ".v"}
ALLOWED_SDC_EXT = {".sdc"}

def which(tool: str) -> bool:
    return shutil.which(tool) is not None

def run_cmd(cmd, cwd=None):
    p = subprocess.run(cmd, cwd=str(cwd) if cwd else None, capture_output=True, text=True)
    out = (p.stdout or "") + ("\n" + p.stderr if p.stderr else "")
    return p.returncode, out

def extract_json(text: str) -> dict:
    text = text.strip()
    text = re.sub(r"^```(?:json)?\s*", "", text)
    text = re.sub(r"\s*```$", "", text)
    return json.loads(text)

def load_meta(p: Path) -> dict:
    return json.loads(p.read_text())

def validate_meta(meta: dict):
    errs = []
    if not isinstance(meta.get("top"), str) or not meta["top"].strip():
        errs.append("meta.top missing or not a non-empty string")
    clk = meta.get("clock")
    if not isinstance(clk, dict):
        errs.append("meta.clock missing or not an object")
    else:
        if not isinstance(clk.get("port"), str) or not clk["port"].strip():
            errs.append("meta.clock.port missing or not a non-empty string")
        per = clk.get("period_ns")
        if not isinstance(per, (int, float)) or per <= 0:
            errs.append("meta.clock.period_ns missing or not a number > 0")
    return errs

def gather_files():
    rtl_dir = HANDOFF_DIR / "rtl"
    if not rtl_dir.exists():
        raise FileNotFoundError("Missing directory: handoff/rtl")

    rtl = [p for p in rtl_dir.rglob("*") if p.is_file() and p.suffix.lower() in ALLOWED_RTL_EXT]
    if not rtl:
        raise FileNotFoundError("No RTL files found in handoff/rtl (.sv/.v expected)")

    sdc_dir = HANDOFF_DIR / "constraints"
    sdc = []
    if sdc_dir.exists():
        sdc = [p for p in sdc_dir.rglob("*") if p.is_file() and p.suffix.lower() in ALLOWED_SDC_EXT]

    return sorted(rtl), sorted(sdc)

def write_min_sdc(out_dir: Path, meta: dict):
    sdc = out_dir / "constraints.sdc"
    sdc.write_text(
        f"# Auto-generated minimal SDC\n"
        f"create_clock -name clk -period {meta['clock']['period_ns']} [get_ports {meta['clock']['port']}]\n"
    )
    return sdc

def prepare_constraints(out_dir: Path, meta: dict, sdc_files):
    # Use meta.constraints.sdc if provided; else first sdc file; else generate minimal
    specified = None
    if isinstance(meta.get("constraints"), dict):
        specified = meta["constraints"].get("sdc")

    if isinstance(specified, str) and specified.strip():
        cand = Path(specified)
        if not cand.is_absolute():
            cand = (HANDOFF_DIR / cand).resolve()
        if cand.exists():
            out = out_dir / "constraints.sdc"
            out.write_text(cand.read_text())
            return out, False, [f"Using meta-specified SDC: {cand}"]
        else:
            return write_min_sdc(out_dir, meta), True, [f"WARNING: meta.constraints.sdc missing: {specified}"]

    if sdc_files:
        out = out_dir / "constraints.sdc"
        out.write_text(sdc_files[0].read_text())
        notes = [f"Using first SDC in handoff/constraints: {sdc_files[0].name}"]
        if len(sdc_files) > 1:
            notes.append("WARNING: Multiple SDC files found; using first.")
        return out, False, notes

    return write_min_sdc(out_dir, meta), True, ["No SDC found; generated minimal clock-only constraints.sdc"]

def lint_compile(top: str, rtl_files):
    # Try verilator, then iverilog, then yosys
    if which("verilator"):
        cmd = ["verilator", "--lint-only", "--sv", "-Wall", "--top-module", top] + [str(f) for f in rtl_files]
        rc, out = run_cmd(cmd)
        return rc == 0, "verilator", cmd, out

    if which("iverilog"):
        cmd = ["iverilog", "-g2012", "-s", top, "-o", "lint.out"] + [str(f) for f in rtl_files]
        rc, out = run_cmd(cmd)
        return rc == 0, "iverilog", cmd, out

    if which("yosys"):
        file_list = " ".join([f"\"{str(f)}\"" for f in rtl_files])
        script = f"read_verilog -sv {file_list}; hierarchy -top {top}; proc; opt; check"
        cmd = ["yosys", "-p", script]
        rc, out = run_cmd(cmd)
        return rc == 0, "yosys", cmd, out

    return False, "none", [], "No lint tool found (install verilator or iverilog or yosys)."

def claude_diagnose(meta: dict, findings: dict) -> dict:
    load_dotenv()
    api_key = os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        raise RuntimeError("ANTHROPIC_API_KEY not found in environment/.env")

    client = Anthropic(api_key=api_key)

    payload = {"meta": meta, "findings": findings}

    resp = client.messages.create(
        model=MODEL,
        max_tokens=900,
        system=(
            "You are a backend RTL intake validation agent. "
            "Return ONLY valid JSON (no markdown, no code fences) with schema:\n"
            "{"
            "\"overall_status\":\"PASS|FAIL\","
            "\"severity\":\"info|warning|error\","
            "\"likely_root_cause\":\"string\","
            "\"top_fixes\":[\"...\"],"
            "\"frontend_ticket\":{\"needed\":true/false,\"suggestions\":[\"...\"]},"
            "\"notes\":[\"...\"],"
            "\"report_md\":\"string\""
            "}"
        ),
        messages=[{"role": "user", "content": json.dumps(payload, indent=2)}],
    )
    return extract_json(resp.content[0].text)

def main():
    out_dir = OUT_ROOT / TAG
    out_dir.mkdir(parents=True, exist_ok=True)

    report = {
        "tag": TAG,
        "handoff_dir": str(HANDOFF_DIR),
        "out_dir": str(out_dir),
        "ok": False,
        "errors": [],
        "warnings": [],
        "tool": None
    }

    md = [f"# Intake Validation ({TAG})", ""]

    # meta
    meta_path = HANDOFF_DIR / "meta.json"
    if not meta_path.exists():
        report["errors"].append("Missing handoff/meta.json")
        write(out_dir, report, md, llm=None)
        return 2

    try:
        meta = load_meta(meta_path)
    except Exception as e:
        report["errors"].append(f"Failed to parse meta.json: {e}")
        write(out_dir, report, md, llm=None)
        return 2

    report["meta"] = meta
    md.append("✅ meta.json parsed")

    meta_errs = validate_meta(meta)
    if meta_errs:
        report["errors"].extend(meta_errs)
        md.append("❌ meta.json schema invalid")
        for e in meta_errs:
            md.append(f"- {e}")
        write(out_dir, report, md, llm=None)
        return 2
    md.append("✅ meta.json schema checks passed")

    # files
    try:
        rtl_files, sdc_files = gather_files()
    except Exception as e:
        report["errors"].append(str(e))
        write(out_dir, report, md, llm=None)
        return 2

    report["rtl_files"] = [str(p) for p in rtl_files]
    report["sdc_found"] = [str(p) for p in sdc_files]
    md.append(f"✅ Found {len(rtl_files)} RTL files")

    # constraints
    sdc_out, generated, notes = prepare_constraints(out_dir, meta, sdc_files)
    report["constraints_sdc"] = str(sdc_out)
    report["generated_sdc"] = generated
    for n in notes:
        (md.append(f"⚠️ {n}") if n.startswith("WARNING") or "generated" in n else md.append(f"✅ {n}"))

    # manifest + filelist
    (out_dir / "manifest.json").write_text(json.dumps({
        "top": meta["top"],
        "clock": meta["clock"],
        "reset": meta.get("reset"),
        "platform": meta.get("platform"),
        "rtl_files": [str(p) for p in rtl_files],
        "constraints_sdc": str(sdc_out),
    }, indent=2) + "\n")
    (out_dir / "srcs.f").write_text("\n".join(str(p) for p in rtl_files) + "\n")

    # lint (optional but recommended)
    ok, tool, cmd, tool_out = lint_compile(meta["top"], rtl_files)
    report["tool"] = {"name": tool, "ok": ok, "cmd": cmd}
    (out_dir / "tool_output.txt").write_text(tool_out)

    if tool == "none":
        report["warnings"].append("No lint tool found; skipping compile check.")
        md.append("⚠️ No lint tool found; skipping compile check.")
    elif ok:
        md.append(f"✅ Lint/compile PASS using {tool}")
    else:
        report["errors"].append(f"Lint/compile FAIL using {tool}")
        md.append(f"❌ Lint/compile FAIL using {tool}")

    findings = {
        "errors": report["errors"],
        "warnings": report["warnings"],
        "tool": {"name": tool, "ok": ok, "cmd": cmd, "output_tail": tool_out[-8000:]},
        "counts": {"rtl_files": len(rtl_files), "sdc_files": len(sdc_files)},
    }

    llm = None
    try:
        llm = claude_diagnose(meta, findings)
        (out_dir / "llm_diagnosis.json").write_text(json.dumps(llm, indent=2) + "\n")
        md.append("✅ Claude diagnosis generated")
    except Exception as e:
        report["warnings"].append(f"Claude diagnosis failed: {e}")
        md.append(f"⚠️ Claude diagnosis failed: {e}")

    report["ok"] = (len(report["errors"]) == 0)
    write(out_dir, report, md, llm=llm)
    return 0 if report["ok"] else 2

def write(out_dir: Path, report: dict, md_lines, llm=None):
    if llm:
        md_lines += ["", "## Claude Summary", f"- overall_status: {llm.get('overall_status')}",
                     f"- severity: {llm.get('severity')}",
                     f"- likely_root_cause: {llm.get('likely_root_cause')}"]
        fixes = llm.get("top_fixes") or []
        if fixes:
            md_lines += ["", "### Top fixes"] + [f"- {f}" for f in fixes]
        rep_md = llm.get("report_md")
        if isinstance(rep_md, str) and rep_md.strip():
            md_lines += ["", "## Report (from Claude)", rep_md.strip()]

    (out_dir / "validation_report.md").write_text("\n".join(md_lines) + "\n")
    (out_dir / "validation_report.json").write_text(json.dumps(report, indent=2) + "\n")

if __name__ == "__main__":
    sys.exit(main())

