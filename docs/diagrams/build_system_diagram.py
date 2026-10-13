"""Generates system_diagram.html (the integrated system diagram) next to this file."""
import html, os
OUT = os.path.join(os.path.dirname(__file__), "system_diagram.html")
E = html.escape

def screen(x, y, w, h, title, lines):
    """Terminal window; lines = [(text, cls)]"""
    s = [f'<g transform="translate({x},{y})">',
         f'<rect width="{w}" height="{h}" rx="8" class="term"/>',
         f'<rect width="{w}" height="24" rx="8" class="termbar"/>',
         f'<rect y="16" width="{w}" height="8" class="termbar"/>',
         '<circle cx="14" cy="12" r="4" fill="#ff5f57"/><circle cx="28" cy="12" r="4" fill="#febc2e"/><circle cx="42" cy="12" r="4" fill="#28c840"/>',
         f'<text x="{w/2}" y="16" text-anchor="middle" class="termtitle">{E(title)}</text>']
    ty = 44
    for text, cls in lines:
        if text:
            s.append(f'<text x="12" y="{ty}" class="t {cls}" xml:space="preserve">{E(text)}</text>')
        ty += 16.5
    s.append('</g>')
    return "\n".join(s)

def doc(x, y, w, h, title, lines):
    """A rendered-document panel (the setup guide); lines = [(text, cls)]"""
    s = [f'<g transform="translate({x},{y})">',
         f'<rect width="{w}" height="{h}" rx="8" class="doc"/>',
         f'<rect width="{w}" height="24" rx="8" class="docbar"/>',
         f'<rect y="16" width="{w}" height="8" class="docbar"/>',
         f'<text x="12" y="16" class="doctitle">{E(title)}</text>']
    ty = 46
    for text, cls in lines:
        if text:
            s.append(f'<text x="14" y="{ty}" class="d {cls}" xml:space="preserve">{E(text)}</text>')
        ty += 16.5
    s.append('</g>')
    return "\n".join(s)

def step(x, y, n, label):
    return (f'<circle cx="{x+11}" cy="{y-5}" r="11" class="stepdot"/>'
            f'<text x="{x+11}" y="{y-1}" text-anchor="middle" class="stepn">{n}</text>'
            f'<text x="{x+30}" y="{y}" class="steplabel">{E(label)}</text>')

S0 = [("Getting Started with", "dh"),
      ("LLM Memory Controller", "dh"), ("", ""),
      ("1  Introduction", "dim"),
      ("2  System Requirements", "dim"),
      ("3  Installation", "sec"),
      ("   ☑ Clone the repository", ""),
      ("   ☑ Python 3.10 environment", ""),
      ("   ☑ Install dependencies", ""),
      ("   ☑ Docker + OpenROAD", ""),
      ("   ☑ .env: API key, NetID", ""),
      ("   ☑ Olympus SSH key", ""),
      ("   ☑ Verify: flow.py --dry-run", ""),
      ("4  Quick Start", "sec"),
      ("5  Recovering from a Halted Run", "dim"),
      ("6  Command Reference", "dim"),
      ("env: all settings detected ✓", "okd")]
S1 = [("$ python3 flow.py", "cmd"), ("", ""),
      ("DDR3 Microarchitecture Generator", "hd"),
      ("-- before we start --------------", "dim"),
      ("What's the primary goal?", ""),
      ("  1. Best performance", ""),
      ("  2. Best power savings", ""),
      ("  3. Lowest cost / smallest area", ""),
      ("  4. Balanced / not sure yet", ""),
      ("choice [1]: 1", "in"), ("", ""),
      ("Anything specific to add?", ""),
      ("> DDR3-1600, 4Gb, 2 ranks, ECC", "in"), ("", ""),
      ("NEEDS CLARIFICATION:", "warn"),
      ("  [byte_lanes] How many byte lanes?", ""),
      ("> 4", "in")]
S2 = [("-- resolved configuration -------", "dim"),
      ("  speed_grade       DDR3-1600", ""),
      ("  density           4Gb", ""),
      ("  ranks             2", ""),
      ("  byte_lanes        4", ""),
      ("  ecc_mode          1", ""),
      ("  scheduler_policy  fr_fcfs", ""),
      ("-- JEDEC-derived -----------------", "dim"),
      ("  tCK       1.25 ns  ctrl 200 MHz", ""),
      ("  CL / CWL  11 / 8", ""),
      ("-- consistency -------------------", "dim"),
      ("  [OK] 27/27 checks pass", "ok"), ("", ""),
      ("use this spec for the run?", ""),
      ("(Y = continue / n = keep refining)", "dim"),
      ("> Y", "in"),
      ("wrote runs/…/spec/generated_spec.json", "ok")]
S3 = [("[14:02:11] spec_synthesis    PASS", "okline"),
      ("[14:02:15] spec_review       PASS", "okline"),
      ("-- phase 1: init_fsm, config_regs…", "dim"),
      ("-- phase 2: addr_decoder, …", "dim"),
      ("-- phase 3: cmd_queue, scheduler…", "dim"),
      ("-- phase 4: data_path", "dim"),
      ("[14:09:40] rtl_generation    PASS", "okline"),
      ("[14:21:03] rtl_validation    FAIL", "failline"),
      ("[14:24:30] frontend_regen.   PASS", "okline"),
      ("[14:31:12] rtl_validation    PASS", "okline"),
      ("[15:02:47] backend           PASS", "okline"),
      ("[15:10:05] final_validation  PASS", "okline"), ("", ""),
      ("COMPLETE: spec, RTL, GDSII and", "ok"),
      ("netlist validated.", "ok")]
S4 = [("$ ls runs/20261013-140211-interactive", "cmd"), ("", ""),
      ("RUN_STATE.json   stage outcomes", ""),
      ("flow.log         full run log", ""), ("", ""),
      ("spec/", "hd"),
      ("  generated_spec.json", ""),
      ("  SPEC_REVIEW.json", ""),
      ("drop/", "hd"),
      ("  PHASE1RTL … PHASE4RTL", ""),
      ("    *.sv  *_tb.sv  *_manifest.json", "dim"),
      ("  TOPRTL/   top-level controller", ""),
      ("validation/", "hd"),
      ("  round_1/  round_2/", ""),
      ("backend/", "hd"),
      ("  GDSII layout + sign-off reports", "")]

W, H = 300, 330
W0 = 250
Y = 78
X0, X1, X2, X3, X4 = 40, 350, 720, 1244, 1614
DX, DY = 1132, Y + H/2           # decision diamond centre
VW_ = 1950                       # viewBox width

def arrow(x1, y1, x2, y2, cls="flow"):
    return f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" class="{cls}" marker-end="url(#ah-{cls})"/>'

def box(x, y, w, h, title, lines, cls="sys"):
    s = [f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="6" class="{cls}"/>',
         f'<text x="{x+16}" y="{y+26}" class="boxtitle">{E(title)}</text>']
    for i, l in enumerate(lines):
        s.append(f'<text x="{x+16}" y="{y+48+i*18}" class="boxline">{E(l)}</text>')
    return "\n".join(s)

parts = []
# ---- row 1: user experience
parts.append('<text x="40" y="34" class="rowlabel">WHAT THE USER SEES</text>')
parts.append(step(X0, Y-12, 1, "Set up with USAGE.md"))
parts.append(step(X1, Y-12, 2, "Describe the controller"))
parts.append(step(X2, Y-12, 3, "Review and accept the spec"))
parts.append(step(X3, Y-12, 4, "Pipeline runs on its own"))
parts.append(step(X4, Y-12, 5, "Collect the results"))
parts.append(doc(X0, Y, W0, H, "USAGE.md", S0))
parts.append(screen(X1, Y, W, H, "Terminal — flow.py", S1))
parts.append(screen(X2, Y, W, H, "Terminal — flow.py", S2))
parts.append(screen(X3, Y, W, H, "Terminal — flow.py", S3))
parts.append(screen(X4, Y, W, H, "Terminal — results", S4))
# guide -> S1
parts.append(arrow(X0+W0+4, DY, X1-6, DY))
parts.append(f'<text x="{(X0+W0+X1)/2}" y="{DY-10}" text-anchor="middle" class="alabel">ready</text>')
# S1 -> S2
parts.append(arrow(X1+W+4, DY, X2-6, DY))
parts.append(f'<text x="{(X1+W+X2)/2}" y="{DY-10}" text-anchor="middle" class="alabel">proposes</text>')
# S2 -> diamond
parts.append(arrow(X2+W+4, DY, DX-58, DY))
parts.append(f'<text x="{(X2+W+DX-55)/2}" y="{DY-10}" text-anchor="middle" class="alabel">accept</text>')
# diamond
parts.append(f'<polygon points="{DX},{DY-52} {DX+52},{DY} {DX},{DY+52} {DX-52},{DY}" class="decision"/>')
parts.append(f'<text x="{DX}" y="{DY-4}" text-anchor="middle" class="dtext">Spec review</text>')
parts.append(f'<text x="{DX}" y="{DY+12}" text-anchor="middle" class="dtext">passes?</text>')
# diamond -> S3
parts.append(arrow(DX+54, DY, X3-6, DY))
parts.append(f'<text x="{(DX+52+X3)/2}" y="{DY-10}" text-anchor="middle" class="alabel">yes</text>')
# FAIL loop: diamond bottom -> below screens -> back up into S1
LY = Y + H + 30
parts.append(f'<polyline points="{DX},{DY+54} {DX},{LY} {X1+W/2},{LY} {X1+W/2},{Y+H+6}" class="loop" marker-end="url(#ah-loop)"/>')
parts.append(f'<text x="{(X1+W/2+DX)/2}" y="{LY-8}" text-anchor="middle" class="alabel loopl">no — findings shown, session reopens to revise</text>')
# S3 -> S4
parts.append(arrow(X3+W+4, DY, X4-6, DY))
parts.append(f'<text x="{(X3+W+X4)/2}" y="{DY-10}" text-anchor="middle" class="alabel">≈ 1 hour</text>')

# ---- row 2: behind the scenes
R2 = 500
parts.append(f'<line x1="40" y1="{R2-22}" x2="{VW_-40}" y2="{R2-22}" class="divider"/>')
parts.append(f'<text x="40" y="{R2+4}" class="rowlabel">BEHIND THE SCENES</text>')
OB = R2 + 22
parts.append(f'<rect x="40" y="{OB}" width="1520" height="44" rx="6" class="orch"/>')
parts.append(f'<text x="58" y="{OB+28}" class="boxtitle">flow.py orchestrator</text>')
parts.append(f'<text x="250" y="{OB+28}" class="boxline">runs every stage in order · caps each retry loop · halts with a reason · resumes with --resume</text>')
# repository cylinder
cx, cy, rx, ry, ch = 1760, OB+4, 140, 10, 44
parts.append(f'<path d="M{cx-rx},{cy} v{ch} a{rx},{ry} 0 0 0 {2*rx},0 v{-ch}" class="repo"/>')
parts.append(f'<ellipse cx="{cx}" cy="{cy}" rx="{rx}" ry="{ry}" class="repo"/>')
parts.append(f'<text x="{cx}" y="{cy+30}" text-anchor="middle" class="boxtitle">runs/&lt;run_id&gt;/</text>')
parts.append(f'<text x="{cx}" y="{cy+48}" text-anchor="middle" class="boxline small">run repository</text>')
parts.append(arrow(1562, OB+22, cx-rx-6, OB+22, "dep"))
parts.append(f'<text x="{(1562+cx-rx)/2}" y="{OB+14}" text-anchor="middle" class="alabel">writes</text>')

SB = OB + 90; SH = 120
FX, VX, BX = 40, 735, 1430; FW, VW, BW = 480, 480, 480
parts.append(box(FX, SB, FW, SH, "Frontend", ["Spec agent: English → microarchitecture spec", "RTL generators: phases 1–4 + top level", "Phase agents repair RTL from findings"]))
parts.append(box(VX, SB, VW, SH, "Validation", ["Spec review: schema, JEDEC, register map", "RTL drop: lint, simulation, coverage", "Final check of backend netlists"]))
parts.append(box(BX, SB, BW, SH, "Backend", ["Synthesis, place and route (OpenROAD)", "DRC / LVS sign-off on sky130", "Per-block netlists + GDSII layout"]))
# forward / feedback arrows
ya, yb = SB + 44, SB + 84
parts.append(arrow(FX+FW+2, ya, VX-6, ya))
parts.append(f'<text x="{(FX+FW+VX)/2}" y="{ya-8}" text-anchor="middle" class="alabel">spec, RTL + testbenches</text>')
parts.append(arrow(VX-2, yb, FX+FW+6, yb, "loop"))
parts.append(f'<text x="{(FX+FW+VX)/2}" y="{yb+18}" text-anchor="middle" class="alabel loopl">findings → regenerate</text>')
parts.append(arrow(VX+VW+2, ya, BX-6, ya))
parts.append(f'<text x="{(VX+VW+BX)/2}" y="{ya-8}" text-anchor="middle" class="alabel">validated RTL</text>')
parts.append(arrow(BX-2, yb, VX+VW+6, yb, "loop"))
parts.append(f'<text x="{(VX+VW+BX)/2}" y="{yb+18}" text-anchor="middle" class="alabel loopl">netlists for final check</text>')
# orchestrator -> subsystems
for x in (FX+FW/2, VX+VW/2, BX+60):
    parts.append(arrow(x, OB+46, x, SB-4, "dep"))

# ---- external environment
EY = SB + SH + 62
parts.append(f'<text x="1230" y="{EY+34}" text-anchor="middle" class="rowlabel ext">EXTERNAL SERVICES</text>')
def ext(x, w, title, sub):
    return (f'<rect x="{x}" y="{EY}" width="{w}" height="58" rx="29" class="ext"/>'
            f'<text x="{x+w/2}" y="{EY+25}" text-anchor="middle" class="boxtitle">{E(title)}</text>'
            f'<text x="{x+w/2}" y="{EY+44}" text-anchor="middle" class="boxline small">{E(sub)}</text>')
parts.append(ext(40, 280, "Anthropic API", "Claude: spec agent + RTL repair"))
parts.append(ext(470, 560, "TAMU Olympus cluster", "Verilator lint · Cadence Xcelium simulation"))
parts.append(ext(1500, 410, "Docker: OpenROAD flow", "sky130 PDK · DRC / LVS"))
# connectors
parts.append(f'<line x1="180" y1="{EY-2}" x2="180" y2="{SB+SH+2}" class="ext-link"/>')
parts.append(f'<text x="188" y="{(EY+SB+SH)/2+4}" class="alabel left">HTTPS</text>')
parts.append(f'<line x1="490" y1="{EY+4}" x2="490" y2="{SB+SH+2}" class="ext-link"/>')
parts.append(f'<line x1="1000" y1="{EY+4}" x2="1000" y2="{SB+SH+2}" class="ext-link"/>')
parts.append(f'<text x="745" y="{(EY+SB+SH)/2+4}" text-anchor="middle" class="alabel">SSH + Slurm (TAMU VPN off campus)</text>')
parts.append(f'<line x1="1700" y1="{EY-2}" x2="1700" y2="{SB+SH+2}" class="ext-link"/>')
parts.append(f'<text x="1708" y="{(EY+SB+SH)/2+4}" class="alabel left">container</text>')

VBH = EY + 80
svg = "\n".join(parts)

page = f'''<title>LLM-MC System Diagram</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: one 16:9 slide figure; top row = the user's terminal journey, bottom row = subsystems and the outside world */
:root {{
  --bg: #ffffff; --fg: #1f1a1b; --muted: #6b5f61; --line: #c9bfc1;
  --accent: #500000; --accent-soft: #f5ecec; --sys: #faf7f7; --ext: #eef2f5; --ext-line: #5b7083;
  --loop: #a4590f;
  --display: "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif;
  --mono: "IBM Plex Mono", ui-monospace, Menlo, monospace;
}}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{
  --bg: #171314; --fg: #f1eaeb; --muted: #b3a6a8; --line: #4a3f41;
  --accent: #e08a8a; --accent-soft: #2c1f20; --sys: #211b1c; --ext: #1b2229; --ext-line: #8fa6bb;
  --loop: #e2a35c; color-scheme: dark; }} }}
:root[data-theme="dark"] {{
  --bg: #171314; --fg: #f1eaeb; --muted: #b3a6a8; --line: #4a3f41;
  --accent: #e08a8a; --accent-soft: #2c1f20; --sys: #211b1c; --ext: #1b2229; --ext-line: #8fa6bb;
  --loop: #e2a35c; color-scheme: dark; }}
body {{ background: var(--bg); color: var(--fg); font-family: var(--display); margin: 0; }}
main {{ max-width: 1950px; margin: 0 auto; padding-inline: 16px; padding-block: 24px 40px; }}
h1 {{ font-size: clamp(1.4rem, 2.6vw, 2.1rem); margin: 0 0 4px; text-wrap: balance; }}
.sub {{ color: var(--muted); margin: 0 0 18px; max-width: 70ch; line-height: 1.5; }}
.frame {{ overflow-x: auto; border: 1px solid var(--line); border-radius: 10px; background: var(--bg); }}
svg {{ display: block; width: 100%; min-width: 1100px; height: auto; }}
figcaption {{ color: var(--muted); font-size: 0.9rem; margin-top: 10px; line-height: 1.5; max-width: 90ch; }}
.term {{ fill: #1d1b22; stroke: #3a3742; }}
.doc {{ fill: #fdfcfa; stroke: #cfc6c7; }}
.docbar {{ fill: #500000; }}
.doctitle {{ font: 600 11px var(--mono); fill: #f6e9e9; }}
.d {{ font: 12px var(--display); fill: #2a2324; }}
.d.dh {{ font-weight: 700; font-size: 14px; fill: #500000; }}
.d.sec {{ font-weight: 700; fill: #1f1a1b; }}
.d.dim {{ fill: #8a7d7f; }}
.d.okd {{ font: 600 11.5px var(--mono); fill: #2e7d3c; }}
.termbar {{ fill: #2d2a33; }}
.termtitle {{ font: 11px var(--display); fill: #a9a4b3; }}
.t {{ font: 11.5px var(--mono); fill: #e6e3ec; }}
.t.cmd {{ fill: #9cdcfe; font-weight: 600; }}
.t.hd {{ fill: #ffffff; font-weight: 600; }}
.t.dim {{ fill: #8d889a; }}
.t.in {{ fill: #f0c674; }}
.t.warn {{ fill: #e8b04a; font-weight: 600; }}
.t.ok, .t.okline {{ fill: #7fd18b; }}
.t.failline {{ fill: #f28b82; }}
.rowlabel {{ font: 600 13px var(--display); letter-spacing: .12em; fill: var(--accent); }}
.rowlabel.ext {{ fill: var(--ext-line); }}
.stepdot {{ fill: var(--accent); }}
.stepn {{ font: 700 12px var(--display); fill: var(--bg); }}
.steplabel {{ font: 600 15px var(--display); fill: var(--fg); }}
.flow {{ stroke: var(--accent); stroke-width: 2.2; fill: none; }}
.loop {{ stroke: var(--loop); stroke-width: 2; stroke-dasharray: 7 5; fill: none; }}
.dep {{ stroke: var(--muted); stroke-width: 1.5; fill: none; }}
.ext-link {{ stroke: var(--ext-line); stroke-width: 1.6; stroke-dasharray: 3 4; }}
.alabel {{ font: 12px var(--display); fill: var(--muted); }}
.alabel.loopl {{ fill: var(--loop); font-weight: 600; }}
.decision {{ fill: var(--accent-soft); stroke: var(--accent); stroke-width: 2; }}
.dtext {{ font: 600 12.5px var(--display); fill: var(--fg); }}
.divider {{ stroke: var(--line); stroke-width: 1; }}
.orch {{ fill: var(--accent-soft); stroke: var(--accent); stroke-width: 1.5; }}
.sys {{ fill: var(--sys); stroke: var(--fg); stroke-width: 1.5; }}
.repo {{ fill: var(--sys); stroke: var(--fg); stroke-width: 1.5; }}
.ext {{ fill: var(--ext); stroke: var(--ext-line); stroke-width: 1.5; }}
.boxtitle {{ font: 700 15px var(--display); fill: var(--fg); }}
.boxline {{ font: 13px var(--display); fill: var(--fg); }}
.boxline.small {{ font-size: 12px; fill: var(--muted); }}
#ah-flow path {{ fill: var(--accent); }}
#ah-loop path {{ fill: var(--loop); }}
#ah-dep path {{ fill: var(--muted); }}
</style>
<main>
<h1>LLM Memory Controller: Integrated System</h1>
<p class="sub">One command takes a DDR3 controller from a plain-English description to a validated GDSII layout. The user works in a single terminal session; the subsystems and external services below do the rest.</p>
<figure style="margin:0">
<div class="frame">
<svg viewBox="0 0 {VW_} {VBH:.0f}" role="img" aria-label="User flow: set up with the USAGE.md getting-started guide, describe the controller, review and accept the spec, spec review decision (fail reopens the session), pipeline runs, results. Below: flow.py orchestrates Frontend, Validation and Backend, which use the Anthropic API, the TAMU Olympus cluster and a Docker OpenROAD flow, and write to a run repository.">
<defs>
<marker id="ah-flow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>
<marker id="ah-loop" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>
<marker id="ah-dep" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>
</defs>
{svg}
</svg>
</div>
<figcaption>Top: setup with the Getting Started guide (USAGE.md), then the four screens a user sees in one run of <code>python3 flow.py</code>. The only decision point that comes back to the user is the spec review; RTL and backend failures are repaired automatically (dashed orange arrows) up to a fixed number of rounds. Bottom: how the system is built and what it connects to. Terminal text is representative of real output.</figcaption>
</figure>
</main>
'''
open(OUT, "w").write(page)
print(OUT)
