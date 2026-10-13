"""Generates user_flow_slide.html next to this file: the "what the user sees"
half of the system diagram as a fixed 16:9 frame, sized to screenshot into a
slide. Two rows (setup -> describe -> review, then decision -> run -> results)
so the terminal text stays legible when projected."""
import html
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "user_flow_slide.html")
E = html.escape
LH = 21                                   # terminal / doc line height
K = 0.82                                  # panels are drawn at full size, then scaled by K


def window(x, y, w, h, title, lines, kind):
    """kind 'term' = dark terminal, 'doc' = the rendered guide."""
    s = [f'<g transform="translate({x},{y}) scale({K})">',
         f'<rect width="{w}" height="{h}" rx="10" class="{kind}"/>',
         f'<rect width="{w}" height="32" rx="10" class="{kind}bar"/>',
         f'<rect y="22" width="{w}" height="10" class="{kind}bar"/>']
    if kind == "term":
        s.append('<circle cx="18" cy="16" r="5.5" fill="#ff5f57"/>'
                 '<circle cx="36" cy="16" r="5.5" fill="#febc2e"/>'
                 '<circle cx="54" cy="16" r="5.5" fill="#28c840"/>')
        s.append(f'<text x="{w/2}" y="21" text-anchor="middle" class="termtitle">{E(title)}</text>')
    else:
        s.append(f'<text x="16" y="21" class="doctitle">{E(title)}</text>')
    ty = 60
    for text, cls in lines:
        if text:
            s.append(f'<text x="18" y="{ty}" class="{"t" if kind == "term" else "d"} {cls}" '
                     f'xml:space="preserve">{E(text)}</text>')
        ty += LH
    s.append('</g>')
    return "\n".join(s)


def step(x, y, n, label):
    return (f'<circle cx="{x+21}" cy="{y-12}" r="21" class="stepdot"/>'
            f'<text x="{x+21}" y="{y-3}" text-anchor="middle" class="stepn">{n}</text>'
            f'<text x="{x+54}" y="{y}" class="steplabel">{E(label)}</text>')


def arrow(x1, y1, x2, y2, cls="flow"):
    return f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" class="{cls}" marker-end="url(#ah-{cls})"/>'


def label(x, y, text, cls="alabel", anchor="middle"):
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" class="{cls}">{E(text)}</text>'


GUIDE = [("Getting Started with", "dh"),
         ("LLM Memory Controller", "dh"), ("", ""),
         ("1  Introduction", "dim"),
         ("2  System Requirements", "dim"),
         ("3  Installation", "sec"),
         ("    ☑  Clone the repository", ""),
         ("    ☑  Python 3.10 environment", ""),
         ("    ☑  Install dependencies", ""),
         ("    ☑  Docker + OpenROAD", ""),
         ("    ☑  .env: API key, NetID", ""),
         ("    ☑  Olympus SSH key", ""),
         ("    ☑  Verify: flow.py --dry-run", ""),
         ("4  Quick Start", "sec"),
         ("5  Recovering from a Halted Run", "dim"),
         ("6  Command Reference", "dim"),
         ("env: all settings detected ✓", "okd")]
DESCRIBE = [("$ python3 flow.py", "cmd"),
            ("DDR3 Microarchitecture Generator", "hd"),
            ("-- before we start ------------------", "dim"),
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
REVIEW = [("-- resolved configuration -----------", "dim"),
          ("  speed_grade       DDR3-1600", ""),
          ("  density           4Gb", ""),
          ("  ranks             2", ""),
          ("  byte_lanes        4", ""),
          ("  ecc_mode          1", ""),
          ("-- JEDEC-derived ---------------------", "dim"),
          ("  tCK       1.25 ns   ctrl 200 MHz", ""),
          ("  CL / CWL  11 / 8", ""),
          ("-- consistency -----------------------", "dim"),
          ("  [OK] 27/27 checks pass", "ok"), ("", ""),
          ("use this spec for the run?", ""),
          ("(Y = continue / n = keep refining)", "dim"),
          ("> Y", "in"),
          ("wrote runs/…/spec/generated_spec.json", "ok")]
RUN = [("[14:02:11] spec_synthesis         PASS", "ok"),
       ("[14:02:15] spec_review            PASS", "ok"),
       ("-- phase 1: init_fsm, config_regs, …", "dim"),
       ("-- phase 2: addr_decoder, …", "dim"),
       ("-- phase 3: cmd_queue, scheduler, …", "dim"),
       ("-- phase 4: data_path", "dim"),
       ("[14:09:40] rtl_generation         PASS", "ok"),
       ("[14:21:03] rtl_validation         FAIL", "fail"),
       ("[14:24:30] frontend_regeneration  PASS", "ok"),
       ("[14:31:12] rtl_validation         PASS", "ok"),
       ("[15:02:47] backend                PASS", "ok"),
       ("[15:10:05] final_validation       PASS", "ok"), ("", ""),
       ("COMPLETE: spec, RTL, GDSII and", "okb"),
       ("netlist validated.", "okb")]
RESULTS = [("$ ls runs/20261013-140211-interactive", "cmd"), ("", ""),
           ("RUN_STATE.json    stage outcomes", ""),
           ("flow.log          full run log", ""),
           ("spec/", "hd"),
           ("  generated_spec.json", ""),
           ("  SPEC_REVIEW.json", ""),
           ("drop/", "hd"),
           ("  PHASE1RTL … PHASE4RTL", ""),
           ("    *.sv   *_tb.sv   *_manifest.json", "dim"),
           ("  TOPRTL/    top-level controller", ""),
           ("validation/", "hd"),
           ("  round_1/   round_2/", ""),
           ("backend/", "hd"),
           ("  GDSII layout + sign-off reports", "")]

# geometry (viewBox 1920 x 1080)
TW0, TH0, GW0 = 560, 410, 400          # panels as drawn (before scaling)
TW, TH, GW = TW0 * K, TH0 * K, GW0 * K  # panels as laid out
GAP = 130
RA, RB = 140, 650                       # row tops
P1 = (1920 - (GW + 2 * TW + 2 * GAP)) / 2
P2 = P1 + GW + GAP
P3 = P2 + TW + GAP                      # row A x
P4, P5 = P2, P3                         # row B x (aligned under row A)
DX, DY = P1 + GW / 2, RB + TH / 2 - 20  # decision diamond centre
DHW, DHH = 120, 88

p = []
# row A: setup -> describe -> review
p.append(step(P1, RA - 26, 1, "Set up with USAGE.md"))
p.append(step(P2, RA - 26, 2, "Describe the controller"))
p.append(step(P3, RA - 26, 3, "Review and accept the spec"))
p.append(window(P1, RA, GW0, TH0, "USAGE.md", GUIDE, "doc"))
p.append(window(P2, RA, TW0, TH0, "Terminal — flow.py", DESCRIBE, "term"))
p.append(window(P3, RA, TW0, TH0, "Terminal — flow.py", REVIEW, "term"))
mid_a = RA + TH / 2
p.append(arrow(P1 + GW + 6, mid_a, P2 - 8, mid_a))
p.append(label((P1 + GW + P2) / 2, mid_a - 14, "ready"))
p.append(arrow(P2 + TW + 6, mid_a, P3 - 8, mid_a))
p.append(label((P2 + TW + P3) / 2, mid_a - 14, "proposes"))

# review -> decision: down from step 3, back across the gutter, into the diamond top
GUT = RA + TH + 52
p.append(f'<polyline points="{P3 + TW/2},{RA + TH + 6} {P3 + TW/2},{GUT} {DX},{GUT} {DX},{DY - DHH - 8}" '
         f'class="flow" marker-end="url(#ah-flow)"/>')
p.append(label((P3 + TW / 2 + DX) / 2 + 120, GUT + 28, "accept → automated spec review"))

# decision
p.append(f'<polygon points="{DX},{DY-DHH} {DX+DHW},{DY} {DX},{DY+DHH} {DX-DHW},{DY}" class="decision"/>')
p.append(label(DX, DY - 6, "Spec review", "dtext"))
p.append(label(DX, DY + 20, "passes?", "dtext"))
# yes -> run
p.append(arrow(DX + DHW + 6, DY, P4 - 8, DY))
p.append(label((DX + DHW + P4) / 2, DY - 14, "yes"))
# no -> back to step 2: out the diamond's left, up the margin, along the gap
# between the rows (above the accept line), into step 2 from below
LX = P1 - 90
LY = RA + TH + 24
p.append(f'<polyline points="{DX - DHW - 4},{DY} {LX},{DY} {LX},{LY} {P2 + TW/2},{LY} {P2 + TW/2},{RA + TH + 8}" '
         f'class="loop" marker-end="url(#ah-loop)"/>')
p.append(label(DX - DHW - 30, DY - 14, "no", "nolabel"))
p.append(f'<text transform="translate({LX - 16},{(LY + DY) / 2}) rotate(-90)" text-anchor="middle" '
         f'class="nolabel">findings shown, back to step 2</text>')

# row B: run -> results
p.append(step(P4, RB - 26, 4, "Pipeline runs on its own"))
p.append(step(P5, RB - 26, 5, "Collect the results"))
p.append(window(P4, RB, TW0, TH0, "Terminal — flow.py", RUN, "term"))
p.append(window(P5, RB, TW0, TH0, "Terminal — results", RESULTS, "term"))
p.append(arrow(P4 + TW + 6, DY, P5 - 8, DY))
p.append(label((P4 + TW + P5) / 2, DY - 14, "≈ 1 hour"))

svg = "\n".join(p)
page = f'''<title>LLM-MC User Flow Slide</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: a fixed 16:9 frame (1920x1080 viewBox) scaled to the window, ready to screenshot onto a white slide.
   Deliberately single-theme (light), since it is pasted onto slides. */
:root {{
  --page: #e9e4e4; --slide: #ffffff; --fg: #1f1a1b; --muted: #6b5f61;
  --accent: #500000; --accent-soft: #f6eded; --loop: #a4590f; --loop-soft: #fbf1e6;
  --display: "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif;
  --mono: "IBM Plex Mono", ui-monospace, Menlo, monospace;
  color-scheme: light;
}}
html, body {{ height: 100%; }}
body {{ background: var(--page); color: var(--fg); margin: 0; font-family: var(--display);
        display: grid; place-items: center; padding-inline: 16px; padding-block: 16px; box-sizing: border-box; }}
.slide {{ width: min(100%, calc((100vh - 72px) * 16 / 9)); aspect-ratio: 16 / 9; max-width: 100%;
          background: var(--slide); box-shadow: 0 1px 3px rgba(0,0,0,.12), 0 8px 24px rgba(0,0,0,.08); }}
.slide svg {{ display: block; width: 100%; height: 100%; }}
.hint {{ color: var(--muted); font-size: 13px; margin-top: 10px; text-align: center; }}
.term {{ fill: #1d1b22; stroke: #3a3742; }}
.termbar {{ fill: #2d2a33; }}
.termtitle {{ font: 14px var(--display); fill: #a9a4b3; }}
.t {{ font: 15px var(--mono); fill: #e6e3ec; }}
.t.cmd {{ fill: #9cdcfe; font-weight: 600; }}
.t.hd {{ fill: #ffffff; font-weight: 600; }}
.t.dim {{ fill: #8d889a; }}
.t.in {{ fill: #f0c674; }}
.t.warn {{ fill: #e8b04a; font-weight: 600; }}
.t.ok {{ fill: #7fd18b; }}
.t.okb {{ fill: #7fd18b; font-weight: 600; }}
.t.fail {{ fill: #f28b82; }}
.doc {{ fill: #fdfcfa; stroke: #cfc6c7; }}
.docbar {{ fill: var(--accent); }}
.doctitle {{ font: 600 14px var(--mono); fill: #f6e9e9; }}
.d {{ font: 16px var(--display); fill: #2a2324; }}
.d.dh {{ font-weight: 700; font-size: 19px; fill: var(--accent); }}
.d.sec {{ font-weight: 700; fill: var(--fg); }}
.d.dim {{ fill: #8a7d7f; }}
.d.okd {{ font: 600 14px var(--mono); fill: #2e7d3c; }}
.stepdot {{ fill: var(--accent); }}
.stepn {{ font: 700 24px var(--display); fill: #ffffff; }}
.steplabel {{ font: 700 34px var(--display); fill: var(--fg); }}
.flow {{ stroke: var(--accent); stroke-width: 3; fill: none; }}
.loop {{ stroke: var(--loop); stroke-width: 2.6; stroke-dasharray: 9 6; fill: none; }}
.alabel {{ font: 20px var(--display); fill: var(--muted); }}
.decision {{ fill: var(--accent-soft); stroke: var(--accent); stroke-width: 3; }}
.dtext {{ font: 700 22px var(--display); fill: var(--fg); }}
.nopill {{ fill: var(--loop-soft); stroke: var(--loop); stroke-width: 2; }}
.nolabel {{ font: 600 17px var(--display); fill: var(--loop); }}
#ah-flow path {{ fill: var(--accent); }}
#ah-loop path {{ fill: var(--loop); }}
</style>
<div>
<div class="slide">
<svg viewBox="0 0 1920 1080" role="img" aria-label="What the user sees: 1 set up with USAGE.md, 2 describe the controller in the terminal, 3 review and accept the spec, then the automated spec review; if it fails the session reopens at step 2, if it passes 4 the pipeline runs on its own for about an hour and 5 the user collects the results in the run folder.">
<defs>
<marker id="ah-flow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>
<marker id="ah-loop" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>
</defs>
<rect width="1920" height="1080" fill="#ffffff"/>
{svg}
</svg>
</div>
<p class="hint">Screenshot the white frame (16:9) and paste it onto a slide. Terminal text is representative of real output.</p>
</div>
'''
with open(OUT, "w") as f:
    f.write(page)
print(OUT)
