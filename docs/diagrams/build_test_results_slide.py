"""Generates test_results_slide.html next to this file: every test the
Frontend's handoffs went through, on a timeline from the first run that failed
it to the run that passed it, as a fixed 16:9 frame to screenshot onto a slide.

Dates are the drop dates in Validation/findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/
(<drop>/findings_v2.json). A test is "opened" on the first drop that reports a
finding against it and "passed" on the first later drop where none remain:
  Sep 18 b4d6f45 · Sep 24 1fea117 · Oct 1 5661e03..a5893356 · Oct 8 3596e1ec,
  4b86c7cd3705, a7cd3cb93546 (0 findings, 19/19 paths).
Other sources:
  Validation/findings/HANDOFF_FRONTEND_2026-09-24.md   formal proofs (tRCD, tRP, tRAS, tFAW)
  Frontend2/HANDOFF_VALIDATION_2026-10-08.md   tREFI fix in dab971c2aab9 (not yet validated)
  backend/handoff/FRONTEND_REQUEST_2026-09-24.md   bundle intake of c8ac792
  backend/findings/outbox/.../3b542a6/findings_v2.json   first timing finding (Oct 1)
  backend/handoff/HANDOFF_FRONTEND_2026-10-08.md   DRC/LVS 11/11, 10/11 close 200 MHz
"""
import datetime as dt
import html
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "test_results_slide.html")
E = html.escape
D = lambda m, d: dt.date(2026, m, d)
START, TODAY = D(9, 18), D(10, 14)
TICKS = [(D(9, 18), "Sep 18"), (D(9, 24), "Sep 24"), (D(10, 1), "Oct 1"), (D(10, 8), "Oct 8"),
         (TODAY, "Today")]

# (name, detail, start, end, kind, result)
#   fixed   = failed from start, passed on end
#   first   = passed on its first run (end only)
#   open    = failing from start, still failing today
#   pending = fix handed over on start, awaiting its test run
VALIDATION = [
    ("Host bus transactions", "wb_port · 5 checks", D(9, 18), D(10, 1), "fixed", "Passed Oct 1"),
    ("CSR register readback", "config_regs · 6 registers", D(9, 18), D(10, 1), "fixed", "Passed Oct 1"),
    ("DDR command address", "cmd_gen", D(9, 18), D(10, 1), "fixed", "Passed Oct 1"),
    ("Read data return", "data_path · 2 checks", D(9, 18), D(10, 1), "fixed", "Passed Oct 1"),
    ("Write data beats", "data_path", D(9, 18), D(10, 8), "fixed", "Passed Oct 8"),
    ("DRAM timing rules", "scheduler, bank_tracker · 7 checks", D(9, 18), D(10, 8), "fixed", "Passed Oct 8"),
    ("Command protocol + refresh", "scheduler · 3 checks", D(9, 18), D(10, 8), "fixed", "Passed Oct 8"),
    ("Formal proofs (JasperGold)", "tRCD, tRP, tRAS, tFAW · 2 bugs", D(9, 24), D(10, 8), "fixed", "Passed Oct 8"),
    ("Single spec + address width", "3 blocks · 28- vs 29-bit seam", D(10, 1), D(10, 8), "fixed", "Passed Oct 8"),
    ("Manifest connectivity", "bank_tracker, data_path · 5 ports", D(10, 1), D(10, 8), "fixed", "Passed Oct 8"),
    ("Command queue dequeue", "cmd_queue", D(10, 1), D(10, 8), "fixed", "Passed Oct 8"),
    ("All 19 integration paths", "full controller, Olympus", D(9, 18), D(10, 8), "fixed", "19 / 19 Oct 8"),
    ("Refresh interval (tREFI)", "refresh_ctrl · drop dab971c2aab9", D(10, 8), TODAY, "pending", "Awaiting run"),
]
BACKEND = [
    ("Bundle intake", "11 manifests schema-valid", None, D(9, 24), "first", "Passed Sep 24"),
    ("DRC + LVS sign-off", "11 / 11 blocks, sky130hd", None, D(10, 8), "first", "Passed Oct 8"),
    ("Timing at 200 MHz", "10 / 11 close · scheduler 169 MHz", D(10, 1), TODAY, "open", "Open · 10 / 11"),
]

# ---------------------------------------------------------------- geometry
NX, TX0, TX1, RX = 60, 560, 1580, 1630      # name col, timeline span, result col
DAYS = (TODAY - START).days


def X(day):
    return TX0 + (day - START).days / DAYS * (TX1 - TX0)


RH = 50                                      # row height
TOP = 120                                    # first section header baseline
p = []

# header: column titles + date ticks
p.append(f'<text x="{NX}" y="{TOP-48}" class="colh">Test</text>')
p.append(f'<text x="{RX}" y="{TOP-48}" class="colh">Result</text>')
rows_total = len(VALIDATION) + len(BACKEND)
body_bot = TOP + 44 + len(VALIDATION) * RH + 10 + 44 + (len(BACKEND) - 1) * RH + 30
for day, lab in TICKS:
    x = X(day)
    p.append(f'<text x="{x:.1f}" y="{TOP-48}" text-anchor="middle" class="tick{" today" if day == TODAY else ""}">{lab}</text>')
    p.append(f'<line x1="{x:.1f}" y1="{TOP-36}" x2="{x:.1f}" y2="{body_bot:.1f}" class="{"todayl" if day == TODAY else "gridl"}"/>')


def section(y, title, note):
    p.append(f'<rect x="{NX-12}" y="{y-30}" width="{1860-NX+24}" height="40" rx="6" class="sect"/>')
    p.append(f'<text x="{NX}" y="{y-2}" class="secth">{E(title)}</text>')
    p.append(f'<text x="{NX + 16 + len(title) * 13.2:.0f}" y="{y-3}" class="sectn">{E(note)}</text>')


def check(x, y, cls="ok"):
    p.append(f'<circle cx="{x:.1f}" cy="{y}" r="13" class="{cls}dot"/>')
    p.append(f'<path d="M{x-6:.1f},{y} l4,4.5 l8,-9" class="tick-mark"/>')


def row(y, name, detail, start, end, kind, result):
    p.append(f'<text x="{NX}" y="{y+2}" class="name">{E(name)}</text>')
    p.append(f'<text x="{NX}" y="{y+22}" class="detail">{E(detail)}</text>')
    yc = y - 4
    if kind == "fixed":
        x0, x1 = X(start), X(end)
        p.append(f'<rect x="{x0:.1f}" y="{yc-9}" width="{x1-x0:.1f}" height="18" rx="4" class="span">'
                 f'<title>{E(name)}: failing from {start:%b %-d}, passed {end:%b %-d}</title></rect>')
        p.append(f'<circle cx="{x0:.1f}" cy="{yc}" r="6" class="startdot"/>')
        check(x1, yc)
        rcls = "pass"
    elif kind == "first":
        check(X(end), yc)
        rcls = "pass"
    elif kind == "open":
        x0, x1 = X(start), X(end)
        p.append(f'<rect x="{x0:.1f}" y="{yc-9}" width="{x1-x0:.1f}" height="18" rx="4" class="openspan">'
                 f'<title>{E(name)}: failing since {start:%b %-d}, still open</title></rect>')
        p.append(f'<circle cx="{x0:.1f}" cy="{yc}" r="6" class="startdot bad"/>')
        rcls = "fail"
    else:  # pending
        x0, x1 = X(start), X(end)
        p.append(f'<rect x="{x0:.1f}" y="{yc-9}" width="{x1-x0:.1f}" height="18" rx="4" class="pendspan">'
                 f'<title>{E(name)}: fix handed to Validation {start:%b %-d}, not yet run</title></rect>')
        rcls = "pend"
    p.append(f'<text x="{RX}" y="{y+2}" class="res {rcls}">{E(result)}</text>')


y = TOP
section(y, "Frontend → Validation", "RTL drops, judged by simulation and formal proofs")
y += 44
for r in VALIDATION:
    if r[0].startswith("All 19"):
        p.append(f'<line x1="{NX}" y1="{y-23}" x2="1860" y2="{y-23}" class="sep"/>')
    row(y, *r)
    y += RH
y += 10
section(y, "Frontend → Backend", "RTL → GDSII on sky130hd")
y += 44
for r in BACKEND:
    row(y, *r)
    y += RH

# legend
ly = 1040
items = [("span", "failing → fixed"), ("ok", "passed"), ("openspan", "still open"), ("pendspan", "fix sent, awaiting test")]
lx = NX
for cls, lab in items:
    if cls == "ok":
        check(lx + 13, ly - 6)
        w = 30
    else:
        p.append(f'<rect x="{lx}" y="{ly-14}" width="44" height="16" rx="4" class="{cls}"/>')
        w = 54
    p.append(f'<text x="{lx + w}" y="{ly}" class="leg">{E(lab)}</text>')
    lx += w + len(lab) * 9.6 + 40
p.append(f'<text x="1860" y="{ly}" text-anchor="end" class="leg">dates = Validation drop dates · today = Oct 14</text>')

svg = "\n".join(p)
page = f'''<title>LLM-MC Test Results Slide</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: a fixed 16:9 frame (1920x1080 viewBox): a test-by-test timeline (Gantt) with one row per test,
   grouped by hand-off, dates across the top, result at the right. Deliberately single-theme (light), since it is pasted onto slides. */
:root {{
  --page: #e9e4e4; --slide: #ffffff; --fg: #1f1a1b; --muted: #6b5f61; --faint: #ece6e7;
  --accent: #500000; --span: #c9a3a3; --sect: #f6f0f0;
  --good: #1e7a3c; --bad: #b3261e; --bad-soft: #f3c7c3; --neutral: #5b6470;
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
.colh {{ font: 700 18px var(--display); fill: var(--muted); letter-spacing: .08em; text-transform: uppercase; }}
.tick {{ font: 600 19px var(--display); fill: var(--fg); }}
.tick.today {{ fill: var(--bad); }}
.gridl {{ stroke: var(--faint); stroke-width: 1.5; }}
.todayl {{ stroke: var(--bad); stroke-width: 1.5; stroke-dasharray: 5 5; }}
.sect {{ fill: var(--sect); }}
.secth {{ font: 700 24px var(--display); fill: var(--accent); }}
.sectn {{ font: 17px var(--display); fill: var(--muted); }}
.sep {{ stroke: var(--faint); stroke-width: 1.5; }}
.name {{ font: 700 21px var(--display); fill: var(--fg); }}
.detail {{ font: 15px var(--display); fill: var(--muted); }}
.span {{ fill: var(--span); }}
.openspan {{ fill: var(--bad-soft); stroke: var(--bad); stroke-width: 1.5; }}
.pendspan {{ fill: #ffffff; stroke: var(--neutral); stroke-width: 1.5; stroke-dasharray: 6 4; }}
.startdot {{ fill: var(--accent); }}
.startdot.bad {{ fill: var(--bad); }}
.okdot {{ fill: var(--good); stroke: #ffffff; stroke-width: 2; }}
.tick-mark {{ fill: none; stroke: #ffffff; stroke-width: 3; stroke-linecap: round; stroke-linejoin: round; }}
.res {{ font: 700 19px var(--display); }}
.res.pass {{ fill: var(--good); }}
.res.fail {{ fill: var(--bad); }}
.res.pend {{ fill: var(--neutral); }}
.leg {{ font: 17px var(--display); fill: var(--muted); }}
</style>
<div>
<div class="slide">
<svg viewBox="0 0 1920 1080" role="img" aria-label="Timeline of every test from the Frontend's handoffs. Frontend to Validation: host bus, CSR readback, command address and read data passed on October 1; write data, DRAM timing, protocol, formal proofs, single-spec, manifest connectivity and command queue tests passed on October 8, when all 19 integration paths passed; the tREFI fix is awaiting its run. Frontend to Backend: bundle intake passed September 24, DRC and LVS passed October 8, and timing at 200 MHz is still open with 10 of 11 blocks closing.">
<rect width="1920" height="1080" fill="#ffffff"/>
{svg}
</svg>
</div>
<p class="hint">Screenshot the white frame (16:9) and paste it onto a slide. Hover a bar for its dates. Dates come from the archived Validation and Backend handoffs.</p>
</div>
'''
with open(OUT, "w") as f:
    f.write(page)
print(OUT)
