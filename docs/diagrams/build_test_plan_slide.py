"""Generates test_plan_slide.html next to this file: the next round of testing
as a planned timeline, in the same format as test_results_slide.html, as a
fixed 16:9 frame to screenshot onto a slide.

Every row is an item still open in the handoffs or the roadmap:
  tREFI run            Frontend2/HANDOFF_VALIDATION_2026-10-08.md §10 (dab971c2aab9 not yet validated)
  interactive flow     flow.py interactive spec session (tests/test_flow.py fakes it; no live run yet)
  presets, English     CLAUDE.md roadmap item 7 (preset matrix + adversarial requests)
  spec identity        Validation/findings/HANDOFF_FRONTEND_2026-10-08_reply.md (SPEC_REVISION_REUSED)
  top level, signoff   Validation/SEMESTER_PLAN.md C5, Phase D; flow.py halts on a top-level-only netlist
  scheduler timing     backend/handoff/HANDOFF_FRONTEND_2026-10-08.md §4 (pipeline stage = spec decision)
  gate-level           backend/handoff/HANDOFF_VALIDATION_2026-10-08.md (only wb_port run so far)
Dates are a plan, not results: edit PLAN below and rerun.
"""
import datetime as dt
import html
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "test_plan_slide.html")
E = html.escape
D = lambda m, d: dt.date(2026, m, d)
START, END = D(10, 14), D(10, 21)          # one column per day; END is the boundary after the last day
TODAY, DEADLINE = D(10, 14), D(10, 20)     # Phase 2 integration deadline (end of day)
DAYS_SHOWN = [START + dt.timedelta(days=i) for i in range((END - START).days)]

# (name, detail, start, end, owner, done when, decide_until)
#   decide_until: the bar is dashed up to this date (waiting on a decision)
VALIDATION = [
    ("tREFI fix validation", "drop dab971c2aab9 · refresh_ctrl", D(10, 14), D(10, 15), "Jacob",
     "19/19 paths; tREFI SVA proves 7.8 µs", None),
    ("Spec revision follows content", "compiler stamps a content hash", D(10, 14), D(10, 15), "Lehana",
     "no SPEC_REVISION_REUSED finding", None),
    ("Interactive design session", "python3 flow.py, live API", D(10, 14), D(10, 16), "Lehana",
     "accepted spec passes spec review", None),
    ("Agent repair of seeded faults", "Phase 1–4 agents on injected bugs", D(10, 15), D(10, 18), "Lehana · Jacob",
     "every seeded fault fixed, re-passes", None),
    ("Preset matrix, end to end", "low-cost-embedded → server-grade", D(10, 15), D(10, 18), "Lehana · Jacob",
     "5 presets: review PASS, all paths", None),
    ("Ambiguous + adversarial English", "vague, conflicting, out-of-JEDEC asks", D(10, 16), D(10, 18), "Lehana",
     "asks or rejects; never a bad spec", None),
    ("Assembled top-level controller", "full-chip paths on TOPRTL", D(10, 16), D(10, 19), "Jacob · Lehana",
     "top-level paths pass on Olympus", None),
    ("Coverage + verification plan", "sign-off measurement", D(10, 18), D(10, 20), "Jacob",
     "vplan 100% measured, waivers decided", None),
]
BACKEND = [
    ("11-block rebuild on new drop", "build mode, 5 ns period", D(10, 14), D(10, 15), "Dawson",
     "11/11 DRC + LVS on dab971c2aab9", None),
    ("Scheduler timing closure", "pipeline stage = spec decision", D(10, 14), D(10, 18), "Lehana · Dawson",
     "WNS ≥ 0 at 5 ns; paths still pass", D(10, 14)),
    ("Gate-level netlists through paths", "all 11 blocks (wb_port done)", D(10, 16), D(10, 19), "Jacob · Dawson",
     "11/11 netlists pass their paths", None),
    ("Full-controller timing at 200 MHz", "clock tree + inter-block wiring", D(10, 17), D(10, 19), "Dawson",
     "assembled top closes 200 MHz", None),
    ("English in → GDSII out", "one flow.py run, all stages", D(10, 19), D(10, 20), "All",
     "COMPLETE with no manual step", None),
]

# ---------------------------------------------------------------- geometry
NX, TX0, TX1 = 60, 520, 1300               # name col, timeline span
OX, CX = 1330, 1500                        # owner col, done-when col
DAYS = (END - START).days


def X(day):
    """Left edge of a day's column."""
    return TX0 + (day - START).days / DAYS * (TX1 - TX0)


def XE(day):
    """Right edge of a day's column (end of that day)."""
    return X(day + dt.timedelta(days=1))


RH = 60
TOP = 118
p = []

p.append(f'<text x="{NX}" y="{TOP-46}" class="colh">Test</text>')
p.append(f'<text x="{OX}" y="{TOP-46}" class="colh">Owner</text>')
p.append(f'<text x="{CX}" y="{TOP-46}" class="colh">Done when</text>')
body_bot = TOP + 44 + len(VALIDATION) * RH + 10 + 44 + (len(BACKEND) - 1) * RH + 30
for day in DAYS_SHOWN:
    x, xm = X(day), (X(day) + XE(day)) / 2
    today = day == TODAY
    p.append(f'<text x="{xm:.1f}" y="{TOP-60}" text-anchor="middle" class="dow{" today" if today else ""}">'
             f'{"Today" if today else day.strftime("%a")}</text>')
    p.append(f'<text x="{xm:.1f}" y="{TOP-38}" text-anchor="middle" class="tick{" today" if today else ""}">'
             f'{day.month}/{day.day}</text>')
    if day != START:
        p.append(f'<line x1="{x:.1f}" y1="{TOP-30}" x2="{x:.1f}" y2="{body_bot:.1f}" class="gridl"/>')
xt = X(TODAY)
p.append(f'<line x1="{xt:.1f}" y1="{TOP-30}" x2="{xt:.1f}" y2="{body_bot:.1f}" class="todayl"/>')
xd = XE(DEADLINE)
p.append(f'<line x1="{xd:.1f}" y1="{TOP-76}" x2="{xd:.1f}" y2="{body_bot:.1f}" class="demol"/>')
p.append(f'<text x="{xd-8:.1f}" y="{body_bot-8:.1f}" text-anchor="end" class="deadl">Deadline 10/20</text>')


def section(y, title, note):
    p.append(f'<rect x="{NX-12}" y="{y-30}" width="{1860-NX+24}" height="40" rx="6" class="sect"/>')
    p.append(f'<text x="{NX}" y="{y-2}" class="secth">{E(title)}</text>')
    p.append(f'<text x="{NX + 16 + len(title) * 13.2:.0f}" y="{y-3}" class="sectn">{E(note)}</text>')


def target(x, y):
    p.append(f'<path d="M{x:.1f},{y-12} l12,12 l-12,12 l-12,-12 z" class="target"/>')


def row(y, name, detail, start, end, owner, done, decide):
    p.append(f'<text x="{NX}" y="{y+2}" class="name">{E(name)}</text>')
    p.append(f'<text x="{NX}" y="{y+22}" class="detail">{E(detail)}</text>')
    yc = y - 4
    x0, x1 = X(start) + 3, XE(end) - 3
    if decide:
        xm = XE(decide)
        p.append(f'<rect x="{x0:.1f}" y="{yc-9}" width="{xm-x0:.1f}" height="18" rx="4" class="decide">'
                 f'<title>{E(name)}: decision needed by {decide:%b %-d}</title></rect>')
        p.append(f'<text x="{(x0+xm)/2:.1f}" y="{yc+5}" text-anchor="middle" class="decidet">decide</text>')
        x0 = xm + 4
    p.append(f'<rect x="{x0:.1f}" y="{yc-9}" width="{x1-x0:.1f}" height="18" rx="4" class="plan">'
             f'<title>{E(name)}: {start:%b %-d} to {end:%b %-d}, owner {E(owner)}</title></rect>')
    target(x1, yc)
    p.append(f'<text x="{OX}" y="{y+2}" class="owner">{E(owner)}</text>')
    p.append(f'<text x="{CX}" y="{y+2}" class="done">{E(done)}</text>')
    p.append(f'<text x="{CX}" y="{y+22}" class="by">by {end:%a %-m/%-d}</text>')


y = TOP
section(y, "Frontend → Validation", "next drops, judged by simulation and formal proofs")
y += 44
for r in VALIDATION:
    row(y, *r)
    y += RH
y += 10
section(y, "Frontend → Backend", "RTL → GDSII on sky130hd, 200 MHz target")
y += 44
for r in BACKEND:
    row(y, *r)
    y += RH

# legend
ly = 1046
lx = NX
p.append(f'<rect x="{lx}" y="{ly-14}" width="44" height="16" rx="4" class="plan"/>')
p.append(f'<text x="{lx+54}" y="{ly}" class="leg">planned testing window</text>')
lx += 54 + 22 * 9.6 + 40
target(lx + 12, ly - 6)
p.append(f'<text x="{lx+32}" y="{ly}" class="leg">pass target</text>')
lx += 32 + 11 * 9.6 + 40
p.append(f'<rect x="{lx}" y="{ly-14}" width="44" height="16" rx="4" class="decide"/>')
p.append(f'<text x="{lx+54}" y="{ly}" class="leg">waiting on a team decision</text>')
p.append(f'<text x="1860" y="{ly}" text-anchor="end" class="leg">planned dates · every test due by the 10/20 deadline</text>')

svg = "\n".join(p)
page = f'''<title>LLM-MC Test Plan Slide</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: a fixed 16:9 frame (1920x1080 viewBox): the next round of testing as a planned timeline (one row per test,
   grouped by hand-off), with owner and exit criterion at the right. Same visual system as test_results_slide.html.
   Deliberately single-theme (light), since it is pasted onto slides. */
:root {{
  --page: #e9e4e4; --slide: #ffffff; --fg: #1f1a1b; --muted: #6b5f61; --faint: #ece6e7;
  --accent: #500000; --plan: #f3e9e9; --sect: #f6f0f0; --bad: #b3261e; --neutral: #5b6470;
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
.tick {{ font: 600 18px var(--display); fill: var(--fg); }}
.tick.today {{ fill: var(--bad); }}
.dow {{ font: 600 15px var(--display); fill: var(--muted); text-transform: uppercase; letter-spacing: .06em; }}
.dow.today, .tick.today {{ fill: var(--bad); }}
.deadl {{ font: 700 17px var(--display); fill: var(--accent); }}
.gridl {{ stroke: var(--faint); stroke-width: 1.5; }}
.todayl {{ stroke: var(--bad); stroke-width: 1.5; stroke-dasharray: 5 5; }}
.demol {{ stroke: var(--accent); stroke-width: 2.5; }}
.sect {{ fill: var(--sect); }}
.secth {{ font: 700 24px var(--display); fill: var(--accent); }}
.sectn {{ font: 17px var(--display); fill: var(--muted); }}
.name {{ font: 700 21px var(--display); fill: var(--fg); }}
.detail {{ font: 15px var(--display); fill: var(--muted); }}
.plan {{ fill: var(--plan); stroke: var(--accent); stroke-width: 1.8; }}
.decide {{ fill: #ffffff; stroke: var(--neutral); stroke-width: 1.5; stroke-dasharray: 6 4; }}
.decidet {{ font: 600 12px var(--display); fill: var(--neutral); }}
.target {{ fill: var(--accent); stroke: #ffffff; stroke-width: 2; }}
.owner {{ font: 600 18px var(--display); fill: var(--fg); }}
.done {{ font: 600 17px var(--display); fill: var(--fg); }}
.by {{ font: 15px var(--display); fill: var(--muted); }}
.leg {{ font: 17px var(--display); fill: var(--muted); }}
</style>
<div>
<div class="slide">
<svg viewBox="0 0 1920 1080" role="img" aria-label="Phase 2 integration test plan from October 14 to the October 20 deadline. Frontend to Validation: tREFI fix validation, spec revision tracking, the interactive design session, agent repair of seeded faults, the preset matrix, ambiguous English requests, the assembled top-level controller, and coverage sign-off. Frontend to Backend: an 11-block rebuild, scheduler timing closure after a spec decision, gate-level netlists through the paths, full-controller timing at 200 MHz, and one English-to-GDSII run on the final day.">
<rect width="1920" height="1080" fill="#ffffff"/>
{svg}
</svg>
</div>
<p class="hint">Screenshot the white frame (16:9) and paste it onto a slide. Hover a bar for its dates. Dates are a plan; edit build_test_plan_slide.py to change them.</p>
</div>
'''
with open(OUT, "w") as f:
    f.write(page)
print(OUT)
