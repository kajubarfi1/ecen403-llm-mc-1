"""Generates outputs_slide.html next to this file: what one run produces, as a
fixed 16:9 frame to screenshot onto a slide. Four panels: the generated spec,
the Phase 1 RTL and testbenches, the validation report, and the backend GDSII
layout (assets/gdsii_layout.jpg, embedded). Code and JSON excerpts are copied
from real outputs in Frontend2/OutputFolders and Validation/findings/outbox."""
import base64
import html
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "outputs_slide.html")
E = html.escape
LH = 20                                    # code line height

with open(os.path.join(HERE, "assets", "gdsii_layout.jpg"), "rb") as f:
    GDS = "data:image/jpeg;base64," + base64.b64encode(f.read()).decode()
GDS_W, GDS_H = 900, 688

# ---------------------------------------------------------------- highlighting
SV_KW = r"\b(module|endmodule|parameter|int|input|output|logic|localparam|typedef|enum|initial|begin|end|if|else|fork|join_any|repeat|wait)\b"


def hl_json(line):
    out, i = [], 0
    for m in re.finditer(r'("(?:[^"\\]|\\.)*")(\s*:)?|(-?\b\d+(?:\.\d+)?\b)|\b(true|false|null)\b', line):
        out.append(E(line[i:m.start()]))
        if m.group(1):
            cls = "k" if m.group(2) else "s"
            out.append(f'<tspan class="{cls}">{E(m.group(1))}</tspan>{E(m.group(2) or "")}')
        elif m.group(3):
            out.append(f'<tspan class="n">{E(m.group(3))}</tspan>')
        else:
            out.append(f'<tspan class="n">{E(m.group(4))}</tspan>')
        i = m.end()
    out.append(E(line[i:]))
    return "".join(out)


def hl_sv(line):
    code, _, comment = line.partition("//")
    out, i = [], 0
    for m in re.finditer(SV_KW + r"|(\$\w+)|(\"[^\"]*\")|(\b\d+'[hbd][0-9A-Fa-f_]+\b|\b\d+\b)", code):
        out.append(E(code[i:m.start()]))
        if m.group(1):
            out.append(f'<tspan class="kw">{E(m.group(1))}</tspan>')
        elif m.group(2):
            out.append(f'<tspan class="sys">{E(m.group(2))}</tspan>')
        elif m.group(3):
            out.append(f'<tspan class="s">{E(m.group(3))}</tspan>')
        else:
            out.append(f'<tspan class="n">{E(m.group(4))}</tspan>')
        i = m.end()
    out.append(E(code[i:]))
    if _ or comment:
        out.append(f'<tspan class="c">//{E(comment)}</tspan>')
    return "".join(out)


def hl_log(line):
    if "PASS" in line:
        return re.sub(r"(PASS(?:ED)?)", r'<tspan class="ok">\1</tspan>', E(line))
    return E(line)


# ---------------------------------------------------------------- pieces
def code(x, y, lines, hl, cls="code"):
    s = []
    for i, l in enumerate(lines):
        if l:
            s.append(f'<text x="{x}" y="{y + i * LH}" class="{cls}" xml:space="preserve">{hl(l)}</text>')
    return "\n".join(s)


def window(x, y, w, h, tabs, active=0):
    """An editor window with file tabs; returns the svg and the content origin."""
    s = [f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="10" class="win"/>',
         f'<path d="M{x},{y+38} v-28 a10,10 0 0 1 10,-10 h{w-20} a10,10 0 0 1 10,10 v28 z" class="winbar"/>',
         f'<circle cx="{x+18}" cy="{y+19}" r="5.5" fill="#ff5f57"/>'
         f'<circle cx="{x+36}" cy="{y+19}" r="5.5" fill="#febc2e"/>'
         f'<circle cx="{x+54}" cy="{y+19}" r="5.5" fill="#28c840"/>']
    tx = x + 76
    for i, t in enumerate(tabs):
        tw = 18 + len(t) * 8.6
        s.append(f'<rect x="{tx}" y="{y+7}" width="{tw}" height="31" rx="6" class="{"tab on" if i == active else "tab"}"/>')
        s.append(f'<text x="{tx + tw/2}" y="{y+28}" text-anchor="middle" class="{"tabt on" if i == active else "tabt"}">{E(t)}</text>')
        tx += tw + 6
    return "\n".join(s)


def step(x, y, n, title, path):
    return (f'<circle cx="{x+20}" cy="{y-11}" r="20" class="stepdot"/>'
            f'<text x="{x+20}" y="{y-3}" text-anchor="middle" class="stepn">{n}</text>'
            f'<text x="{x+52}" y="{y}" class="steplabel">{E(title)}</text>'
            f'<text x="{x+860}" y="{y-2}" text-anchor="end" class="path">{E(path)}</text>')


SPEC = ['{',
        '  "design_id": "ddr3_mc_core_v2",',
        '  "revision": "golden_ddr3_1600k_x8_2lane_1rank",',
        '  "memory_geometry": {',
        '    "row_bits": 15, "column_bits": 10, "bank_bits": 3,',
        '    "ranks": 1, "burst_length": 8,',
        '    "device_width_bits": 8, "byte_lanes": 2,',
        '    "address_mapping": "row-bank-column"',
        '  },',
        '  "timing_model": {',
        '    "speed_bin": "DDR3-1600K (11-11-11)",',
        '    "tRCD": 13.75, "tRP": 13.75, "tRAS": 35.0,',
        '    "tRFC": 160.0, "tREFI": 7800.0',
        '  },',
        '  …',
        '}']
RTL = ['module init_fsm #(',
       '    parameter int DDR_ADDR_W = 15',
       ') (',
       '    input  logic clk,',
       '    input  logic rst_n,',
       '    output logic init_done,',
       '    output logic [3:0] init_cmd,',
       '    …',
       ');',
       '  localparam WAIT_RESET = 40000;',
       '  localparam WAIT_CKE   = 100000;',
       '  localparam MR0_VAL = 15\'h1D34;',
       '  …',
       'endmodule']
TB = ['module init_fsm_tb;',
      '  initial begin',
      '    rst_n=0; repeat(10) @(posedge clk);',
      '    rst_n=1; enable=1;',
      '    wait(init_done);',
      '    check("init_done asserted", …);',
      '    check("4 MRS commands", …);',
      '    check("MR order 2->3->1->0", …);',
      '    check("MR0 encoding matches spec",',
      '          dut.MR0_VAL===15\'h1D34);',
      '    …',
      '    $display("ALL %0d TESTS PASSED", …);',
      '  end',
      'endmodule']
HANDOFF = ['{',
           '  "drop_id": "a7cd3cb93546",',
           '  "spec_revision": "golden_ddr3_1600k_x8_2lane_1rank",',
           '  "status": "PASS",',
           '  "failed_modules": [],',
           '  "files": ["retry_instructions.json",',
           '            "findings_v2.json", "SPEC_REVIEW.json"]',
           '}']
PHASE1 = ['{ "pipeline": "phase1", "status": "PASS",',
          '  "lint_status": "PASS", "sim_status": "PASS",',
          '  "modules": ["init_fsm", "config_regs", "wb_port"] }']
SIMLOG = ['init_fsm_tb     ALL 11 TESTS PASSED',
          'config_regs_tb  PASSED',
          'wb_port_tb      PASSED']

# ---------------------------------------------------------------- layout
W, H = 860, 400
XL, XR = 70, 990
YA, YB = 128, 630                          # panel tops (headers sit above)

p = []
# 1 spec
p.append(step(XL, YA - 22, 1, "Generated spec", "spec/generated_spec.json"))
p.append(window(XL, YA, W, H, ["generated_spec.json", "microarch_report.json"]))
p.append(code(XL + 22, YA + 66, SPEC, hl_json))

# 2 phase 1 RTL + testbenches
p.append(step(XR, YA - 22, 2, "Phase 1 RTL + testbenches", "drop/PHASE1RTL/"))
p.append(window(XR, YA, W, H, ["init_fsm.sv", "init_fsm_tb.sv", "init_fsm_manifest.json"]))
p.append(f'<line x1="{XR + 420}" y1="{YA + 50}" x2="{XR + 420}" y2="{YA + H - 46}" class="split"/>')
p.append(code(XR + 22, YA + 66, RTL, hl_sv, "code sm"))
p.append(code(XR + 440, YA + 66, TB, hl_sv, "code sm"))
p.append(f'<rect x="{XR}" y="{YA + H - 38}" width="{W}" height="38" class="strip"/>')
p.append(f'<text x="{XR + 22}" y="{YA + H - 13}" class="stript">PHASE1RTL/  ·  init_fsm  ·  config_regs  ·  wb_port  —  each as .sv + _tb.sv + _manifest.json</text>')

# 3 validation report
p.append(step(XL, YB - 22, 3, "Validation report", "validation/round_N/HANDOFF.json"))
p.append(window(XL, YB, W, H, ["HANDOFF.json", "phase1_final_report.json", "sim log"]))
p.append(code(XL + 22, YB + 66, HANDOFF, hl_json))
p.append(f'<line x1="{XL + 22}" y1="{YB + 236}" x2="{XL + W - 22}" y2="{YB + 236}" class="split"/>')
p.append(code(XL + 22, YB + 264, PHASE1, hl_json))
p.append(f'<rect x="{XL + 22}" y="{YB + 318}" width="{W - 44}" height="68" rx="6" class="logbox"/>')
p.append(code(XL + 38, YB + 340, SIMLOG, hl_log, "code log"))

# 4 GDSII
p.append(step(XR, YB - 22, 4, "GDSII layout", "backend/  ·  sky130hd"))
p.append(window(XR, YB, W, H, ["6_final.gds"]))
ih = H - 60
iw = ih * GDS_W / GDS_H
p.append(f'<image href="{GDS}" x="{XR + 14}" y="{YB + 48}" width="{iw:.1f}" height="{ih}" preserveAspectRatio="xMidYMid meet"/>')
lx = XR + 14 + iw + 30
legend = [("#3a3cf0", "Metal routing"),
          ("#e24ad9", "Vias and upper metal"),
          ("#c9b458", "VDD / VSS power rails"),
          ("#8fe3f0", "I/O pins at the boundary")]
p.append(f'<text x="{lx}" y="{YB + 86}" class="legendh">Placed and routed</text>')
p.append(f'<text x="{lx}" y="{YB + 110}" class="legendt">sky130 standard cells</text>')
for i, (c, t) in enumerate(legend):
    yy = YB + 160 + i * 40
    p.append(f'<rect x="{lx}" y="{yy - 15}" width="20" height="20" rx="3" fill="{c}"/>')
    p.append(f'<text x="{lx + 32}" y="{yy}" class="legendt">{E(t)}</text>')
p.append(f'<text x="{lx}" y="{YB + H - 30}" class="legendt dim">RTL → synthesis → place</text>')
p.append(f'<text x="{lx}" y="{YB + H - 8}" class="legendt dim">→ route (OpenROAD)</text>')

svg = "\n".join(p)
page = f'''<title>LLM-MC Outputs Slide</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: a fixed 16:9 frame (1920x1080 viewBox) with a 2x2 grid of output panels, ready to screenshot onto a white slide.
   Deliberately single-theme (light), since it is pasted onto slides. */
:root {{
  --page: #e9e4e4; --slide: #ffffff; --fg: #1f1a1b; --muted: #6b5f61; --accent: #500000;
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
.win {{ fill: #1d1b22; stroke: #3a3742; }}
.winbar {{ fill: #2d2a33; }}
.tab {{ fill: #26232c; }}
.tab.on {{ fill: #1d1b22; }}
.tabt {{ font: 13px var(--mono); fill: #8d889a; }}
.tabt.on {{ fill: #e6e3ec; }}
.code {{ font: 15px var(--mono); fill: #d8d4e0; }}
.code.sm {{ font-size: 14px; }}
.code.log {{ font-size: 15px; fill: #e6e3ec; }}
.k {{ fill: #9cdcfe; }}
.s {{ fill: #ce9178; }}
.n {{ fill: #b5cea8; }}
.kw {{ fill: #c586c0; }}
.sys {{ fill: #dcdcaa; }}
.c {{ fill: #6a9955; }}
.ok {{ fill: #7fd18b; font-weight: 600; }}
.split {{ stroke: #3a3742; stroke-width: 1.5; }}
.strip {{ fill: #26232c; }}
.stript {{ font: 13.5px var(--mono); fill: #a9a4b3; }}
.logbox {{ fill: #15131a; stroke: #2f6b3a; }}
.stepdot {{ fill: var(--accent); }}
.stepn {{ font: 700 23px var(--display); fill: #ffffff; }}
.steplabel {{ font: 700 34px var(--display); fill: var(--fg); }}
.path {{ font: 16px var(--mono); fill: var(--muted); }}
.legendh {{ font: 700 20px var(--display); fill: #f1eef5; }}
.legendt {{ font: 16px var(--display); fill: #d8d4e0; }}
.legendt.dim {{ fill: #8d889a; font-size: 15px; }}
</style>
<div>
<div class="slide">
<svg viewBox="0 0 1920 1080" role="img" aria-label="Outputs of one run: 1 the generated microarchitecture spec JSON, 2 the Phase 1 RTL and testbenches (init_fsm.sv and init_fsm_tb.sv shown), 3 the validation report (HANDOFF.json status PASS, phase 1 lint and simulation PASS), 4 the backend GDSII layout on sky130.">
<rect width="1920" height="1080" fill="#ffffff"/>
{svg}
</svg>
</div>
<p class="hint">Screenshot the white frame (16:9) and paste it onto a slide. Excerpts are from real output files; "…" marks omitted lines.</p>
</div>
'''
with open(OUT, "w") as f:
    f.write(page)
print(OUT)
