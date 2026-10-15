"""Generates guide_slide.html next to this file: the most notable steps of
USAGE.md as real screenshots on a fixed 16:9 frame, to paste onto a slide.

Each step's section of USAGE.md is rendered (a small converter for the
Markdown the guide uses), screenshotted with headless Chrome at 2x, saved to
assets/guide_<n>.png and embedded in the slide. Rerun after editing USAGE.md.
Needs Google Chrome at the standard macOS path.
"""
import base64
import html
import os
import re
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
GUIDE = os.path.join(ROOT, "USAGE.md")
OUT = os.path.join(HERE, "guide_slide.html")
ASSETS = os.path.join(HERE, "assets")
CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
SHOT_W, SHOT_H = 700, 478                 # CSS px of each screenshot (captured at 2x)

# (section heading prefix, stop before this text or None, slide caption, one-line note)
STEPS = [("### 1.1", None, "Check what you need", "Python 3.10, TAMU NetID + Olympus, API key, Docker"),
         ("### 3.3", "### 3.5", "Install the tools", "Python packages, Docker and OpenROAD"),
         ("### 3.5", None, "Add your credentials", "one .env file in the repository root"),
         ("### 3.6", None, "Connect to Olympus", "a passphrase-free SSH key for lint and sim"),
         ("### 3.8", None, "Verify the setup", "a dry run reports every setting it found"),
         ("### 4.2", "4. **Review", "Start the pipeline", "python3 flow.py opens the design session")]


# ---------------------------------------------------------------- markdown subset
def inline(t):
    t = html.escape(t, quote=False)
    t = re.sub(r"`([^`]+)`", r"<code>\1</code>", t)
    t = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", t)
    t = re.sub(r"(?<![*\w])\*([^*]+)\*(?!\*)", r"<em>\1</em>", t)
    t = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r'<a>\1</a>', t)
    return t


def md(text):
    lines = text.split("\n")
    out, i, para = [], 0, []

    def flush():
        if para:
            out.append("<p>" + inline(" ".join(para)) + "</p>")
            para.clear()

    while i < len(lines):
        raw = lines[i]
        s = raw.strip()
        if s.startswith("```"):
            flush()
            indent = len(raw) - len(raw.lstrip())
            i += 1
            code = []
            while i < len(lines) and not lines[i].strip().startswith("```"):
                code.append(lines[i][indent:] if lines[i][:indent].strip() == "" else lines[i])
                i += 1
            out.append("<pre><code>" + html.escape("\n".join(code)) + "</code></pre>")
        elif m := re.match(r"(#{1,4}) (.*)", s):
            flush()
            n = len(m.group(1))
            out.append(f"<h{n}>{inline(m.group(2))}</h{n}>")
        elif s.startswith("|"):
            flush()
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r":?-+:?", c) for c in cells):
                    rows.append(cells)
                i += 1
            i -= 1
            t = "<table><thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in rows[0]) + "</tr></thead><tbody>"
            t += "".join("<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>" for r in rows[1:])
            out.append(t + "</tbody></table>")
        elif s.startswith(">"):
            flush()
            q = []
            while i < len(lines) and lines[i].strip().startswith(">"):
                q.append(lines[i].strip()[1:].strip())
                i += 1
            i -= 1
            out.append("<blockquote><p>" + inline(" ".join(q)) + "</p></blockquote>")
        elif m := re.match(r"- \[ \] (.*)", s):
            flush()
            out.append(f'<div class="check"><span class="box"></span><span>{inline(m.group(1))}</span></div>')
        elif m := re.match(r"(\d+)\. (.*)", s):
            flush()
            out.append(f'<div class="li"><span class="num">{m.group(1)}.</span><span>{inline(m.group(2))}</span></div>')
        elif s.startswith("- "):
            flush()
            out.append(f'<div class="li"><span class="num">•</span><span>{inline(s[2:])}</span></div>')
        elif s == "" or s == "---":
            flush()
        elif raw.startswith("   ") and out and out[-1].startswith('<div class="li">') and not para:
            # continuation of a list item's text
            out[-1] = out[-1][:-len("</span></div>")] + " " + inline(s) + "</span></div>"
        else:
            para.append(s)
        i += 1
    flush()
    return "\n".join(out)


def section(text, head, stop):
    """From `head` to the next heading of the same or higher level (headings
    inside code fences do not count), or to `stop` when given."""
    rest = text[text.index(head):]
    if stop:
        return rest[:rest.index(stop)].strip()
    level, pos, fenced = len(head.split(" ")[0]), 0, False
    for line in rest.split("\n"):
        if line.strip().startswith("```"):
            fenced = not fenced
        elif pos and not fenced and re.match(r"#{1,%d} " % level, line):
            return rest[:pos].strip()
        pos += len(line) + 1
    return rest.strip()


PAGE_CSS = f"""
html,body{{margin:0;background:#fff}}
body{{width:{SHOT_W}px;height:{SHOT_H}px;overflow:hidden;box-sizing:border-box;padding:26px 34px;
     font:17px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;color:#1f2328}}
h3{{font-size:23px;margin:0 0 12px;padding-bottom:8px;border-bottom:1px solid #d1d9e0}}
h2{{font-size:24px;margin:0 0 12px}}
p{{margin:0 0 12px}}
code{{font:14.5px ui-monospace,SFMono-Regular,Menlo,monospace;background:#eff1f3;padding:2px 5px;border-radius:5px}}
pre{{background:#f6f8fa;border-radius:7px;padding:12px 14px;margin:0 0 12px;overflow:hidden}}
pre code{{background:none;padding:0;font-size:14.5px;line-height:1.5}}
table{{border-collapse:collapse;margin:0 0 12px;font-size:14px}}
th,td{{border:1px solid #d1d9e0;padding:5px 10px;text-align:left}}
th{{background:#f6f8fa}}
blockquote{{margin:0 0 12px;padding:2px 14px;border-left:4px solid #d1d9e0;color:#59636e}}
.check,.li{{display:flex;gap:10px;margin:0 0 8px;align-items:baseline}}
.box{{flex:none;width:14px;height:14px;border:1.5px solid #8c959f;border-radius:3px;transform:translateY(2px)}}
.num{{flex:none;min-width:18px;color:#59636e;font-weight:600}}
a{{color:#0969da}}
.fade{{position:fixed;left:0;right:0;bottom:0;height:70px;background:linear-gradient(rgba(255,255,255,0),#fff)}}
"""


def capture(n, body_html):
    os.makedirs(ASSETS, exist_ok=True)
    png = os.path.join(ASSETS, f"guide_{n}.png")
    with tempfile.NamedTemporaryFile("w", suffix=".html", delete=False) as f:
        f.write(f"<!doctype html><meta charset='utf-8'><style>{PAGE_CSS}</style>{body_html}<div class='fade'></div>")
        src = f.name
    subprocess.run([CHROME, "--headless=new", "--disable-gpu", "--hide-scrollbars",
                    "--force-device-scale-factor=2", f"--window-size={SHOT_W},{SHOT_H}",
                    f"--screenshot={png}", "file://" + src],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    os.unlink(src)
    return png


# ---------------------------------------------------------------- slide
def build():
    text = open(GUIDE).read()
    shots = []
    for n, (head, stop, cap, note) in enumerate(STEPS, 1):
        png = capture(n, md(section(text, head, stop)))
        with open(png, "rb") as f:
            shots.append(("data:image/png;base64," + base64.b64encode(f.read()).decode(), cap, note))

    # 3 x 2 grid of browser-framed screenshots
    p = []
    cols, cw, gx, x0 = 3, 576, 36, 60
    iw = cw - 2                                   # image width inside the frame
    ih = iw * SHOT_H / SHOT_W
    fh = 30 + ih                                  # frame height (bar + image)
    rows_y = [92, 92 + fh + 132]
    for i, (uri, cap, note) in enumerate(shots):
        r, c = divmod(i, cols)
        x, y = x0 + c * (cw + gx), rows_y[r]
        n = i + 1
        p.append(f'<circle cx="{x+19}" cy="{y-46}" r="19" class="dot"/>'
                 f'<text x="{x+19}" y="{y-38.5}" text-anchor="middle" class="dotn">{n}</text>'
                 f'<text x="{x+50}" y="{y-37}" class="cap">{html.escape(cap)}</text>'
                 f'<text x="{x+50}" y="{y-13}" class="note">{html.escape(note)}</text>')
        p.append(f'<rect x="{x}" y="{y}" width="{cw}" height="{fh:.1f}" rx="9" class="frame"/>')
        p.append(f'<path d="M{x},{y+30} v-21 a9,9 0 0 1 9,-9 h{cw-18} a9,9 0 0 1 9,9 v21 z" class="bar"/>')
        p.append(f'<circle cx="{x+16}" cy="{y+15}" r="4.5" fill="#ff5f57"/><circle cx="{x+30}" cy="{y+15}" r="4.5" fill="#febc2e"/>'
                 f'<circle cx="{x+44}" cy="{y+15}" r="4.5" fill="#28c840"/>')
        p.append(f'<text x="{x+cw/2}" y="{y+20}" text-anchor="middle" class="url">USAGE.md</text>')
        p.append(f'<image href="{uri}" x="{x+1}" y="{y+30}" width="{iw}" height="{ih:.1f}"/>')
        if c < cols - 1:
            ay = y + 30 + ih / 2
            p.append(f'<path d="M{x+cw+8},{ay:.1f} h{gx-20}" class="arrow" marker-end="url(#ah)"/>')

    svg = "\n".join(p)
    page = f'''<title>LLM-MC User Guide Slide</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&family=IBM+Plex+Sans:wght@400;600;700&display=swap">
<style>
/* Layout: a fixed 16:9 frame (1920x1080 viewBox): six numbered screenshots of USAGE.md in a 3x2 grid, read left to right.
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
.dot {{ fill: var(--accent); }}
.dotn {{ font: 700 21px var(--display); fill: #ffffff; }}
.cap {{ font: 700 28px var(--display); fill: var(--fg); }}
.note {{ font: 18px var(--display); fill: var(--muted); }}
.frame {{ fill: #ffffff; stroke: #cfc6c7; stroke-width: 1.5; }}
.bar {{ fill: #f1ecec; }}
.url {{ font: 13px var(--mono); fill: var(--muted); }}
.arrow {{ stroke: var(--accent); stroke-width: 3; fill: none; }}
#ah path {{ fill: var(--accent); }}
</style>
<div>
<div class="slide">
<svg viewBox="0 0 1920 1080" role="img" aria-label="Six steps from the Getting Started guide, USAGE.md: 1 check what you need, 2 install the tools, 3 add your credentials in .env, 4 connect to Olympus with an SSH key, 5 verify the setup with a dry run, 6 start the pipeline with python3 flow.py.">
<defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="5" markerHeight="5" orient="auto"><path d="M0,0 L10,5 L0,10 z"/></marker></defs>
<rect width="1920" height="1080" fill="#ffffff"/>
{svg}
</svg>
</div>
<p class="hint">Screenshot the white frame (16:9) and paste it onto a slide. Each panel is a real render of the matching section of USAGE.md.</p>
</div>
'''
    with open(OUT, "w") as f:
        f.write(page)
    print(OUT)


if __name__ == "__main__":
    build()
