import re, sys
kind, src, plat, out = sys.argv[1:5]
lines = open(src).read().splitlines()
pins = {l.split()[1].lower(): l.split()[2:] for l in re.sub(r"\n\+", " ", open(plat, errors="ignore").read()).splitlines()
        if l.upper().startswith(".SUBCKT")}
def swap(match, pa, pb):
    for i, l in enumerate(lines):
        t = l.split()
        if l.startswith("X") and match(t[-1].lower()):
            p = pins[t[-1].lower()]; nets = t[1:-1]; a, b = p.index(pa), p.index(pb)
            if nets[a] == nets[b]: continue           # same net on both pins: swap would be a no-op
            nets[a], nets[b] = nets[b], nets[a]; lines[i] = " ".join([t[0]] + nets + [t[-1]])
            print(f"MUT swap {pa}<->{pb} on {t[0]} ({t[-1]})"); return True
    return False
done = False
if kind == "swap":   done = swap(lambda c: {"CLK", "D"} <= set(pins.get(c, [])), "CLK", "D")
elif kind == "swapcell": done = swap(lambda c: c == sys.argv[5], sys.argv[6], sys.argv[7])
elif kind == "delete":
    for i, l in enumerate(lines):
        if l.startswith("X"): print(f"MUT delete {l.split()[0]} ({l.split()[-1]})"); del lines[i]; done = True; break
if not done: print(f"MUT {kind} NOT APPLIED")
open(out, "w").write("\n".join(lines) + "\n")
