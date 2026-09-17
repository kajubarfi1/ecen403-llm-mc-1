"""Build the LVS reference netlist for one block.

Design side — restore what OpenROAD's CDL writer loses, remove what has no devices:
  taps (no devices), antenna diodes (deck has no diode extraction),
  conb_1 ties ('short' => LO==VGND, HI==VPWR: nets joined), assign feedthroughs (nets joined).
Library side — include only the .SUBCKT definitions the design actually instantiates,
  copied verbatim from the vendor CDL. Unused library cells are not part of the design.
usage: filt3.py <6_final.cdl> <6_final.v> <platform.cdl> <out.cdl>
"""
import re, sys
cdl, v, plat, out_p = sys.argv[1:5]
J = lambda p: re.sub(r"\n\+", " ", open(p, errors="ignore").read()).splitlines()
alias, n = {}, {"taps": 0, "diodes": 0, "ties": 0, "feedthroughs": 0, "pin_aliases": 0}
ident = lambda s: s.strip().lstrip("\\").replace(" ", "")
top_pins = set(next((l.split()[2:] for l in J(cdl) if l.startswith(".SUBCKT")), []))
for m in re.finditer(r"^\s*assign\s+([^=]+?)\s*=\s*([^;]+);", open(v, errors="ignore").read(), re.M):
    lhs, rhs = ident(m.group(1)), ident(m.group(2))
    if not re.fullmatch(r"[A-Za-z_][\w$]*(\[\d+\])?", rhs): continue
    if lhs in top_pins and rhs in top_pins: alias[lhs] = rhs; n["feedthroughs"] += 1   # pin-to-pin wire
    elif lhs in top_pins: alias[rhs] = lhs; n["pin_aliases"] += 1                      # keep the pin's name
    else: alias[lhs] = rhs; n["pin_aliases"] += 1
kept = []
for l in J(cdl):
    if l.startswith("X"):
        t = l.split(); cell = t[-1].lower(); nets = t[1:-1]
        if cell.endswith("tapvpwrvgnd_1"): n["taps"] += 1; continue
        if cell.startswith("sky130_fd_sc_hd__diode_"): n["diodes"] += 1; continue
        if cell == "sky130_fd_sc_hd__conb_1":
            alias[nets[5]] = nets[0]; alias[nets[4]] = nets[3]; n["ties"] += 1; continue
    kept.append(l)
def res(x):
    seen = set()
    while x in alias and x not in seen: seen.add(x); x = alias[x]
    return x
design = []
for l in kept:
    t = l.split()
    if l.startswith(".SUBCKT"):
        pins, s = [], set()
        for p in t[2:]:
            r = res(p)
            if r not in s: s.add(r); pins.append(r)
        l = " ".join(t[:2] + pins)
    elif l.startswith("X"):
        l = " ".join([t[0]] + [res(x) for x in t[1:-1]] + [t[-1]])
    design.append(l)
# library: verbatim blocks for referenced cells (transitively)
blocks, cur = {}, None
for l in open(plat, errors="ignore").read().splitlines():
    if l.upper().startswith(".SUBCKT"): cur = l.split()[1].lower(); blocks[cur] = [l]; continue
    if cur is not None:
        blocks[cur].append(l)
        if l.upper().startswith(".ENDS"): cur = None
need = {l.split()[-1].lower() for l in design if l.startswith("X")}
todo, used = list(need), set()
while todo:
    c = todo.pop()
    if c in used or c not in blocks: continue
    used.add(c)
    todo += [x.split()[-1].lower() for x in blocks[c] if x.startswith("X") and "/" not in x]
missing = sorted(need - set(blocks))
lib = [ln for c in sorted(used) for ln in blocks[c]]
open(out_p, "w").write("\n".join(design + lib) + "\n")
print("PREP " + " ".join(f"{k}={v}" for k, v in n.items()) + f" lib_cells={len(used)} missing_defs={missing}")
