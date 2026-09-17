set -u
cd /OpenROAD-flow-scripts/flow
W=/work/drc
for b in addr_decoder bank_tracker calibration cmd_queue config_regs data_path refresh_ctrl scheduler wb_port; do
  R=results/sky130hd/$b/base
  t0=$(date +%s)
  # same invocation as ORFS's Makefile drc recipe, minus the GDS re-merge
  scripts/klayout.sh -zz -rd in_gds="$R/6_final.gds" -rd report_file=$W/$b.lyrdb \
    -r platforms/sky130hd/drc/sky130hd.lydrc > $W/$b.log 2>&1
  python3 - "$W/$b.lyrdb" "$b" "$(( $(date +%s)-t0 ))" <<'PY'
import sys, collections, xml.etree.ElementTree as ET
p, b, t = sys.argv[1:4]
try:
    root = ET.parse(p).getroot()
except Exception as e:
    print(f"DRC {b} NO_REPORT ({e})"); sys.exit()
cats = collections.Counter((it.findtext("category") or "?").strip("'") for it in root.iter("item"))
print(f"DRC {b} {t}s items={sum(cats.values())}" + ("" if not cats else "  " + ", ".join(f"{k}={v}" for k, v in cats.most_common(6))))
PY
done
