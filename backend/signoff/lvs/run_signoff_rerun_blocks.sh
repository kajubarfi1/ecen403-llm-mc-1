set -u
cd /OpenROAD-flow-scripts/flow
S=/signoff; W=/work/rerun; P=platforms/sky130hd/cdl/sky130hd.cdl; D=$S/sky130hd_fixed.lylvs
lvs(){ scripts/klayout.sh -b -rd in_gds="$2" -rd cdl_file=$3 -rd report_file=$W/$1.lvsdb \
         -rd target_netlist=$W/$1_ext.cir -r $D > $W/$1.lvs.log 2>&1
       v=$(grep -hE "Netlists don.t match|Congratulations" $W/$1.lvs.log | tail -1); echo "RESULT $1 ${v:-NO_VERDICT}"
       klayout -b -rd lvsdb=$W/$1.lvsdb -rd b=$4 -r $S/xref_summary.rb 2>&1 | grep XREF; }
for b in cmd_gen init_fsm; do
  R=results/sky130hd/$b/base; CFG=designs/sky130hd/$b/config.mk
  echo "=== $b ==="
  [ -f $R/6_final.gds ] || { echo "RESULT $b NO_GDS"; continue; }
  echo "GDS $(date -r $R/6_final.gds '+%Y-%m-%d %H:%M')"
  # the port that the old normalize bug deleted must now exist in the netlist
  port=$([ $b = cmd_gen ] && echo ddr_addr || echo init_addr)
  echo "PORT $port occurrences in 6_final.v: $(grep -c "\b$port\b" $R/6_final.v)"
  echo "SYNTH_FRONTEND $(grep -m1 -oE 'Executing SLANG frontend|read_verilog' logs/sky130hd/$b/base/1_1_yosys_canonicalize.log 2>/dev/null)"
  if [ ! -f $R/6_final.cdl ]; then
    make -n DESIGN_CONFIG=$CFG $R/6_final.cdl > /tmp/dry_$b.txt 2>&1
    other=$(grep -E "yosys|openroad|klayout" /tmp/dry_$b.txt | grep -vc "cdl.tcl")
    [ "$other" != "0" ] && { echo "RESULT $b SKIPPED make-wants-to-rebuild"; continue; }
    make DESIGN_CONFIG=$CFG $R/6_final.cdl > $W/$b.cdl.log 2>&1 || { echo "RESULT $b CDL_FAILED"; continue; }
  fi
  python3 $S/prep_reference.py $R/6_final.cdl $R/6_final.v $P $W/$b.ref.cdl
  lvs $b $R/6_final.gds $W/$b.ref.cdl $b
  klayout -b -rd lvsdb=$W/$b.lvsdb -rd b=$b -r $S/audit_pins.rb 2>&1 | grep AUDIT
  # DRC: same invocation as ORFS's Makefile drc recipe, without the GDS re-merge
  scripts/klayout.sh -zz -rd in_gds="$R/6_final.gds" -rd report_file=$W/$b.drc.lyrdb \
    -r platforms/sky130hd/drc/sky130hd.lydrc > $W/$b.drc.log 2>&1
  echo "DRC $b items=$(grep -c '<item>' $W/$b.drc.lyrdb 2>/dev/null || echo NO_REPORT)"
  echo "--- negative controls on $b (each must FAIL) ---"
  python3 $S/negative_controls.py swap   $W/$b.ref.cdl $P $W/${b}_swap.cdl
  python3 $S/negative_controls.py delete $W/$b.ref.cdl $P $W/${b}_del.cdl
  lvs neg_${b}_swap_clk_d  $R/6_final.gds $W/${b}_swap.cdl $b
  lvs neg_${b}_delete_cell $R/6_final.gds $W/${b}_del.cdl  $b
done
