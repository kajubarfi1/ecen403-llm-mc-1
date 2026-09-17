set -u
cd /OpenROAD-flow-scripts/flow
W=/work/final6; P=platforms/sky130hd/cdl/sky130hd.cdl; D=$W/sky130hd_fixed.lylvs
run(){ scripts/klayout.sh -b -rd in_gds="$2" -rd cdl_file=$3 -rd report_file=$W/$1.lvsdb \
         -rd target_netlist=$W/$1_ext.cir -r $D > $W/$1.log 2>&1
       v=$(grep -hE "Netlists don.t match|Congratulations" $W/$1.log | tail -1); echo "RESULT $1 ${v:-NO_VERDICT}"
       klayout -b -rd lvsdb=$W/$1.lvsdb -rd b=$4 -r $W/xref.rb 2>&1 | grep XREF; }
for b in addr_decoder bank_tracker calibration cmd_queue config_regs data_path refresh_ctrl scheduler wb_port; do
  R=results/sky130hd/$b/base
  python3 $W/filt4.py $R/6_final.cdl $R/6_final.v $P $W/$b.ref.cdl
  bb=$(grep -cE "sky130_fd_sc_hd__(a2111oi_2|a211oi_4|o211ai_4|a21oi_2)$" $W/$b.ref.cdl)
  echo "BLACKBOXED_INSTANCES $b $bb"
  run $b $R/6_final.gds $W/$b.ref.cdl $b
  klayout -b -rd lvsdb=$W/$b.lvsdb -rd b=$b -r $W/audit.rb 2>&1 | grep AUDIT
done
echo "===== NEGATIVE CONTROLS (each must FAIL) ====="
for b in config_regs cmd_queue; do
  R=results/sky130hd/$b/base
  python3 $W/mutate.py swap   $W/$b.ref.cdl $P $W/${b}_swap.cdl
  python3 $W/mutate.py delete $W/$b.ref.cdl $P $W/${b}_del.cdl
  run neg_${b}_swap_clk_d  $R/6_final.gds $W/${b}_swap.cdl $b
  run neg_${b}_delete_cell $R/6_final.gds $W/${b}_del.cdl  $b
done
R=results/sky130hd/scheduler/base
python3 $W/mutate.py swapcell $W/scheduler.ref.cdl $P $W/sch_bb.cdl sky130_fd_sc_hd__a21oi_2 A1 B1
run neg_scheduler_blackbox_pin $R/6_final.gds $W/sch_bb.cdl scheduler
