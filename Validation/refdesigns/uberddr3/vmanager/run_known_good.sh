#!/bin/bash
# vManager test: UberDDR3 + Micron DDR3 model, with the validation subsystem's
# spec-derived assertions bound at the DRAM pins and coverage on the
# controller. Output goes to stdout so vManager's scan sees it; the
# transaction lines are kept in a side file for the offline checks.
source /opt/coe/ncsu/ncsu-cdk-1.6.0.beta/ncsu.sh 2>/dev/null
TB=$HOME/uberddr3/UberDDR3/testbench
V=$HOME/vmanager_uberddr3
mkdir -p "$V/work" && cd "$V/work" || exit 9
/opt/coe/cadence/XCELIUM240/tools/bin/xrun -64bit -sv -access +r -timescale 1ps/1ps \
  -define NO_TEST_MODEL -define SIM_MODEL -incdir $TB \
  -coverage A -covoverwrite -covdut ddr3_top -covtest sva_timing_protocol \
  -top ddr3_dimm_micron_sim $TB/ddr3_dimm_micron_sim.sv $TB/ddr3.sv \
  $TB/models/IDELAYCTRL_model.v $TB/models/IDELAYE2_model.v $TB/models/IOBUF_DCIEN_model.v $TB/models/IOBUF_model.v \
  $TB/models/IOBUFDS_DCIEN_model.v $TB/models/IOBUFDS_model.v $TB/models/ISERDESE2_model.v $TB/models/OBUFDS_model.v \
  $TB/models/ODELAYE2_model.v $TB/models/OSERDESE2_model.v $TB/models/OBUF_model.v \
  $TB/../rtl/ddr3_top.v $TB/../rtl/ddr3_controller.v $TB/../rtl/ddr3_phy.v $TB/ddr3_module.sv \
  $V/cmd_gen_sva_pins.sv $V/uberddr3_pin_sva.sv $V/uberddr3_wb_monitor.sv \
  -input $V/run_exit.tcl 2>&1 | grep -av "TXN ddr_cmd\|TXN wb"
grep -ao 'TXN .*' xrun.log > "$V/txn_all.txt"
A=$(grep -c 'has failed' xrun.log); M=$(grep -cE 'ddr3.*ERROR' xrun.log); N=$(grep -c 'TXN ddr_cmd command' "$V/txn_all.txt")
echo "commands observed at the DRAM pins: $N"
echo "spec-derived assertion failures: $A   Micron model timing errors: $M"
[ "$A" = "0" ] && [ "$M" = "0" ] && [ "$N" -gt 1000 ] && echo "VALIDATION_PASS: 14 timing/protocol assertions silent over $N commands; Micron model agrees" \
  || echo "VALIDATION_FAIL: assertions=$A micron=$M commands=$N"
