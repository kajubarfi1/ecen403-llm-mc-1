#!/usr/bin/env bash
set -euo pipefail

cd C:\Users\dawca\OpenROAD-flow-scripts\flow
make -j1 DESIGN_CONFIG=designs/sky130hd/ddr3_controller/config.mk
