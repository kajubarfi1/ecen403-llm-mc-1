#!/bin/bash
# vManager test: an offline validation check on the transaction log the
# simulation test wrote. $1 = integrity | path19 | path20 | path19_2nd | path20_2nd
V=$HOME/vmanager_uberddr3; R=$V/repo; L=$V/txn_all.txt
[ -s "$L" ] || { echo "VALIDATION_FAIL: no transaction log; run sva_timing_protocol first"; exit 1; }
cd "$R" || exit 9
# The Cadence environment puts its own libraries ahead of the system ones and
# breaks the default python3; run a system interpreter with a clean loader path.
PY="env -u LD_LIBRARY_PATH -u PYTHONHOME -u PYTHONPATH /usr/bin/python3.11"
P=Validation/predictors
case "$1" in
  integrity)  $PY Validation/refdesigns/uberddr3/check_data_integrity.py --log "$L" \
                --spec builds/uberddr3_ddr3-667_x16_2lane_1rank/microarch_spec.json | tee /tmp/vmu_$$.txt
              grep -q "verdict: PASS" /tmp/vmu_$$.txt && echo "VALIDATION_PASS: every read returned what was written; every host request matched a CAS at the pins" \
                || echo "VALIDATION_FAIL: data integrity"; rm -f /tmp/vmu_$$.txt ;;
  path19)     $PY Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log "$L" --models $P/path_19_row_conflict_checker.py ;;
  path20)     $PY Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log "$L" --models $P/path_20_refresh_preempt_checker.py ;;
  path19_2nd) $PY Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log "$L" --models $P/second_opinion/path_19_row_conflict_checker.py ;;
  path20_2nd) $PY Validation/refdesigns/uberddr3/path_checkers_on_uberddr3.py --log "$L" --models $P/second_opinion/path_20_refresh_preempt_checker.py ;;
  *) echo "VALIDATION_FAIL: unknown check $1"; exit 2 ;;
esac
