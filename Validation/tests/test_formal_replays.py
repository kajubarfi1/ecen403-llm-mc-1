#!/usr/bin/env python3
"""validate_drop re-proves a formally proved path when no JasperGold report
applies to the design under judgement, with the options of its last report
(2026-10-20)."""

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tools"))
sys.path.insert(0, os.path.join(HERE, "..", "structural"))
import validate_drop as VD  # noqa: E402
import rtl_drop as RD  # noqa: E402


class TestFormalReplays(unittest.TestCase):

    def _rep(self, d, name, **kw):
        rep = {"path": "path_01_write_cmd", "drop": "old", "design_id": "olddesign",
               "max_trace_length": 200, "results": [], "abstractions": []}
        rep.update(kw)
        with open(os.path.join(d, name), "w") as f:
            json.dump(rep, f)

    def test_stale_report_is_replayed_with_its_options(self):
        d = tempfile.mkdtemp()
        self._rep(d, "jg_path_01_write_cmd_old.json", max_trace_length=300)
        self._rep(d, "jg_path_08_init_to_cal_old_abs.json", path="path_08_init_to_cal",
                  abstractions=[{"stopat": "u_init_fsm.wait_cnt"}], max_trace_length=400)
        self._rep(d, "jg_cmd_path_legacy.json", path=None)
        todo = VD.formal_replays("newdrop", reports_dir=d)
        self.assertEqual(todo, [("path_01_write_cmd", {"trace": 300, "stopat": [], "assume": [], "sva_param": []}),
                                ("path_08_init_to_cal", {"trace": 400, "stopat": ["u_init_fsm.wait_cnt"],
                                                         "assume": [], "sva_param": []})])

    def test_an_assumed_configuration_is_its_own_recipe(self):
        d = tempfile.mkdtemp()
        self._rep(d, "jg_path_01_write_cmd_old_abs.json", max_trace_length=300,
                  abstractions=[{"stopat": "u_config_regs.cfg_tREFI_nCK"},
                                {"assume": "u_config_regs.cfg_tREFI_nCK == 24'd516"},
                                {"sva_param": "TIMING_012_BOUND=258"}])
        todo = VD.formal_replays("newdrop", reports_dir=d)
        self.assertEqual(todo, [("path_01_write_cmd", {"trace": 300, "stopat": ["u_config_regs.cfg_tREFI_nCK"],
                                                       "assume": ["u_config_regs.cfg_tREFI_nCK == 24'd516"],
                                                       "sva_param": ["TIMING_012_BOUND=258"]})])

    def test_a_report_for_this_drop_or_design_needs_no_replay(self):
        d = tempfile.mkdtemp()
        self._rep(d, "jg_path_01_write_cmd_old.json")
        self._rep(d, "jg_path_01_write_cmd_new.json", drop="newdrop")
        self.assertEqual(VD.formal_replays("newdrop", reports_dir=d), [])
        d2 = tempfile.mkdtemp()
        self._rep(d2, "jg_path_01_write_cmd_x.json", drop="x", design_id=RD.design_id())
        self.assertEqual(VD.formal_replays("newdrop", reports_dir=d2), [])

    def test_no_history_means_nothing_to_replay(self):
        self.assertEqual(VD.formal_replays("newdrop", reports_dir=tempfile.mkdtemp()), [])


if __name__ == "__main__":
    unittest.main()
