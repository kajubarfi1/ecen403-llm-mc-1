#!/usr/bin/env python3
"""gui/flow_gui.py: the status the progress page polls, read from a run the
way flow.py and ORFS leave it. A demo run is driven to completion on a fast
clock; the parsers are checked on log lines in the shapes ORFS prints."""

import os
import shutil
import sys
import tempfile
import threading
import time
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "gui"))
import demo_run  # noqa: E402
import flow_gui  # noqa: E402


class Parsers(unittest.TestCase):
    def test_orfs_stage_names(self):
        cases = {"1_2_yosys.log": "synth", "2_4_floorplan_pdn.log": "floorplan",
                 "3_3_place_gp.tmp.log": "place", "4_1_cts.log": "cts", "5_1_grt.log": "grt",
                 "5_2_route.log": "route", "5_3_fillcell.log": "route", "6_1_merge.log": "finish",
                 "6_report.log": "finish", "notes.txt": None}
        for name, want in cases.items():
            self.assertEqual(flow_gui.orfs_stage_of(name), want, name)

    def test_placement_overflow(self):
        frac, detail = flow_gui.parse_place("[NESTEROV] Iter:  100 overflow: 0.550 HPWL: 1\n")
        self.assertAlmostEqual(frac, 0.5, places=2)
        self.assertIn("0.550", detail)
        frac, _ = flow_gui.parse_place("     350 |   0.1000 |  1.2e+09 |\n")   # newer table form
        self.assertAlmostEqual(frac, 1.0, places=2)

    def test_route_iterations(self):
        txt = ("[INFO DRT-0195] Start 0th optimization iteration.\n"
               "    Completing 50% with 812 violations.\n")
        frac, detail, v = flow_gui.parse_route(txt)
        self.assertAlmostEqual(frac, 0.325, places=3)
        self.assertEqual(v, 812)
        frac2, _, _ = flow_gui.parse_route(txt + "[INFO DRT-0195] Start 2nd optimization iteration.\n"
                                           "    Completing 100% with 3 violations.\n")
        self.assertGreater(frac2, 0.65)
        _, _, v = flow_gui.parse_route("Start 4th optimization iteration.\nNumber of violations = 0.\n")
        self.assertEqual(v, 0)

    def test_run_folder_name_is_not_spec_synthesis(self):
        # runs named after the golden spec contain "microarchitectures"
        body = "$ python3 backend/agents/pipeline.py --bundle_dir runs/x-llmmc_microarchitectures/drop/TOPRTL"
        self.assertEqual(flow_gui.stage_of_cmd(body), "backend")


class DemoRun(unittest.TestCase):
    def test_whole_run(self):
        tmp = tempfile.mkdtemp()
        try:
            demo = demo_run.Demo(minutes=0.25, root=tmp)
            t = threading.Thread(target=demo.run, daemon=True)
            t.start()
            w = flow_gui.Watcher(demo.runs_root, run=demo.run_dir, orfs_dir=demo.orfs_dir)
            seen_steps, peak = set(), 0.0
            deadline = time.time() + 60
            while t.is_alive() and time.time() < deadline:
                st = w.status()
                bk = st["backend"]
                if bk["current_step"]:
                    seen_steps.add(bk["current_step"])
                self.assertGreaterEqual(bk["progress"] + 1e-9, peak * 0.999 if bk["orfs"]["pass"] <= 1 else 0)
                peak = max(peak, bk["progress"])
                time.sleep(0.05)
            t.join(5)
            st = w.status()
            self.assertEqual(st["run"]["status"], "done")
            self.assertTrue(all(s["state"] == "pass" for s in st["stages"]), st["stages"])
            bk = st["backend"]
            self.assertEqual(bk["result"], "pass")
            self.assertEqual(bk["progress"], 1.0)
            self.assertTrue(all(s["state"] == "done" for s in bk["steps"]), bk["steps"])
            self.assertEqual(bk["orfs"]["design"], "ddr3_controller")
            self.assertEqual(bk["orfs"]["cells"], 23587)
            self.assertEqual(bk["orfs"]["violations"], 0)
            self.assertEqual(bk["report"]["lvs_status"], "PASS")
            # the slow steps were each seen running, read from ORFS's own logs
            self.assertTrue({"place", "route"} <= seen_steps, seen_steps)
            # the demo's own fix-loop (data_path's sim gate, then Validation
            # sending wb_port back) resolved and the final state is clean
            fe, val = st["frontend"], st["validation"]
            self.assertIsNone(fe["active_fix"])
            self.assertTrue(all(p["result"] == "pass" for p in fe["phases"]), fe["phases"])
            outcomes = {(f["module"], f["outcome"]) for f in fe["fixloop"]}
            self.assertIn(("data_path", "fixed"), outcomes)
            self.assertIn(("wb_port", "fixed"), outcomes)
            wb_fix = next(f for f in fe["fixloop"] if f["module"] == "wb_port")
            self.assertEqual(wb_fix["trigger"]["kind"], "validation")
            self.assertEqual(val["result"], "pass")
            self.assertEqual(val["failed_modules"], [])
            self.assertEqual(len(val["paths"]), 20)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    def test_backend_without_orfs_logs_is_estimated(self):
        tmp = tempfile.mkdtemp()
        try:
            demo = demo_run.Demo(minutes=0.25, root=tmp)
            demo.run()
            w = flow_gui.Watcher(demo.runs_root, run=demo.run_dir, orfs_dir=None)
            w.orfs_dir = None
            bk = w.status()["backend"]
            self.assertTrue(bk["orfs"]["estimated"])
            self.assertEqual(bk["result"], "pass")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
