#!/usr/bin/env python3
"""repair_node's guards, driven by the two failures of 2026-11-12.

Both runs died in ORFS, not in the design, and both times the repair agent
answered with a config.mk edit that made things worse: DESIGN_NICKNAME =
TOPRTL after the SDC copy race (results move to a directory runner_node
never reads), then FLOORPLAN_SDC pointed at the synthesis SDC and
DESIGN_NAME re-set to its own value after the floorplan rule bug. All three
were stripped out by hand (Validation SEMESTER_PLAN, 2026-11-12).

What is pinned here: a toolchain fault never reaches the classifier, no
variable outside REPAIR_ALLOWED_MK_VARS is ever written to config.mk, and
the repairs that were always legitimate still apply unchanged.
"""

import importlib.util
import os
import sys
import tempfile
import types
import unittest
from pathlib import Path

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


def _load_pipeline():
    """Import backend/agents/pipeline.py. langgraph and typing_extensions are
    needed to build the graph and to declare PipelineState, never to call a
    node, so stub them when they are not installed -- this test then runs
    anywhere flow.py's own tests do, agent dependencies or not."""
    import typing
    stubs = {
        "langgraph": {},
        "langgraph.graph": {"StateGraph": lambda *_a, **_k: None, "END": object()},
        "langgraph.graph.message": {"add_messages": lambda *_a, **_k: None},
        "typing_extensions": {"TypedDict": typing.TypedDict, "Annotated": typing.Annotated,
                              "Literal": typing.Literal},
    }
    for name, attrs in stubs.items():
        try:
            __import__(name)
            continue
        except ImportError:
            pass
        mod = types.ModuleType(name)
        for a, v in attrs.items():
            setattr(mod, a, v)
        sys.modules[name] = mod
    sys.path.insert(0, ROOT)
    spec = importlib.util.spec_from_file_location(
        "backend_pipeline", os.path.join(ROOT, "backend", "agents", "pipeline.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


P = _load_pipeline()


# the two logs, as ORFS wrote them
LOG_CP_RACE = """
[INFO] Running synthesis
cp results/sky130hd/ddr3_controller/base/1_synth.sdc \\
   results/sky130hd/ddr3_controller/base/1_2_yosys.sdc
cp: cannot create regular file 'results/sky130hd/ddr3_controller/base/1_2_yosys.sdc': No such file or directory
make: *** [Makefile:287: results/sky130hd/ddr3_controller/base/1_2_yosys.sdc] Error 1
"""

LOG_FLOORPLAN_RULE = """
[INFO] Elapsed time: 1:08.3[h:]min:sec. CPU time: user 66.9 sys 1.2 (99%).
make: *** No rule to make target 'results/sky130hd/ddr3_controller/base/2_1_floorplan.sdc',
 needed by 'results/sky130hd/ddr3_controller/base/2_floorplan.sdc'.  Stop.
"""

LOG_CONGESTION = """
[WARNING GRT-0101] Global routing finished with congestion.
[ERROR DRT-0255] Routing congestion too high to converge.
"""


class RepairGuards(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="repairguard-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.design, self.platform = "ddr3_controller", "sky130hd"
        d = Path(self.tmp) / "flow" / "designs" / self.platform / self.design
        d.mkdir(parents=True)
        self.config_mk = d / "config.mk"
        self.config_mk.write_text(
            "export DESIGN_NAME = ddr3_controller\n"
            "export PLATFORM    = sky130hd\n"
            "export PLACE_DENSITY = 0.60\n", encoding="utf-8")
        self.log = Path(self.tmp) / "run.log"
        self.calls = []
        # a key must be present, or the node takes the heuristic path and
        # never exercises the classifier these guards wrap
        self._key = os.environ.get("ANTHROPIC_API_KEY")
        os.environ["ANTHROPIC_API_KEY"] = "test-key-not-used"
        self.addCleanup(self._restore_key)
        self._real_call = P.call_claude
        self.addCleanup(lambda: setattr(P, "call_claude", self._real_call))

    def _restore_key(self):
        if self._key is None:
            os.environ.pop("ANTHROPIC_API_KEY", None)
        else:
            os.environ["ANTHROPIC_API_KEY"] = self._key

    def _answer(self, payload):
        """Make the classifier return `payload`, recording that it was asked."""
        def fake(api_key, model, system, user, **kw):
            self.calls.append({"system": system, "user": user})
            return payload
        P.call_claude = fake

    def _run(self, log_text, exit_code=2):
        self.log.write_text(log_text, encoding="utf-8")
        return P.repair_node({
            "runner_result": {"design_name": self.design, "orfs_dir": self.tmp,
                              "platform": self.platform, "log_path": str(self.log),
                              "exit_code": exit_code},
            "packager_report": {},
        })

    def mk(self):
        return self.config_mk.read_text(encoding="utf-8")

    # -- toolchain faults never reach the classifier --------------------------

    def test_cp_into_missing_results_dir_is_not_a_design_error(self):
        """2026-11-12 morning: the SDC copy raced synth.sh's mkdir and lost."""
        self._answer('{"error_class":"timing_too_tight","fixable":true,'
                     '"fix_description":"relax","config_mk_changes":{"DESIGN_NICKNAME":"TOPRTL"}}')
        out = self._run(LOG_CP_RACE)
        self.assertEqual([], self.calls, "classifier was asked about a toolchain fault")
        self.assertEqual("FAIL", out["pipeline_status"])
        self.assertEqual("infrastructure_toolchain", out["repair_history"][-1]["error_class"])
        self.assertFalse(out["repair_history"][-1]["fixable"])
        self.assertNotIn("DESIGN_NICKNAME", self.mk())

    def test_missing_make_rule_is_not_a_design_error(self):
        """2026-11-12 evening: ORFS f34d4d9 names the wrong prerequisite."""
        self._answer('{"error_class":"routing_congestion","fixable":true,'
                     '"fix_description":"density","config_mk_changes":{"FLOORPLAN_SDC":"1_synth.sdc"}}')
        out = self._run(LOG_FLOORPLAN_RULE)
        self.assertEqual([], self.calls)
        self.assertEqual("FAIL", out["pipeline_status"])
        self.assertNotIn("FLOORPLAN_SDC", self.mk())

    def test_toolchain_fault_does_not_retry_the_build(self):
        self._answer('{"error_class":"unknown","fixable":false,"config_mk_changes":{}}')
        out = self._run(LOG_FLOORPLAN_RULE)
        self.assertNotEqual("REPAIR_RETRY", out["pipeline_status"])
        self.assertEqual("reporter", P.route_after_repair(out))

    # -- the allowlist --------------------------------------------------------

    def test_packager_owned_variable_is_refused(self):
        """DESIGN_NICKNAME is what the agent actually reached for."""
        self._answer('{"error_class":"synthesis_error","fixable":true,'
                     '"fix_description":"nickname","config_mk_changes":{"DESIGN_NICKNAME":"TOPRTL"}}')
        out = self._run(LOG_CONGESTION)
        self.assertNotIn("DESIGN_NICKNAME", self.mk())
        self.assertEqual({"DESIGN_NICKNAME": "TOPRTL"}, out["repair_history"][-1]["fix_rejected"])
        self.assertFalse(out["repair_history"][-1]["fixable"],
                         "a proposal with nothing left to apply is not fixable")
        self.assertNotEqual("REPAIR_RETRY", out["pipeline_status"])

    def test_resetting_design_name_to_itself_is_refused(self):
        self._answer('{"error_class":"synthesis_error","fixable":true,'
                     '"fix_description":"name","config_mk_changes":{"DESIGN_NAME":"ddr3_controller"}}')
        self._run(LOG_CONGESTION)
        self.assertEqual(1, self.mk().count("DESIGN_NAME"),
                         "DESIGN_NAME was rewritten or appended a second time")

    def test_mixed_proposal_keeps_only_what_repair_owns(self):
        self._answer('{"error_class":"routing_congestion","fixable":true,'
                     '"fix_description":"mixed","config_mk_changes":'
                     '{"PLACE_DENSITY":"0.50","FLOORPLAN_SDC":"1_synth.sdc"}}')
        out = self._run(LOG_CONGESTION)
        mk = self.mk()
        self.assertIn("export PLACE_DENSITY = 0.50", mk)
        self.assertNotIn("FLOORPLAN_SDC", mk)
        self.assertEqual({"PLACE_DENSITY": "0.50"}, out["repair_history"][-1]["fix_applied"])
        self.assertTrue(out["repair_history"][-1]["fixable"])

    def test_rejected_keys_are_carried_into_the_next_prompt(self):
        self._answer('{"error_class":"synthesis_error","fixable":true,'
                     '"fix_description":"x","config_mk_changes":{"DESIGN_NICKNAME":"TOPRTL"}}')
        out = self._run(LOG_CONGESTION)
        self.calls.clear()
        P.repair_node({
            "runner_result": {"design_name": self.design, "orfs_dir": self.tmp,
                              "platform": self.platform, "log_path": str(self.log),
                              "exit_code": 2},
            "packager_report": {},
            "repair_history": out["repair_history"],
            "repair_iteration": out["repair_iteration"],
        })
        self.assertIn("DESIGN_NICKNAME", self.calls[0]["user"],
                      "the second iteration cannot see that the first was discarded")

    def test_prompt_names_the_allowed_variables(self):
        self._answer('{"error_class":"unknown","fixable":false,"config_mk_changes":{}}')
        self._run(LOG_CONGESTION)
        system = self.calls[0]["system"]
        for var in P.REPAIR_ALLOWED_MK_VARS:
            self.assertIn(var, system)
        self.assertIn("DESIGN_NICKNAME", system, "the prompt should name what is off-limits")

    # -- the repairs that were always legitimate ------------------------------

    def test_congestion_fix_still_applies(self):
        self._answer('{"error_class":"routing_congestion","fixable":true,'
                     '"fix_description":"density","config_mk_changes":{"PLACE_DENSITY":"0.50"}}')
        out = self._run(LOG_CONGESTION)
        self.assertIn("export PLACE_DENSITY = 0.50", self.mk())
        self.assertEqual("REPAIR_RETRY", out["pipeline_status"])
        self.assertEqual("runner", P.route_after_repair(out))

    def test_pdn_fix_still_applies(self):
        self._answer('{"error_class":"pdn_too_small","fixable":true,'
                     '"fix_description":"pdn","config_mk_changes":'
                     '{"CORE_UTILIZATION":"15","CORE_MARGIN":"15"}}')
        self._run("[ERROR PDN-0185] Insufficient width")
        mk = self.mk()
        self.assertIn("export CORE_UTILIZATION = 15", mk)
        self.assertIn("export CORE_MARGIN = 15", mk)

    def test_heuristic_fallback_stays_inside_the_allowlist(self):
        """Every fix _heuristic_repair can propose must survive the filter."""
        for log in ("syntax error near unexpected '['",
                    "[ERROR PDN-0185] Insufficient width",
                    "DRC violation: congestion"):
            _cls, fixable, _desc, changes = P._heuristic_repair(log)
            self.assertTrue(fixable)
            self.assertTrue(set(changes) <= set(P.REPAIR_ALLOWED_MK_VARS),
                            f"heuristic proposes {set(changes) - set(P.REPAIR_ALLOWED_MK_VARS)}")

    def test_watchdog_timeout_guard_still_holds(self):
        """The 2026-09-24 guard: exit -2 is slow, not tight."""
        self._answer('{"error_class":"timing_too_tight","fixable":true,'
                     '"fix_description":"relax","config_mk_changes":{"CLOCK_PERIOD":"6.0"}}')
        out = self._run(LOG_CONGESTION, exit_code=-2)
        self.assertEqual([], self.calls)
        self.assertEqual("FAIL", out["pipeline_status"])
        self.assertNotIn("CLOCK_PERIOD", self.mk())


if __name__ == "__main__":
    unittest.main(verbosity=2)
