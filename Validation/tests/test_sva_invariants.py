#!/usr/bin/env python3
"""Invariant assertions from signal groups: `@cmd(iface, COMMAND)` resolves
through the catalog, every other identifier is a manifest port, and a name
the block does not have is a loud failure (2026-10-22, refresh rules)."""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "sva"))
import sva_gen as SG  # noqa: E402


class TestInvariantRules(unittest.TestCase):

    def setUp(self):
        with open(SG.SPEC_PATH) as f:
            self.spec = json.load(f)
        with open(SG.CATALOG_PATH) as f:
            self.catalog = json.load(f)["interfaces"]
        with open(SG.SCHEMA_PATH) as f:
            self.schemas = json.load(f)["interfaces"]
        if "sched_cmd" not in self.schemas:
            self.skipTest("scheduler stream not in the current drop's schemas")

    def test_cmd_macro_resolves_through_the_catalog(self):
        expr, ports = SG.expand_expr("@cmd(sched_cmd, REF) && (|bank_is_active)", "scheduler",
                                     self.catalog, self.schemas)
        self.assertEqual(expr, "((cmd_valid) && (cmd_type == 4'd5)) && (|bank_is_active)")
        self.assertEqual(ports, {"cmd_valid", "cmd_type", "bank_is_active"})

    def test_unknown_command_or_stream_is_refused(self):
        with self.assertRaises(SG.SvaGenError):
            SG.expand_expr("@cmd(sched_cmd, NOPE)", "scheduler", self.catalog, self.schemas)
        with self.assertRaises(SG.SvaGenError):
            SG.expand_expr("@cmd(sched_cmd, REF)", "refresh_ctrl", self.catalog, self.schemas)

    def test_refresh_groups_generate_against_the_drop(self):
        with open(SG.RULES_PATH) as f:
            groups = {g["name"]: g for g in json.load(f)["signal_groups"]}
        mod, src, block, ids = SG.generate_signal_group(self.spec, groups["refresh_scheduler"],
                                                        self.catalog, self.schemas)
        self.assertEqual((block, ids), ("scheduler", ["REF_002", "REF_001"]))
        self.assertIn("!(((cmd_valid) && (cmd_type == 4'd5)) && (|bank_is_active))", src)
        self.assertIn("input logic [7:0] bank_is_active", src)
        self.assertIn("c_REF_002: cover property", src)
        self.assertNotIn("refresh_ctrl", groups, "REF_001 is the scheduler's obligation, not refresh_ctrl's")

    def test_liveness_rule_is_a_bounded_obligation_at_the_scheduler(self):
        with open(SG.RULES_PATH) as f:
            groups = {g["name"]: g for g in json.load(f)["signal_groups"]}
        mod, src, block, ids = SG.generate_signal_group(self.spec, groups["refresh_scheduler"],
                                                        self.catalog, self.schemas)
        self.assertIn("REF_001", ids)
        self.assertIn("$rose(ref_urgent) |-> ##[1:REF_001_BOUND] ref_ack", src)
        self.assertIn("parameter int REF_001_BOUND = ", src)
        self.assertNotIn("input logic $rose", src)
        b = groups["refresh_scheduler"]["liveness_rules"][0]["bound"]
        n = SG.liveness_bound(self.spec, b)
        ws = int(self.spec["timing_model"].get("counter_clock", {}).get("window_scale", 1))
        expect = ws * sum(SG.cycles_for(self.spec, p)[0] for p in b["params"]) + (1 << int(self.spec["memory_geometry"]["bank_bits"])) + b["slack"]
        self.assertEqual(n, expect)

    def test_liveness_rule_skipped_when_the_policy_is_not_the_specs(self):
        grp = {"name": "x", "block": "scheduler", "liveness_rules": [{
            "id": "X_001", "when": {"spec_path": "controller_architecture.refresh_policy.refresh_priority", "equals": "never"},
            "trigger": "$rose(ref_urgent)", "response": "ref_ack", "bound": {"params": ["tRP"]}, "requirement": "r"}]}
        mod, src, block, ids = SG.generate_signal_group(self.spec, grp, self.catalog, self.schemas)
        self.assertEqual(ids, [])

    def test_a_port_the_manifest_lacks_is_a_loud_failure(self):
        grp = {"name": "x", "block": "scheduler",
               "invariant_rules": [{"id": "X_001", "never": "no_such_port", "cover": "ref_urgent",
                                    "requirement": "r."}]}
        with self.assertRaises(SG.SvaGenError):
            SG.generate_signal_group(self.spec, grp, self.catalog, self.schemas)



class TestPartialDrops(unittest.TestCase):

    def test_absent_blocks_parsed_from_schema_notes(self):
        sdoc = {"streams_without_block": ["sched_cmd (scheduler)", "dp_wr (data_path)", "odd note"]}
        self.assertEqual(SG.absent_blocks(sdoc), {"scheduler", "data_path"})
        self.assertEqual(SG.absent_blocks({}), set())

    def test_cmd_macro_on_an_absent_stream_is_a_loud_failure(self):
        with open(SG.CATALOG_PATH) as f:
            catalog = json.load(f)["interfaces"]
        with self.assertRaises(SG.SvaGenError):
            SG.expand_expr("@cmd(sched_cmd, REF)", "scheduler", catalog, {})


if __name__ == "__main__":
    unittest.main()
