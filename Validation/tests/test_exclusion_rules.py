"""Coverage exclusions are rules over the spec, resolved per spec (exclusion_rules.py)."""
import copy
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "coverage"))
import exclusion_rules as XR  # noqa: E402

SPEC = json.load(open(os.path.join(ROOT, "Spec", "llmmc_microarchitecturespec_filled.json")))
EXCL = json.load(open(os.path.join(ROOT, "Validation", "coverage", "exclusions.json")))


class Rules(unittest.TestCase):

    def test_counter_bits_follow_the_spec_value(self):
        rule = {"above_max": "timing_model.$derived_cycles.tRCD_nCK", "width": 8}
        self.assertEqual(XR.resolve_bits(rule, SPEC), [4, 5, 6, 7])          # tRCD 11 -> bits 4..7
        other = copy.deepcopy(SPEC)
        other["timing_model"]["$derived_cycles"]["tRCD_nCK"] = 20
        self.assertEqual(XR.resolve_bits(rule, other), [5, 6, 7])             # 20 -> bits 5..7
        other["timing_model"]["$derived_cycles"]["tRCD_nCK"] = 200
        self.assertEqual(XR.resolve_bits(rule, other), [])                    # nothing excluded

    def test_arithmetic_and_functions(self):
        r = {"above_max": "ceil(timing_model.CL_cycles / clocking_model.clock_ratio_ddr_to_controller) - 1", "width": 8}
        self.assertEqual(XR.resolve_bits(r, SPEC), [2, 3, 4, 5, 6, 7])        # ceil(11/4)-1 = 2
        self.assertEqual(XR.resolve_bits({"low_bits": "log2(memory_geometry.burst_length)"}, SPEC), [0, 1, 2])
        with self.assertRaises(XR.RuleError):
            XR.resolve_bits({"above_max": "__import__('os').system('x')"}, SPEC)
        with self.assertRaises(XR.RuleError):
            XR.resolve_bits({"above_max": "timing_model.no_such_thing"}, SPEC)

    def test_register_map_rules(self):
        self.assertEqual(XR.resolve_bits({"reserved_of": "CTRL_CONFIG"}, SPEC), list(range(8, 32)))
        self.assertEqual(XR.resolve_bits({"reserved_of": "BIST_ADDR_START"}, SPEC), [29, 30, 31])
        self.assertEqual(XR.resolve_bits({"address_bits_unused": True}, SPEC), [0, 1, 6, 7])
        other = copy.deepcopy(SPEC)
        other["csr_register_map"]["registers"].append({"name": "X", "offset": "0x40", "fields": []})
        self.assertEqual(XR.resolve_bits({"address_bits_unused": True}, other), [0, 1, 7])

    def test_literal_bit_lists_are_rejected(self):
        with self.assertRaises(XR.RuleError):
            XR.resolve_bits([4, 5, 6, 7], SPEC)

    def test_every_checked_in_exclusion_resolves(self):
        for e in EXCL["exclusions"]:
            r = XR.resolve(e, SPEC)
            self.assertTrue(r["signals"], e["id"])
            self.assertTrue(r["bits"] == "all" or isinstance(r["bits"], list), e["id"])

    def test_undriven_inputs_skip_connected_tied_and_boundary_ports(self):
        imap = {"connections": [{"from": "init_fsm.init_done", "to": "config_regs.sts_init_done"}],
                "standalone_ties": {"config_regs.sts_cal_done": {"value": "1'b0"}}}
        ports = {"clk": {"dir": "input"}, "rst_n": {"dir": "input"},
                 "sts_init_done": {"dir": "input"}, "sts_cal_done": {"dir": "input"},
                 "sts_bist_done": {"dir": "input"}, "csr_adr_i": {"dir": "input"},
                 "cfg_ecc_enable": {"dir": "output"}}
        got = XR.undriven_inputs("config_regs", imap, ports)
        self.assertEqual(got, ["sts_bist_done"])     # csr_adr_i is a catalog (host) port


if __name__ == "__main__":
    unittest.main()
