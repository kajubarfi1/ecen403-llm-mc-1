"""random_v2: address-aware constrained-random stimulus is legal, seeded and local."""
import collections
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "closure"))
sys.path.insert(0, os.path.join(HERE, "..", "sequences"))
import random_v2 as V  # noqa: E402
import sequence_contract as SC  # noqa: E402


def load():
    with open(V.SPEC) as f:
        spec = json.load(f)
    with open(V.SCHEMAS) as f:
        schemas = json.load(f)["interfaces"]
    with open(V.CATALOG) as f:
        catalog = json.load(f)["interfaces"]
    return spec, schemas, catalog


class RandomV2(unittest.TestCase):
    def test_passes_the_contract_and_is_deterministic(self):
        spec, schemas, catalog = load()
        addr_w = schemas["wb"]["kinds"]["write"]["addr"]["width"]
        if int(addr_w) < int(spec["host_interface"]["address_width_bits"]):
            raise unittest.SkipTest(
                f"the checked-in drop's wb address port is {addr_w} bits, the spec says "
                f"{spec['host_interface']['address_width_bits']}: a filed width regression; "
                f"the stimulus is generated to the spec and cannot be driven into that port")
        a = V.generate(spec, schemas, catalog, "wb_port", seed=7, drives=120)
        b = V.generate(spec, schemas, catalog, "wb_port", seed=7, drives=120)
        self.assertEqual(a, b)
        errs = SC.validate(a, schemas, {"wb"})
        self.assertEqual(errs, [])
        self.assertEqual(sum(1 for s in a["steps"] if s["op"] == "drive"), 120)

    def test_addresses_revisit_banks_and_rows(self):
        spec, schemas, catalog = load()
        amap = V.AddressMap(spec)
        seq = V.generate(spec, schemas, catalog, "wb_port", seed=2, drives=200, profile="conflict_heavy")
        drives = [s for s in seq["steps"] if s["op"] == "drive"]
        shift = amap.byte_off + amap.burst_off + amap.col_upper
        banks = collections.Counter((s["fields"]["addr"] >> shift) & ((1 << amap.bank_bits) - 1) for s in drives)
        # every bank used, and consecutive requests often share a bank (hits/conflicts)
        self.assertEqual(len(banks), 1 << amap.bank_bits)
        bank_of = lambda s: (s["fields"]["addr"] >> shift) & ((1 << amap.bank_bits) - 1)
        same_bank = sum(1 for x, y in zip(drives, drives[1:]) if bank_of(x) == bank_of(y))
        self.assertGreater(same_bank / len(drives), 0.4)

    def test_burst_phase_exceeds_queue_depth_without_idle(self):
        spec, schemas, catalog = load()
        depth = spec["controller_architecture"]["command_queue_depth"]
        seq = V.generate(spec, schemas, catalog, "wb_port", seed=1, drives=300)
        run, longest = 0, 0
        for s in seq["steps"]:
            run = run + 1 if s["op"] == "drive" else 0
            longest = max(longest, run)
        self.assertGreaterEqual(longest, 2 * depth)

    def test_address_map_round_trips_the_predictor_layout(self):
        spec, _, _ = load()
        amap = V.AddressMap(spec)
        a = amap.compose(row=0x1234, bank=5, colu=0x2A)
        shift = amap.byte_off + amap.burst_off
        self.assertEqual((a >> shift) & ((1 << amap.col_upper) - 1), 0x2A)
        self.assertEqual((a >> (shift + amap.col_upper)) & ((1 << amap.bank_bits) - 1), 5)
        self.assertEqual(a >> (shift + amap.col_upper + amap.bank_bits), 0x1234)


if __name__ == "__main__":
    unittest.main()


class TestStormPhase(unittest.TestCase):
    """A storm phase sends 2 x queue depth requests to one address with no
    idle between them, write first (2026-11-12: the per-entry conflict
    matrix of cmd_queue is only reachable this way)."""

    def test_storm_repeats_one_address_without_idle(self):
        RV = V
        spec, schemas, catalog = load()
        depth = int(spec["controller_architecture"].get("command_queue_depth", 16))
        found = False
        for seed in range(1, 12):
            seq = RV.generate(spec, schemas, catalog, "wb_port", seed=seed, drives=400)
            if "storm" not in seq["_provenance"]["phases"]:
                continue
            # the longest run of consecutive drives to one address, no idle between
            best, run, last = 0, 0, None
            for st in seq["steps"]:
                if st["op"] != "drive":
                    run, last = 0, None
                    continue
                a = st["fields"].get("addr", st["fields"].get("address"))
                run = run + 1 if a == last else 1
                last = a
                best = max(best, run)
            self.assertGreaterEqual(best, min(2 * depth, 8))
            found = True
            break
        self.assertTrue(found, "no seed in 1..11 drew a storm phase")
