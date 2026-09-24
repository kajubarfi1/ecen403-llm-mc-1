"""integration_map_gen: the integration map is derived from manifest `source`
fields, and the residue that manifests cannot express is carried explicitly."""

import copy
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "structural"))
import integration_map_gen as G  # noqa: E402


def _port(width, d, source=None):
    return {"width": width, "dir": d, "group": "g", "source": source}


# A three-block toy design: producer -> consumer, plus a port the design
# drives through registered glue.
MANIFESTS = {
    "prod": {"out_a": _port(8, "output"), "out_b": _port(1, "output"),
             "out_c": _port(4, "output")},
    "cons": {"in_a": _port(8, "input", "prod.out_a"),
             "in_b": _port(1, "input"),               # no source: override
             "in_c": _port(4, "input", "prod.out_c")},  # glue target
    "other": {"x": _port(1, "input")},
}
BLOCKS = ["prod", "cons", "other"]
OV = {"connections": [{"from": "prod.out_b", "to": "cons.in_b"}],
      "glue": [{"from": "prod.out_c", "to": ["cons.in_c"], "delay_cycles": 1,
                "why": "registered."}],
      "expr_glue": [], "ties": {}, "requires": {}, "stubs": []}


class Derivation(unittest.TestCase):
    def test_manifest_edge_and_override_and_glue(self):
        imap, rep = G.build(MANIFESTS, BLOCKS, OV)
        edges = {(c["from"], c["to"]) for c in imap["connections"]}
        self.assertEqual(edges, {("prod.out_a", "cons.in_a"), ("prod.out_b", "cons.in_b")})
        self.assertEqual(rep["manifest_edges"], 1)
        self.assertEqual(rep["override_edges"], 1)
        # the glue target's direct source is superseded and reported
        self.assertEqual([(s["from"], s["to"], s["superseded_by"]) for s in rep["superseded"]],
                         [("prod.out_c", "cons.in_c", "glue")])
        # the override edge is the one consumer port without a source
        self.assertEqual(rep["missing"], {"cons": ["in_b"]})
        self.assertEqual(imap["glue"], OV["glue"])

    def test_redundant_override_is_reported_not_duplicated(self):
        m = copy.deepcopy(MANIFESTS)
        m["cons"]["in_b"]["source"] = "prod.out_b"      # manifest catches up
        imap, rep = G.build(m, BLOCKS, OV)
        self.assertEqual(len(imap["connections"]), 2)
        self.assertEqual([(c["from"], c["to"]) for c in rep["redundant"]],
                         [("prod.out_b", "cons.in_b")])
        self.assertEqual(rep["missing"], {})

    def test_source_naming_missing_port_refuses(self):
        m = copy.deepcopy(MANIFESTS)
        m["cons"]["in_a"]["source"] = "prod.nope"
        with self.assertRaises(G.MapError):
            G.build(m, BLOCKS, OV)

    def test_width_mismatch_refuses(self):
        m = copy.deepcopy(MANIFESTS)
        m["cons"]["in_a"]["width"] = 16
        with self.assertRaises(G.MapError):
            G.build(m, BLOCKS, OV)

    def test_source_that_is_an_input_refuses(self):
        m = copy.deepcopy(MANIFESTS)
        m["cons"]["in_a"]["source"] = "other.x"
        with self.assertRaises(G.MapError):
            G.build(m, BLOCKS, OV)

    def test_findings_name_ports_and_wrong_sources(self):
        _, rep = G.build(MANIFESTS, BLOCKS, OV)
        fs = G.to_findings(rep, "rev")
        kinds = sorted(f["kind"] for f in fs)
        self.assertEqual(kinds, ["manifest_gap", "manifest_wrong_source"])
        gap = next(f for f in fs if f["kind"] == "manifest_gap")
        self.assertEqual(gap["evidence"]["ports"], ["in_b"])
        self.assertEqual(gap["target"], "frontend")


class OnDiskMap(unittest.TestCase):
    """The committed map must be what the generator produces from the drop."""

    def test_map_is_current(self):
        blocks = G.blocks_in_order()
        with open(G.OVERRIDES_PATH) as f:
            ov = json.load(f)
        imap, _ = G.build(G.load_manifests(blocks), blocks, ov)
        with open(G.MAP_PATH) as f:
            on_disk = json.load(f)
        self.assertEqual({(c["from"], c["to"]) for c in imap["connections"]},
                         {(c["from"], c["to"]) for c in on_disk["connections"]})
        for k in ("glue", "expr_glue", "ties", "requires", "stubs"):
            self.assertEqual(imap[k], on_disk[k], k)

    def test_every_override_is_still_needed(self):
        blocks = G.blocks_in_order()
        with open(G.OVERRIDES_PATH) as f:
            ov = json.load(f)
        _, rep = G.build(G.load_manifests(blocks), blocks, ov)
        self.assertEqual(rep["redundant"], [],
                         "an override duplicates a manifest source; delete it")


if __name__ == "__main__":
    unittest.main()
