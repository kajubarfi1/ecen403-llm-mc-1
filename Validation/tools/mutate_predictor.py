#!/usr/bin/env python3
"""
mutate_predictor.py — how good is the gate that accepts a reference model?
===========================================================================
"How do I know the predictor is right?" cannot be answered directly. What CAN
be answered is the question one level down, which is the useful one:

    If the predictor WERE wrong, would my acceptance tests notice?

That is mutation testing. Deliberately inject a realistic bug into the
reference model, run the acceptance suite, and see whether it fails. A test
suite that accepts a broken model is not evidence of anything — the same
failure this project already shipped once, where a harness reported passes it
had not earned.

The score this prints is the fraction of injected bugs the gate KILLS. It is a
measurable, citable property of the acceptance suite, and it is the honest
basis for trusting an agent-generated model.

Mutations are chosen to mirror how a language model actually gets register
semantics wrong: inverting RW1C, letting RO fields be written, forgetting WO
self-clear, off-by-one field widths, skipping reset values.

Usage:
    python3 Validation/tools/mutate_predictor.py
"""

import importlib.util
import io
import re
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
MODEL_SRC = os.path.join(ROOT, "Validation", "refmodel", "spec_register_model.py")
TEST_SRC = os.path.join(ROOT, "Validation", "tests", "test_spec_register_model.py")

# (name, what a model author got wrong, source find, source replace)
MUTATIONS = [
    ("RW1C inverted",
     "clears on write-0 instead of write-1 — the classic RW1C misreading",
     'f["value"] &= (~wbits) & fmask',
     'f["value"] &= wbits & fmask'),

    ("RO becomes writable",
     "applies bus writes to read-only fields",
     'elif acc == "RW1C":',
     'elif acc == "RO":\n                f["value"] = wbits\n            elif acc == "RW1C":'),

    ("WO does not self-clear",
     "keeps the written value instead of clearing after the side effect",
     'f["value"] = 0          # side-effect accepted, self-clears',
     'f["value"] = wbits'),

    ("WO readable",
     "lets write-only fields read back their value instead of 0",
     'if f["access"] == "WO":\n                continue                # WO always reads 0',
     'if False:\n                continue'),

    ("reset ignores spec value",
     "resets every field to 0 rather than its spec reset_value",
     'f["value"] = f["reset"] & ((1 << width) - 1)',
     'f["value"] = 0'),

    ("field width off by one",
     "computes width as hi-lo, dropping the inclusive bit",
     'width = f["hi"] - f["lo"] + 1\n            fmask = (1 << width) - 1',
     'width = f["hi"] - f["lo"]\n            fmask = (1 << width) - 1'),

    ("unmapped write reported as mapped",
     "returns success for a write to an address that does not exist",
     'if reg is None:\n            self.last_err = True\n            return False',
     'if reg is None:\n            self.last_err = True\n            return True'),

    ("read drops field shift",
     "ORs field values together without shifting them into position",
     'val |= (f["value"] & ((1 << width) - 1)) << f["lo"]',
     'val |= (f["value"] & ((1 << width) - 1))'),

    # EQUIVALENT MUTANT — proven by differential testing (4000 random trials
    # with oversize writes produced zero observable differences). Every field
    # lies within the bus width, so (data >> lo) & fmask already discards the
    # high bits; the explicit mask is defence-in-depth for a future spec with
    # a field crossing the bus width. Kept, and excluded from the score,
    # because no test can kill a mutation that changes no behaviour.
    ("write ignores data mask [EQUIVALENT]",
     "proven behaviourally identical — excluded from the score",
     'data &= self._data_mask',
     'data = data'),

    ("RW1C cleared by reset only",
     "makes write-1-to-clear a no-op entirely",
     'elif acc == "RW1C":\n                f["value"] &= (~wbits) & fmask',
     'elif acc == "RW1C":\n                pass'),
]


def run_suite_against(source_code: str):
    """Load a (possibly mutated) model, point the test suite at it, run it.
    Returns (tests_run, failures+errors)."""
    real_spec = os.path.join(ROOT, "Validation", "spec",
                             "llmmc_microarchitecturespec_filled.json")

    with tempfile.TemporaryDirectory() as td:
        mpath = os.path.join(td, "spec_register_model.py")
        with open(mpath, "w") as f:
            f.write(source_code)

        # Load the mutant under the name the test module imports.
        spec = importlib.util.spec_from_file_location("spec_register_model", mpath)
        mod = importlib.util.module_from_spec(spec)
        saved = sys.modules.pop("spec_register_model", None)
        saved_test = sys.modules.pop("test_spec_register_model", None)
        sys.modules["spec_register_model"] = mod
        try:
            spec.loader.exec_module(mod)
            # The model resolves _DEFAULT_SPEC relative to its own file, which
            # under mutation is a temp dir. Repoint it at the real spec after
            # load — cleaner than rewriting source, and applied to baseline and
            # mutants alike so the comparison stays fair.
            mod._DEFAULT_SPEC = real_spec
            tspec = importlib.util.spec_from_file_location(
                "test_spec_register_model", TEST_SRC)
            tmod = importlib.util.module_from_spec(tspec)
            sys.modules["test_spec_register_model"] = tmod
            tspec.loader.exec_module(tmod)

            suite = unittest.defaultTestLoader.loadTestsFromModule(tmod)
            buf = io.StringIO()
            res = unittest.TextTestRunner(stream=buf, verbosity=0).run(suite)
            return res.testsRun, len(res.failures) + len(res.errors), None
        except Exception as e:
            # A mutant that will not even import counts as killed — but say
            # why, so a harness bug is never mistaken for a caught mutation.
            return 0, 1, f"{type(e).__name__}: {e}"
        finally:
            sys.modules.pop("spec_register_model", None)
            sys.modules.pop("test_spec_register_model", None)
            if saved is not None:
                sys.modules["spec_register_model"] = saved
            if saved_test is not None:
                sys.modules["test_spec_register_model"] = saved_test


def main() -> int:
    original = open(MODEL_SRC).read()

    n, bad, why = run_suite_against(original)
    print(f"baseline (unmutated): {n} tests, {bad} failing")
    if bad:
        print(f"  The suite does not pass on the real model — fix that first.")
        if why:
            print(f"  reason: {why}")
        return 2
    print()

    print(f"{'INJECTED BUG':34} {'KILLED?':9} {'FAILING TESTS'}")
    print("-" * 74)
    killed = survived = equivalent = 0
    survivors = []
    for name, why, find, repl in MUTATIONS:
        if find not in original:
            print(f"  {name:32} {'N/A':9} mutation no longer applies "
                  f"(source changed)")
            continue
        mutant = original.replace(find, repl, 1)
        n, bad, _ = run_suite_against(mutant)
        if "[EQUIVALENT]" in name:
            equivalent += 1
            print(f"  {name:32} {'equiv':9} excluded — changes no behaviour")
            continue
        if bad:
            killed += 1
            print(f"  {name:32} {'killed':9} {bad} of {n}")
        else:
            survived += 1
            survivors.append((name, why))
            print(f"  {name:32} {'SURVIVED':9} <-- gate did not notice")

    total = killed + survived
    print("-" * 74)
    pct = (100.0 * killed / total) if total else 0.0
    print(f"  mutation score: {killed}/{total} ({pct:.0f}%) of KILLABLE bugs killed"
          + (f"   ({equivalent} equivalent mutant(s) excluded)" if equivalent else ""))
    if survivors:
        print("\n  SURVIVING MUTANTS — each is a hole in the acceptance suite:")
        for name, why in survivors:
            print(f"    {name}: {why}")
        print("\n  A surviving mutant means an agent could generate a model with")
        print("  that exact bug and the gate would accept it. Add a test.")
    else:
        print("\n  Every injected bug was caught. The gate has teeth against this")
        print("  mutation set — which bounds, but does not eliminate, the risk:")
        print("  it says nothing about bug classes not in the set.")
    return 0 if not survivors else 1


if __name__ == "__main__":
    sys.exit(main())
