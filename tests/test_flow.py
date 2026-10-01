#!/usr/bin/env python3
"""flow.py state machine, with every subsystem faked at the subprocess
boundary. What is pinned: stage order, where artifacts land, the halts
(spec review FAIL, missing feedback agent, caps, backend without Docker,
the not-yet-built final stage), and resume."""

import json
import os
import shutil
import sys
import tempfile
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, ROOT)
import flow  # noqa: E402


class Fake:
    """Fakes `flow.sh`: recognises each subsystem command by its script and
    writes what the real one would, as scripted by the test."""

    def __init__(self, run, review_rc=0, phase_fail=None, validation=("PASS",),
                 backend=None, feedback_rc=0):
        self.run, self.review_rc, self.phase_fail = run, review_rc, phase_fail
        self.validation = list(validation)       # one status per validation call
        self.backend, self.feedback_rc = backend, feedback_rc
        self.calls = []

    def __call__(self, cmd, cwd=None, stdin=None, env=None, log=None, timeout=None):
        script = next((c for c in cmd if c.endswith(".py")), "")
        name = os.path.basename(script)
        self.calls.append((name, list(cmd), stdin, dict(env or {})))
        if name == "microarch_cli.py":
            out = cmd[cmd.index("--out") + 1]
            os.makedirs(os.path.dirname(out), exist_ok=True)
            with open(out, "w") as f:
                json.dump({"revision": "fake_rev"}, f)
            return 0, "ok"
        if name == "validate_spec_stage.py":
            out = cmd[cmd.index("--json") + 1]
            os.makedirs(os.path.dirname(out), exist_ok=True)
            with open(out, "w") as f:
                json.dump({"blocking": ["schema: x"] if self.review_rc else [], "advisory": []}, f)
            self.review_rc, rc = (self.review_rc - 1 if self.review_rc > 0 else 0), self.review_rc
            return rc, "  status : FAIL\n" if rc else "  [gap:decision] X\n"
        if name.startswith("phase") and name.endswith("_pipeline.py"):
            n = int(name[5])
            spec, outdir = stdin.split("\n")[:2]
            rep = os.path.join(outdir, "VALIDATIONREPORT")
            os.makedirs(rep, exist_ok=True)
            if self.phase_fail == n:
                with open(os.path.join(rep, f"phase{n}_error_report.json"), "w") as f:
                    json.dump({"failure_stage": "LINT", "failed_modules": ["wb_port"]}, f)
                return 1, ""
            with open(os.path.join(rep, f"phase{n}_final_report.json"), "w") as f:
                json.dump({"lint_status": "PASS", "sim_status": "PASS"}, f)
            return 0, ""
        if name == "generate_top.py":
            outdir = cmd[cmd.index("--output-dir") + 1]
            os.makedirs(os.path.join(outdir, "TOPRTL"), exist_ok=True)
            return 0, ""
        if name == "validate_drop.py":
            status = self.validation.pop(0) if self.validation else "PASS"
            os.makedirs(flow.OUTBOX_CURRENT, exist_ok=True)
            with open(os.path.join(flow.OUTBOX_CURRENT, "HANDOFF.json"), "w") as f:
                json.dump({"drop_id": "abc123", "status": status,
                           "failed_modules": [] if status == "PASS" else ["wb_port"]}, f)
            with open(os.path.join(flow.OUTBOX_CURRENT, "retry_instructions.json"), "w") as f:
                json.dump({"failed_modules": [] if status == "PASS" else ["wb_port"]}, f)
            return 0 if status == "PASS" else 1, ""
        if name == "to_frontend_error_report.py":
            retry = cmd[cmd.index("--retry") + 1]
            with open(retry) as f:
                failed = json.load(f).get("failed_modules", [])
            phases = {n: blocks for n, _, _, _, blocks in flow.PHASES}
            written = {str(n): f"rep{n}" for n, blocks in phases.items() if set(blocks) & set(failed)}
            return 0, json.dumps(written) + "\n"
        if name.endswith("_validation_agent.py"):
            self.calls[-1] = (name, list(cmd), stdin, dict(env or {}))
            return self.feedback_rc, ""
        if name == "pipeline.py":
            out_root = cmd[cmd.index("--out_root") + 1]
            os.makedirs(out_root, exist_ok=True)
            with open(os.path.join(out_root, "pipeline_final_report_TOPRTL.json"), "w") as f:
                json.dump(self.backend or {"pipeline_status": "PASS", "artifacts": ["x/6_final.v"]}, f)
            return 0 if (self.backend or {}).get("pipeline_status", "PASS") == "PASS" else 1, ""
        raise AssertionError(f"unexpected command {name}")


class FlowCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="flow_")
        self.run_dir = os.path.join(self.tmp, "run")
        self.saved = (flow.sh, flow.OUTBOX_CURRENT, flow.phase_agent, flow.agent_takes_retry)
        self.direct = False
        flow.agent_takes_retry = lambda agent: self.direct
        flow.OUTBOX_CURRENT = os.path.join(self.tmp, "outbox_current")
        self.agents = {}                       # phase -> fake agent path
        flow.phase_agent = lambda n: self.agents.get(n, os.path.join(self.tmp, f"no_agent_{n}.py"))
        os.environ["ANTHROPIC_API_KEY"] = os.environ.get("ANTHROPIC_API_KEY", "x")
        os.environ["OLYMPUS_KEY"] = "/fake/key"
        os.environ.pop("USE_DOCKER", None)
        flow.QUIET = True

    def tearDown(self):
        flow.sh, flow.OUTBOX_CURRENT, flow.phase_agent, flow.agent_takes_retry = self.saved
        flow.QUIET = False
        shutil.rmtree(self.tmp, ignore_errors=True)
        os.environ.pop("OLYMPUS_KEY", None)

    def args(self, **kw):
        base = dict(request=None, preset="balanced", choices=None, spec=None, goal=None,
                    resume=None, run_dir=self.run_dir, max_spec_rounds=2, max_rtl_rounds=4,
                    max_backend_rounds=2, validate_per_phase=False, skip_backend=False,
                    dry_run=False)
        base.update(kw)
        return type("A", (), base)()

    def go(self, fake, **kw):
        flow.sh = fake
        a = self.args(**kw)
        run = flow.Run(self.run_dir, a)
        rc = flow.run_flow(run, a)
        return rc, run

    def stages(self, run):
        return [(s["stage"], s["status"]) for s in run.state["stages"]]


class TestHappyPath(FlowCase):
    def test_order_and_artifacts_up_to_the_unbuilt_final_stage(self):
        os.environ["USE_DOCKER"] = "1"
        rc, run = self.go(Fake(self.run_dir))
        self.assertEqual(rc, 2)
        self.assertEqual(run.state["halt"]["stage"], "final_validation")
        self.assertIn("NOT_IMPLEMENTED", run.state["halt"]["why"])
        st = self.stages(run)
        order = [s for s, _ in st]
        self.assertEqual(order[:3], ["spec_synthesis", "spec_review", "rtl_generation"])
        self.assertIn(("rtl_validation", "PASS"), st)
        self.assertIn(("backend", "PASS"), st)
        self.assertTrue(os.path.exists(os.path.join(self.run_dir, "spec", "generated_spec.json")))
        self.assertTrue(os.path.exists(os.path.join(self.run_dir, "drop", "generated_spec.json")),
                        "the drop ships the spec it was generated from")
        self.assertTrue(os.path.exists(os.path.join(self.run_dir, "drop", "TOPRTL")))
        self.assertTrue(os.path.exists(os.path.join(self.run_dir, "validation", "round_1", "HANDOFF.json")))
        self.assertEqual(run.state["netlist"], "x/6_final.v")

    def test_skip_backend_completes(self):
        rc, run = self.go(Fake(self.run_dir), skip_backend=True)
        self.assertEqual(rc, 0)
        self.assertEqual(run.state["status"], "complete")

    def test_phase_pipelines_get_spec_and_drop_on_stdin_and_validation_gets_the_env(self):
        fake = Fake(self.run_dir)
        self.go(fake, skip_backend=True)
        phase = [c for c in fake.calls if c[0] == "phase1_pipeline.py"][0]
        self.assertEqual(phase[2].split("\n")[:2],
                         [os.path.join(self.run_dir, "spec", "generated_spec.json"),
                          os.path.join(self.run_dir, "drop")])
        val = [c for c in fake.calls if c[0] == "validate_drop.py"][0]
        self.assertEqual(val[3]["VALIDATION_RTL_DROP_ROOTS"], os.path.join(self.run_dir, "drop"))
        self.assertEqual(val[3]["VALIDATION_SPEC"], os.path.join(self.run_dir, "spec", "generated_spec.json"))


class TestHalts(FlowCase):
    def test_spec_review_fail_on_a_preset_halts_before_any_rtl(self):
        fake = Fake(self.run_dir, review_rc=1)
        rc, run = self.go(fake)
        self.assertEqual(rc, 2)
        self.assertEqual(run.state["halt"]["stage"], "spec_review")
        self.assertIn("cannot revise", run.state["halt"]["why"])
        self.assertFalse(any(c[0].startswith("phase") for c in fake.calls))

    def test_spec_review_fail_on_english_goes_back_to_the_microarch_agent(self):
        # review fails once, then passes on the revised spec
        fake = Fake(self.run_dir, review_rc=1)
        rc, run = self.go(fake, preset=None, request="DDR3-1333 x16 one lane", skip_backend=True)
        self.assertEqual(rc, 0, run.state["halt"])
        synth = [c for c in fake.calls if c[0] == "microarch_cli.py"]
        self.assertEqual(len(synth), 2)
        self.assertIn("FAILED validation review", synth[1][1][2], "findings travel in the request text")
        self.assertIn("schema: x", synth[1][1][2])
        self.assertEqual(run.state["rounds"]["spec"], 2)

    def test_spec_round_cap(self):
        fake = Fake(self.run_dir, review_rc=5)
        rc, run = self.go(fake, preset=None, request="anything", max_spec_rounds=2)
        self.assertEqual(run.state["halt"]["stage"], "spec_review")
        self.assertIn("cap 2", run.state["halt"]["why"])
        self.assertEqual(len([c for c in fake.calls if c[0] == "microarch_cli.py"]), 2)

    def test_frontend_phase_failure_halts_with_its_report(self):
        rc, run = self.go(Fake(self.run_dir, phase_fail=2))
        self.assertEqual(run.state["halt"]["stage"], "rtl_generation")
        self.assertIn("phase 2 failed at LINT", run.state["halt"]["why"])
        self.assertEqual(run.state["halt"]["phase"], 2)

    def _agent(self, n):
        p = os.path.join(self.tmp, f"phase{n}_validation_agent.py")
        open(p, "w").close()
        self.agents[n] = p

    def test_validation_fail_without_a_phase_agent_halts_with_the_package(self):
        rc, run = self.go(Fake(self.run_dir, validation=["FAIL"]))        # wb_port: phase 1, no agent
        self.assertEqual(run.state["halt"]["stage"], "frontend_regeneration")
        self.assertIn("no validation agent", run.state["halt"]["why"])
        self.assertEqual(run.state["halt"]["phases"], [1])
        self.assertTrue(os.path.exists(os.path.join(run.state["halt"]["package"], "retry_instructions.json")))

    def test_phase_agent_loop_regenerates_only_the_failed_phase_then_passes(self):
        self._agent(1)
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"])
        rc, run = self.go(fake, skip_backend=True)
        self.assertEqual(rc, 0, run.state["halt"])
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("phase1_validation_agent.py"), 1)
        agent = [c for c in fake.calls if c[0] == "phase1_validation_agent.py"][0]
        self.assertTrue(agent[2].startswith("a\n"), "every proposal is applied unattended")
        self.assertIn("--output-dir", agent[1])
        self.assertEqual(names.count("phase1_pipeline.py"), 2)   # wb_port is phase 1
        self.assertEqual(names.count("phase2_pipeline.py"), 1)
        self.assertEqual(names.count("validate_drop.py"), 2)
        self.assertEqual(run.state["rounds"]["rtl"], 2)

    def test_agent_that_takes_retry_gets_our_package_directly(self):
        self._agent(1)
        self.direct = True
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"])
        rc, run = self.go(fake, skip_backend=True)
        self.assertEqual(rc, 0, run.state["halt"])
        agent = [c for c in fake.calls if c[0] == "phase1_validation_agent.py"][0]
        self.assertIn("--retry", agent[1])
        self.assertTrue(agent[1][agent[1].index("--retry") + 1].endswith("retry_instructions.json"))
        self.assertIn("--yes", agent[1])

    def test_rtl_round_cap(self):
        self._agent(1)
        rc, run = self.go(Fake(self.run_dir, validation=["FAIL"] * 6), max_rtl_rounds=2, skip_backend=True)
        self.assertEqual(run.state["halt"]["stage"], "frontend_regeneration")
        self.assertIn("cap 2", run.state["halt"]["why"])
        self.assertEqual(run.state["rounds"]["rtl"], 2)

    def test_backend_needs_docker(self):
        rc, run = self.go(Fake(self.run_dir))
        # USE_DOCKER unset in setUp -> the backend stage halts before running
        os.environ.pop("USE_DOCKER", None)
        rc, run2 = self.go(Fake(self.run_dir))
        self.assertIn(run2.state["halt"]["stage"], ("backend", "final_validation"))

    def test_backend_synth_failure_is_the_frontend_edge_and_halts_for_the_format(self):
        os.environ["USE_DOCKER"] = "1"
        rc, run = self.go(Fake(self.run_dir, backend={"pipeline_status": "FAIL", "failed_stage": "synth",
                                                      "error_message": "synthesis_error"}))
        self.assertEqual(run.state["halt"]["stage"], "backend_to_frontend")
        self.assertIn("no agreed backend->frontend artifact", run.state["halt"]["why"])

    def test_missing_olympus_key_halts_before_phases(self):
        os.environ.pop("OLYMPUS_KEY", None)
        fake = Fake(self.run_dir)
        rc, run = self.go(fake)
        self.assertEqual(run.state["halt"]["stage"], "rtl_generation")
        self.assertIn("OLYMPUS_KEY", run.state["halt"]["why"])
        self.assertFalse(any(c[0].startswith("phase") for c in fake.calls))


class TestResume(FlowCase):
    def test_resume_continues_after_the_halt_is_fixed(self):
        os.environ.pop("OLYMPUS_KEY", None)
        rc, run = self.go(Fake(self.run_dir))
        self.assertEqual(run.state["halt"]["stage"], "rtl_generation")
        os.environ["OLYMPUS_KEY"] = "/fake/key"
        fake = Fake(self.run_dir)
        flow.sh = fake
        a = self.args(skip_backend=True)
        run2 = flow.Run(self.run_dir)
        rc = flow.run_flow(run2, a)
        self.assertEqual(rc, 0)
        self.assertEqual(run2.state["status"], "complete")
        names = [c[0] for c in fake.calls]
        self.assertNotIn("microarch_cli.py", names, "spec synthesis is not redone on resume")
        self.assertNotIn("validate_spec_stage.py", names, "a passed review is not redone")


if __name__ == "__main__":
    unittest.main()
