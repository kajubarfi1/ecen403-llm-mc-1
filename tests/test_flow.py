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
        self.agent_fixes = ["wb_port"]      # what the fake agent's fix report claims (or {phase: [...]})
        self.failed = ["wb_port"]           # what the fake validation reports as failed
        self.absent = []                     # blocks the fake validation reports absent
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
            if status == "STOP":
                # a generator refused the drop: no handoff written for it
                return 1, ("    [1] resolve blocks through the declared drop (git ffff00000000)\n"
                           "    STOP: a generator refused the drop; its output is in the log.\n")
            os.makedirs(flow.OUTBOX_CURRENT, exist_ok=True)
            if self.absent:
                with open(os.path.join(flow.OUTBOX_CURRENT, "DROP_STATUS.json"), "w") as f:
                    json.dump({"partial": True, "blocks_absent": self.absent, "paths_blocked": {"path_21_wb_port_standalone": ["wb_port"]},
                               "paths_run": []}, f)
            with open(os.path.join(flow.OUTBOX_CURRENT, "HANDOFF.json"), "w") as f:
                json.dump({"drop_id": "abc123", "status": status,
                           "failed_modules": [] if status == "PASS" else self.failed}, f)
            with open(os.path.join(flow.OUTBOX_CURRENT, "retry_instructions.json"), "w") as f:
                json.dump({"failed_modules": [] if status == "PASS" else self.failed}, f)
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
            outdir = cmd[cmd.index("--output-dir") + 1]
            n = int(name[5])
            fixes = (self.agent_fixes.get(n, []) if isinstance(self.agent_fixes, dict)
                     else self.agent_fixes)
            if fixes is not None:
                os.makedirs(os.path.join(outdir, "VALIDATIONREPORT"), exist_ok=True)
                with open(os.path.join(outdir, "VALIDATIONREPORT", f"phase{n}_fix_report.json"), "w") as f:
                    json.dump({"results": [{"module": m, "final_status": "fixed"} for m in fixes]}, f)
            return self.feedback_rc, "ModuleNotFoundError: No module named 'anthropic'\n" if self.feedback_rc else ""
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
        self.saved = (flow.sh, flow.OUTBOX_CURRENT, flow.phase_agent, flow.agent_findings_flag, flow.agent_takes_yes, flow.BACKEND_OUTBOX)
        self.direct = False
        flow.agent_findings_flag = lambda agent: "--findings" if self.direct else None
        flow.agent_takes_yes = lambda agent: False
        flow.OUTBOX_CURRENT = os.path.join(self.tmp, "outbox_current")
        self.agents = {}                       # phase -> fake agent path
        flow.phase_agent = lambda n: self.agents.get(n, os.path.join(self.tmp, f"no_agent_{n}.py"))
        os.environ["ANTHROPIC_API_KEY"] = os.environ.get("ANTHROPIC_API_KEY", "x")
        os.environ["OLYMPUS_KEY"] = "/fake/key"
        os.environ.pop("USE_DOCKER", None)
        flow.QUIET = True

    def tearDown(self):
        flow.sh, flow.OUTBOX_CURRENT, flow.phase_agent, flow.agent_findings_flag, flow.agent_takes_yes, flow.BACKEND_OUTBOX = self.saved
        flow.QUIET = False
        shutil.rmtree(self.tmp, ignore_errors=True)
        os.environ.pop("OLYMPUS_KEY", None)

    def args(self, **kw):
        base = dict(request=None, preset="balanced", choices=None, spec=None, goal=None, phases=None, revalidate=False,
                    resume=None, run_dir=self.run_dir, max_spec_rounds=2, max_rtl_rounds=4,
                    max_backend_rounds=2, validate_per_phase=False, skip_backend=False, backend_mode="build",
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

    def _agent(self, n):
        p = os.path.join(self.tmp, f"phase{n}_validation_agent.py")
        open(p, "w").close()
        self.agents[n] = p



class TestHappyPath(FlowCase):
    def test_order_and_artifacts_up_to_the_unbuilt_final_stage(self):
        os.environ["USE_DOCKER"] = "1"
        rc, run = self.go(Fake(self.run_dir))
        self.assertEqual(rc, 2)
        self.assertEqual(run.state["halt"]["stage"], "final_validation")
        self.assertIn("no per-block netlist", run.state["halt"]["why"])   # the fake backend wrote none
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
        self.assertIn("--findings", agent[1])
        self.assertTrue(agent[1][agent[1].index("--findings") + 1].endswith("retry_instructions.json"))
        self.assertNotIn("--yes", agent[1], "only passed when the agent advertises it")

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

    def test_backend_gets_drop_id_spec_revision_and_mode(self):
        os.environ["USE_DOCKER"] = "1"
        fake = Fake(self.run_dir)
        rc, run = self.go(fake, backend_mode="contract")
        be = [c for c in fake.calls if c[0] == "pipeline.py"][0][1]
        self.assertEqual(be[be.index("--drop_id") + 1], "abc123")
        self.assertEqual(be[be.index("--spec_revision") + 1], "fake_rev")
        self.assertEqual(be[be.index("--mode") + 1], "contract")

    def test_backend_synth_failure_is_the_frontend_edge_and_halts_for_the_format(self):
        os.environ["USE_DOCKER"] = "1"
        rc, run = self.go(Fake(self.run_dir, backend={"pipeline_status": "FAIL", "failed_stage": "synth",
                                                      "error_message": "synthesis_error"}))
        self.assertEqual(run.state["halt"]["stage"], "backend_to_frontend")
        self.assertIn("emitted no findings", run.state["halt"]["why"])

    def test_backend_findings_are_routed_to_the_phase_agents(self):
        os.environ["USE_DOCKER"] = "1"
        self._agent(1)
        # the backend's outbox, in our envelope, naming wb_port
        flow.BACKEND_OUTBOX = os.path.join(self.tmp, "backend_outbox")
        d = os.path.join(flow.BACKEND_OUTBOX, "fake_rev", "h1")
        os.makedirs(d)
        with open(os.path.join(d, "findings_v2.json"), "w") as f:
            json.dump({"drop": {"git_head": "h1"}, "spec_revision": "fake_rev", "findings": [
                {"id": "wb_port/TIMING/x", "kind": "timing_defect", "check_id": "TIMING/x",
                 "owner_module": "wb_port", "severity": "critical", "confidence": "observed",
                 "title": "t", "expected": "slack >= 0", "actual": "WNS -0.9", "status": "open",
                 "suggested_fix": "shorten the path", "repro": {"command": "x"}}]}, f)
        with open(os.path.join(flow.BACKEND_OUTBOX, "fake_rev", "latest"), "w") as f:
            f.write("h1\n")
        fake = Fake(self.run_dir, validation=["PASS", "PASS"],
                    backend={"pipeline_status": "FAIL", "failed_stage": "synth", "error_message": "synthesis_error"})
        rc, run = self.go(fake, max_backend_rounds=2)
        names = [c[0] for c in fake.calls]
        self.assertIn(("backend_to_frontend", "ROUTED"), self.stages(run))
        self.assertIn("phase1_validation_agent.py", names, "wb_port is phase 1: its agent gets the package")
        pkg = os.path.join(self.run_dir, "backend", "retry_round_1", "retry_instructions.json")
        with open(pkg) as f:
            ri = json.load(f)
        self.assertEqual(ri["failed_modules"], ["wb_port"])
        self.assertEqual(ri["retry_instructions"]["wb_port"]["failed_checks"][0]["fix"], "shorten the path")
        self.assertEqual(names.count("validate_drop.py"), 2, "the regenerated drop is validated again")

    def test_final_stage_runs_each_netlist_through_its_paths(self):
        os.environ["USE_DOCKER"] = "1"
        self.run_paths = []
        fake = Fake(self.run_dir, backend={"pipeline_status": "PASS", "artifacts": []})
        orig = fake.__call__

        def call(cmd, cwd=None, stdin=None, env=None, log=None, timeout=None):
            name = os.path.basename(next((c for c in cmd if c.endswith(".py")), ""))
            if name == "pipeline.py":
                rc, out = orig(cmd, cwd, stdin, env, log, timeout)
                out_root = cmd[cmd.index("--out_root") + 1]
                os.makedirs(os.path.join(out_root, "runner", "wb_port"))
                open(os.path.join(out_root, "runner", "wb_port", "6_final.v"), "w").close()
                return rc, out
            if name == "run_path.py":
                self.run_paths.append(cmd)
                return 0, "  path verdict : PASS\n"
            return orig(cmd, cwd, stdin, env, log, timeout)
        flow.sh = call
        a = self.args()
        run = flow.Run(self.run_dir, a)
        rc = flow.run_flow(run, a)
        self.assertEqual(rc, 0, run.state["halt"])
        self.assertEqual(run.state["status"], "complete")
        paths = [c[c.index("--path") + 1] for c in self.run_paths]
        self.assertIn("path_21_wb_port_standalone", paths)
        self.assertTrue(all("--netlist" in c and any(x.startswith("wb_port=") for x in c) for c in self.run_paths))
        self.assertNotIn("path_14_status_init", paths, "no netlist for init_fsm/config_regs: not run")

    def test_missing_olympus_key_halts_before_phases(self):
        os.environ.pop("OLYMPUS_KEY", None)
        fake = Fake(self.run_dir)
        rc, run = self.go(fake)
        self.assertEqual(run.state["halt"]["stage"], "rtl_generation")
        self.assertIn("OLYMPUS_KEY", run.state["halt"]["why"])
        self.assertFalse(any(c[0].startswith("phase") for c in fake.calls))


class TestPhaseLimitedLoop(FlowCase):
    def test_phases_1_generates_only_phase_1_validates_partial_and_completes(self):
        self._agent(1)
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"])
        rc, run = self.go(fake, phases="1")
        self.assertEqual(rc, 0, run.state["halt"])
        self.assertEqual(run.state["status"], "complete")
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("phase1_pipeline.py"), 2)      # initial + regeneration
        self.assertNotIn("phase2_pipeline.py", names)
        self.assertNotIn("generate_top.py", names, "no top-level assembly on a phase-limited run")
        self.assertNotIn("pipeline.py", names, "backend skipped")
        vd = [c for c in fake.calls if c[0] == "validate_drop.py"]
        self.assertTrue(all("--partial" in c[1] for c in vd), "a Phase-1 drop is validated as partial")
        self.assertEqual(len(vd), 2)


class TestAgentOutcome(FlowCase):
    def test_agent_that_fixed_nothing_halts_with_its_reason(self):
        self._agent(1)
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"], feedback_rc=1)
        fake.agent_fixes = []
        rc, run = self.go(fake, phases="1")
        self.assertEqual(run.state["halt"]["stage"], "frontend_regeneration")
        self.assertIn("fixed nothing", run.state["halt"]["why"])
        self.assertIn("anthropic", run.state["halt"]["why"])
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("phase1_pipeline.py"), 1, "no blind regeneration")

    def test_one_phase_fixing_is_enough_to_revalidate(self):
        # phase 1 fixed wb_port, phase 2's agent gave up (API error): the
        # drop changed, so it is validated again; the halt is only for
        # "no phase changed anything" (2026-10-08 live run: bank_tracker fixed
        # by phase 2, scheduler unresolved by phase 3, run halted)
        self._agent(1); self._agent(2)
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"], feedback_rc=1)
        fake.failed = ["wb_port", "bank_tracker"]
        fake.agent_fixes = {1: ["wb_port"], 2: []}
        rc, run = self.go(fake, phases="1,2")
        self.assertEqual(rc, 0, run.state.get("halt"))
        self.assertIn(("frontend_regeneration", "PARTIAL"), self.stages(run))
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("validate_drop.py"), 2)
        self.assertEqual(names.count("phase2_pipeline.py"), 2, "the unfixed phase is regenerated too")

    def test_validation_stopped_before_judging_is_not_a_verdict(self):
        # round 1 fails, the agent patches, round 2's validate_drop stops in
        # its regenerate step (a manifest the patch broke): the stale handoff
        # in outbox/current must not be read as round 2's FAIL
        self._agent(1)
        fake = Fake(self.run_dir, validation=["FAIL", "STOP"], feedback_rc=1)
        fake.agent_fixes = ["wb_port"]
        rc, run = self.go(fake, phases="1")
        self.assertEqual(run.state["halt"]["stage"], "rtl_validation")
        self.assertIn("stopped before judging drop ffff00000000", run.state["halt"]["why"])
        self.assertIn("refused", run.state["halt"]["why"])
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("phase1_validation_agent.py"), 1, "no agent on a non-verdict")

    def test_partial_fix_regenerates(self):
        self._agent(1)
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"], feedback_rc=1)
        fake.agent_fixes = ["wb_port"]           # exit 1 (not every module) but one fixed
        rc, run = self.go(fake, phases="1")
        self.assertEqual(rc, 0, run.state["halt"])
        self.assertIn(("frontend_regeneration", "PARTIAL"), self.stages(run))


class TestGeneratedBlockMustBeJudged(FlowCase):
    def test_generated_block_absent_from_the_drop_halts_even_on_pass(self):
        fake = Fake(self.run_dir, validation=["PASS"])
        fake.absent = ["wb_port"]
        rc, run = self.go(fake, phases="1")
        self.assertEqual(run.state["halt"]["stage"], "rtl_validation")
        self.assertIn("wb_port", run.state["halt"]["why"])
        self.assertEqual(run.state["halt"]["unjudged"], ["wb_port"])


class TestRevalidate(FlowCase):
    def test_resume_with_revalidate_runs_validation_again(self):
        self._agent(1)
        rc, run = self.go(Fake(self.run_dir), phases="1")
        self.assertEqual(run.state["status"], "complete")
        fake = Fake(self.run_dir, validation=["FAIL", "PASS"])
        flow.sh = fake
        a = self.args(phases="1", revalidate=True)
        run2 = flow.Run(self.run_dir)
        rc = flow.run_flow(run2, a)
        self.assertEqual(rc, 0, run2.state["halt"])
        names = [c[0] for c in fake.calls]
        self.assertEqual(names.count("validate_drop.py"), 2)
        self.assertEqual(names.count("phase1_validation_agent.py"), 1)
        self.assertEqual(run2.state["rounds"]["rtl"], 3)


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
