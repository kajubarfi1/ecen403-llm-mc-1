# Handoff to Validation — 2026-10-15

From Frontend (Lehana) to Validation (Jacob). Replies to Addendum 5
(2026-10-15, afternoon) in `Validation/findings/HANDOFF_FRONTEND_2026-10-08_reply.md`
— the `propose_fix` failure on `scheduler` and your ask 4.

## 1. Ask 4: fixed — attempts 2/3 now actually run

Confirmed the bug on our side: in all four `phase{1,2,3,4}_validation_agent.py`,
the fix-attempt loop caught any exception from `_propose_fix()` (a missing
required tool-call field, same shape you hit) and did `break`, abandoning the
module after attempt 1 of `MAX_ATTEMPTS_PER_MODULE` (3). The sibling branch two
lines below, handling invalid-Python-syntax proposals, already did the right
thing (`continue` with feedback) — the asymmetry was a copy-paste bug, present
identically in all four files. Fixed: the exception handler now sets
`prev_feedback` and `continue`s, same as the syntax-error branch. This is why
our own 10/08 run also stalled at "scheduler: unresolved" after exactly one
attempt.

**Correction to your diagnosis.** You attributed this to the response hitting
`max_tokens` mid-call while emitting the full corrected generator source. We
checked: `Frontend2/scripts/Phase3/scheduler_gen.py` is 427 lines (~5,000
tokens by rough estimate), against `MAX_TOKENS = 32000` for the `propose_fix`
call — roughly 6x headroom even accounting for the other required fields
alongside the file. We don't think token budget is the mechanism; the stop
reason we captured on our own 10/08 occurrence was `stop_reason='tool_use'`
(a normal completion), not `'max_tokens'`. Our read is a one-off model
compliance miss on a schema with several required fields, not a budget
problem — which the retry fix should cover regardless of which explanation is
right. We did not raise `MAX_TOKENS` further or move to a diff-based format;
say if you still want one of those once you've seen the retry fix's effect.

## 2. Three infrastructure bugs found testing this, on your side of the fence

Trying to actually exercise the fix above against a live run surfaced three
separate issues in `Validation/tools/`, none of them RTL or judgment logic.

**2a. `validate_drop.py`'s `sh()` helper hardcodes `"python3"`.** Every
subprocess command (`run_path.py`, `compare_drops.py`, `dashboard_gen.py`,
etc.) is a literal string run via `shell=True`, so it resolves whatever
`python3` is first on PATH rather than the interpreter actually running
`validate_drop.py`. In an environment where those aren't the same (ours: a venv
with `langgraph`/`anthropic`/`paramiko`, invoked by absolute path), every
subprocess call falls back to a bare system Python missing those packages, and
every `run_path.py` invocation fails identically and instantly. `flow.py`
already resolves this correctly (`PY = sys.executable`); `validate_drop.py`
doesn't. **Not fixed by us** — this is a design choice in your file (maybe
intentional, if your normal workflow always activates a venv first), so
flagging rather than patching. We worked around it locally by activating our
venv before invoking anything, which makes bare `python3` resolve correctly
for the whole subprocess tree without touching your code.

**2b. `run_path.py` blocks on an interactive password prompt even when a key
is configured.** `main()` calls `agent.connect(password=load_password())` —
Python evaluates `load_password()` eagerly as a function argument, so it
always runs (and blocks on `getpass.getpass()` as its last resort) regardless
of whether `OLYMPUS_KEY` is set. `CadenceSSHAgent.connect()` itself already
prefers `key_path` over `password` when both are present (`sim_runner.py`
lines 143–144) — the `password` value just gets silently discarded in that
case. So a key-based setup still pays for (and in our non-interactive case,
crashed on: `EOFError` reading stdin) a password prompt it never needed.
**Fixed by us**, one line: only call `load_password()` when
`agent.ssh.get("key_path")` is falsy. Small and mechanical — revert if you'd
rather own it.

**2c. `outbox/current/*.json` isn't refreshed by a clean run. Not fixed,
still open.** After (2a) and (2b) were resolved and a real run finished with
`validate_drop.py`'s own printed output showing all 19 paths `PASS` (`pass=19
fail=0 error=0`, "19 pass / 0 fail / 0 error in 0.5 min"), the written
`Validation/findings/outbox/current/DROP_STATUS.json` from that same
invocation still showed `paths_run: []` and all 22 paths listed with stale
`run error (rc=2)` entries pointing at `.txt` logs from the *previous* (now-
fixed) failing attempt. `findings_v2.json` in the same directory carried two
`confirmed, critical` JasperGold findings on `scheduler`
(`formal/scheduler/PROTO_001`, `formal/scheduler/TIMING_008`) — but we never
ran JasperGold in this session at all, so that content is stale too. We
suspect part of this is on us: resolving the `main`/`integrate-validation`
merge conflict earlier today, we took your branch's version of
`outbox/current/*.json` for the conflicted files, which may have been an
older snapshot. But that doesn't explain why a subsequent clean
`validate_drop.py` run didn't overwrite it — our read of the `blocked` dict's
construction (populated only inside `if errored:`, and `errored` was empty
this run) suggests it isn't unconditionally rewritten when nothing newly
fails, so stale content from an earlier state just sits there. We haven't
found the exact line and didn't want to guess further into your file. This is
the one still genuinely blocking us from confirming section 1's fix end-to-end
— `flow.py` keeps halting on this stale state before ever reaching the Phase 3
fix-agent stage again.

## 3. What we can actually confirm: real end-to-end simulation works

Once (2a) and (2b) were sorted, all 19 runnable paths simulated for real on
Olympus and passed (`pass=19 fail=0 error=0`, drop `4bf921ce1833`, run
`runs/20261015-123308-llmmc_microarchitectures`). Your `flow.py` infra-halt
detection (the "did not simulate ... not a verdict on the drop" logic from
today's `integrate-validation` merge) also behaved exactly as intended earlier
in this same session, on the pre-(2b)-fix attempt: it correctly recognized the
SSH failure as infrastructure and halted for a rerun instead of misattributing
it to `scheduler` and burning a Phase 3 fix-agent call on a bogus signal. That
part of your merge is working.

What we have **not** been able to confirm yet is whether section 1's fix
actually gets attempt 2/3 to succeed on a real `scheduler` finding — (2c) has
kept routing every rerun back to a halt before reaching that stage. Your next
real run, once (2c) is sorted on your side (or if you tell us it's fine for us
to dig further into it), is the real test.

## Questions

1. Do you want to take (2a) and (2c), or would you rather we propose patches
   for those too, the way we did for (2b)? We've now touched `run_path.py`
   once; happy to keep going if that's easier than a back-and-forth per bug.
2. For (2c): is `outbox/current/` expected to be a persistent/accumulating
   ledger across runs, or should a clean `validate_drop.py` invocation always
   overwrite it fully? That changes what the right fix looks like.
3. Once (2c) is resolved, we'd like to rerun `runs/20261015-123308-llmmc_microarchitectures`
   (`--resume`) as the actual test of section 1. Anything you want us to hold
   off on until your side is ready for it?
