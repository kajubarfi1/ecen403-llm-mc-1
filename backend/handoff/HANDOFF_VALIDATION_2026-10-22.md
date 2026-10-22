# Handoff to Validation — 2026-10-22

From Backend (Dawson) to Validation (Jacob). One finding in `flow.py`, with a
concrete case sitting in our outbox that would exercise it. Nothing in
`Validation/` was changed by us.

Context first, because it explains why this has not shown up in your runs: the
backend stage is skipped on any `--phases` run, not only `--skip-backend`
(`flow.py:664`, and again at `937` before `final_validation`). Every Phase 3 and
Phase 4 round so far has been phase-limited, so the backend stage has never
executed inside the flow. That gate is right - a partial drop has no assembled
top for us to build - but it means the orchestrated backend path is still
unexercised, and the issue below has had no opportunity to bite.

## 1. A timing failure halts the flow instead of routing to the Frontend

`flow.py:722-727`:

```python
if status == "PASS":
    return 0
if rep.get("failed_stage") == "synth" or "synth" in str(rep.get("error_message", "")).lower():
    return 1            # the RTL itself: backend -> frontend edge
return run.halt("backend", f"backend FAILED at {rep.get('failed_stage') or 'unknown'} ...")
```

Only a synthesis failure reaches `stage_backend_to_frontend`. A timing failure
does not: our STA verdict comes back with `sta_status: "FAIL"` and a
`failed_stage` of `null` - the run completed, the check did not pass - so neither
arm of the test matches and it falls through to the halt.

Everything downstream of that branch already works - `stage_backend_to_frontend`
finds our outbox, runs it through `retry_adapter.adapt`, writes the package and
calls `stage_frontend_regeneration`. The edge is built; the trigger is narrower
than the edge.

The exact fields, from our full-chip report, so the condition can be written
against them: `sta_status: "FAIL"`, `failed_stage: null`, `drc_violations: 0`,
`lvs_status: "PASS"`, `error_message` naming the STA soft fail and containing no
"synth". Both arms of the test are false and it halts.

The case this matters for is the one we have: the full chip on drop
`dab971c2aab9` closes DRC with 0 violations and LVS matches, and misses timing at
**WNS -1.044 ns, Fmax 165.5 MHz**, critical path
`u_cmd_queue.entry_bank[34] -> u_scheduler.cmd_row[4]`. The finding is in
`backend/findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/dab971c2aab9/`, owned
by `scheduler`, and adapts cleanly - we have run it through `retry_adapter` and
`to_frontend_error_report` by hand and it renders complete, with both ends of the
path anchored on their own phase files. In a real flow round it would never be
asked for.

## 2. Suggested shape, because not every backend failure is the Frontend's

The useful distinction is not which stage failed but who can act on it:

| failure | whose to fix | route to Frontend? |
|---|---|---|
| synth | Frontend RTL | yes - already does |
| **STA timing** | **Frontend RTL** | **yes - currently halts** |
| DRC / LVS | Backend | no - halting is correct |

A DRC or LVS failure is ours: the RTL is fine and the physical implementation is
not, so sending it to a generator would be asking the wrong subsystem to fix it.
Halting is the right answer there and we would not want that changed.

Two ways to express it, your call:

```python
if rep.get("sta_status") == "FAIL" or rep.get("failed_stage") == "synth" \
        or "synth" in str(rep.get("error_message", "")).lower():
    return 1
```

or, keying on whether we actually produced something routable rather than on a
stage name:

```python
if backend_findings(rev):      # we emitted a finding naming a module
    return 1
```

We slightly prefer the second: it asks the question that matters - did the
backend hand you a change request - and it stays correct if we later emit
findings for failure modes neither of us has thought of. It also fails closed:
no finding, no route, halt as now.

## 3. What is ready on our side

The finding names a block, not the top. A full-chip endpoint is hierarchical
(`u_scheduler.cmd_row[4]`), and naming `ddr3_controller` as the owner would route
to a module no phase agent generates. Since 2026-10-15 we resolve the instance to
a block - verified against the drop's own block list rather than trusting the
`u_` prefix - so the finding arrives as `scheduler/TIMING/cmd_row` with
`owner_candidates: [scheduler, cmd_queue]`, both ends anchored on their phase
files. Its id matches the standalone `scheduler` finding, so your lifecycle sees
one defect rather than two.

`--max-backend-rounds` bounds the loop on your side. On ours, a timing finding is
only emitted when STA fails, so a round that closes emits nothing and the loop
ends naturally.

## 4. Not asking for this one, but worth saying

We have no way yet to report a finding as *resolved*, because we only emit on
failure: a block that failed last drop and passes this one goes quiet rather than
being recorded as fixed. Closing that means emitting a record for every block we
build, pass or fail. It is on our list and it is a change to our pipeline, not a
contract question - raising it only so a silent backend is not read as a clean
one.
