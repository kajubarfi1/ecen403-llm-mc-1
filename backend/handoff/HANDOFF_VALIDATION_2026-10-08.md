# Handoff to Validation — 2026-10-08

From Backend (Dawson) to Validation (Jacob), answering
`Validation/findings/HANDOFF_BACKEND_2026-10-07.md`. Anchors are done and the
whole chain is verified end to end. Four things need a change on your side and
one needs the Frontend. Nothing outside `backend/` was changed by us.

## 1. Anchors — done

`backend/findings/emit_findings.py` now anchors on the drop's phase copy, found
by looking rather than from the manifest, and names the signal at both ends of
the critical path:

```json
"anchor": [
  {"file": "Frontend2/OutputFolders/PHASE3RTL/scheduler.sv",
   "signal": "cmd_aux", "bit": 3,  "role": "endpoint"},
  {"file": "Frontend2/OutputFolders/PHASE3RTL/scheduler.sv",
   "signal": "q_bank",  "bit": 33, "role": "startpoint"}
]
```

`bit` and `role` are additive — a consumer reading only `file` and `signal` is
unaffected. Both ends are given because a timing fix usually needs both: the
endpoint is the register that misses, the startpoint is where its path begins.

**Do not trust a manifest's `phase` field.** On the current drop
`backend/bundles/data_path/data_path_manifest.json` still says `phase: 3` while
the block lives in `PHASE4RTL`. We resolve by globbing `PHASE*RTL/<file>` in the
drop root and never choosing `TOPRTL/`, per the contract §1. Verified: all 11
blocks resolve, `data_path` to PHASE4RTL, and a bundle that *is* `<drop>/TOPRTL`
(how `flow.py` invokes us) still resolves to the phase copy.

**One-time id change.** Finding ids were keyed on the indexed endpoint
(`TIMING/cmd_row[5]`); they are now keyed on the signal alone
(`TIMING/cmd_aux`). The bit moves between runs while the defect does not, so the
old form broke lifecycle tracking the same way the synthesis suffix did. The
first drop after this change will read as "old resolved, new opened" once. It
coincides with the spec-revision change in §3, so the outbox is being
regenerated anyway.

## 2. What you have already done, and the two left

Checked against main at `9e51329` before writing this - an earlier version of this
file asked for things you had already fixed, which was our failure to re-read.

**Done, thank you:** `run.state["drop_id"] = h["drop_id"]` at `flow.py:462` and both
`--drop_id` and `--spec_revision` passed at `flow.py:580`, plus `--backend-mode`.
Our first finding from a real run landed in
`backend/findings/outbox/golden_ddr3_1600k_x8_2lane_1rank/4b86c7cd3705/` because of
it. And every defect we reported in `to_frontend_error_report.py` is fixed in
`8d5770e` - `repro.command` is read, the anchor no longer prints `:None`, `bit` and
`role` survive, and the dangling `occurrences: N on` is gone. We re-rendered our
scheduler finding through your chain and it comes out complete.

Two things are still open in `stage_backend`.

**`reports[0]` from an unsorted listdir** (`flow.py:585`):

```python
reports = [... for f in os.listdir(run.backend_dir) if f.startswith("pipeline_final_report_")]
```

With one design per run directory this is fine. The moment a multi-block bundle or a
second round writes there, it picks an arbitrary report and attributes it to the
stage. Sorting is not the fix either - the right report is the one for the design
that was run.

**A stale report still outranks `rc`** (`flow.py:590`):

```python
status = rep.get("pipeline_status", "FAIL" if rc else "PASS")
```

The default fires only when the key is absent, so a report left by an earlier round
makes the stage report PASS over a nonzero `rc`. We hit the identical bug in our own
batch on 2026-10-08: eleven blocks died on import in 0.2s and reported PASS with
three-week-old DRC, LVS, area and power attached. `if rc != 0: status = "FAIL"` ahead
of that line closes it.

Worth knowing how far that pattern goes, because it bit us twice more the same day. A
mode that runs no ORFS exits 0, so our own exit-code guard never fired and a
contract-mode run reported metrics read from month-old artifacts - through a summary
file written seconds earlier, so an mtime check could not catch it either. And our
per-block emitter, writing into one shared drop folder, treated a sibling block's
findings as the previous drop's: with two failing blocks only the last survived and
the first was recorded as resolved. All three are fixed on our side. If `flow.py`
ever treats a file's freshness as proof of its provenance, that is the shape to look
for.

## 3. Resolution needs a pass signal, and we cannot give it yet

One limitation to declare rather than have you discover it.

We emit a finding only when a block fails. So when a block that failed last drop
passes this one, nothing is written and its finding stays `open` forever - it is
never recorded as resolved. The reverse is now handled: resolution is scoped to the
modules an emission actually speaks for, so a block that was not built is no longer
reported as fixed. But a genuine fix will also not be reported, which is the worse
half.

Closing it means emitting a record for every block we build, pass or fail, so the
outbox carries results rather than only complaints. That is a change to our pipeline
rather than a contract question, and it is next on our list. Until then, treat an
open backend finding as "open as of the last drop that failed it", and `0` findings
from us as "nothing failed", not "everything we previously reported is fixed".

If `untested_in_this_drop` is the right place for the modules we did not build, say
so and we will populate it.

## 4. The drop id: not reproducible off Linux, and it churns

Resolved first: the `compiled_ddr3800_x8_1lane_1rank` revision we flagged earlier
today is gone. The drop is back on `golden_ddr3_1600k_x8_2lane_1rank`, so the
200 MHz target stands and our bundles are on the right spec. We also removed the
stale `SPEC_REVISION` default that would have written findings to a folder nothing
reads while looking like success; it now takes `--spec_revision` and warns when it
has neither.

But the id itself does not survive a Windows checkout. `drop_id()` hashes raw file
bytes, this repo has no `.gitattributes`, and git hands a Windows clone CRLF:

| computed on | drop id |
|---|---|
| our checkout, as git delivered it | `ec49d485ca8d` |
| the same tree, LF-normalised | `4b86c7cd3705` |
| Frontend's published value | `4b86c7cd3705` |

So `HANDOFF_CONTRACT.md` §2 - "Same files always get the same id; one changed byte
is a new drop" - holds only within one line-ending convention, and Frontend's claim
that their id "equals `rtl_drop.drop_id()` on this tree" is true on Olympus and
false on either of our laptops. Anything comparing a locally computed id against a
published one therefore always sees a mismatch, which is the failure mode that
looks like a stale drop when nothing is stale.

Two fixes, either is fine, yours to choose:

```python
data = open(p, "rb").read().replace(b"
", b"
")   # in drop_id(), or
```

```
*.sv   text eol=lf        # .gitattributes
*.json text eol=lf
```

We prefer the normalise in `drop_id()`: it is correct regardless of how any
teammate's git is configured, and it cannot be undone by a fresh clone.

Second point, separate from the line endings. `a7cd3cb93546` supersedes
`4b86c7cd3705`, and **the RTL is identical between them** - all 11 blocks match byte
for byte once the `// Generated:` header line is discounted. The id moved because the
hash covers that timestamp and the regenerated manifests. So a new drop id does not
imply a changed design, and re-running the generators with no spec change always
mints one.

That matters for your side more than ours. A stale-drop check keyed on the id will
fire on a no-op regeneration, and findings carried across such a drop look like they
were re-tested against new RTL when nothing was rebuilt. If it is useful, we can
publish the RTL-only hash the backend computes alongside the drop id, so there is a
value that answers "did the design change" as distinct from "are these the same
bytes". Say the word and we will add it to the findings envelope.

We are stamping findings with the team's published id, not the one our tree computes.

## 5. Per-block netlists - delivered

All 11 are built, from drop `4b86c7cd3705` (RTL identical to `a7cd3cb93546`, see §4):
`agents/pipeline_out/runner/<block>/6_final.v`. 42 minutes wall clock, 11 blocks,
`build` mode. Point `run_path.py --netlist` at those.

Not from `backend/bundles/`, which your handoff named - that set is months old, up to
506 lines adrift per block, and netlists from it would correspond to nothing you have
judged. We re-cut `backend/bundles_frontend2/` from `rtl_drop`'s own resolution, so
all 22 files are byte-identical to the drop. Worth pointing `flow.py` there.

**And the timing answer you have been waiting on. Ten of eleven blocks close at
200 MHz.** DRC 0 violations and LVS PASS on all eleven:

| block | Fmax | WNS @ 5 ns | |
|---|---|---|---|
| calibration | 416.8 | +2.601 | |
| cmd_gen | 378.8 | +2.360 | |
| init_fsm | 317.1 | +1.846 | |
| config_regs | 280.8 | +1.439 | |
| cmd_queue | 277.7 | +1.399 | |
| refresh_ctrl | 265.4 | +1.232 | |
| wb_port | 249.0 | +0.983 | |
| data_path | 224.1 | +0.537 | |
| bank_tracker | 214.3 | +0.334 | |
| **scheduler** | **169.1** | **-0.915** | misses |
| addr_decoder | n/a | n/a | combinational, no timing paths |

Two cautions on reading that as good news. `bank_tracker` and `data_path` close with
0.33 ns and 0.54 ns of margin, and the top level has to add clock distribution and
inter-block wiring on top; a block that closes standalone at 214 MHz is not a block
that closes in the assembled controller. And this supersedes every timing number we
reported before 2026-09-24 - nine of those were measured at a 10 ns period, where
closing means nothing for this target.

`scheduler` is the one real defect, and §1's finding is the routable version of it.

Your `wb_port/6_final.v` result (**19/19** on `path_21_wb_port_standalone`) is the
first behavioural confirmation of a backend netlist we have. Thank you for chasing
the two checker defects rather than filing them against the netlist.

## 6. `--backend-mode` - done on your side

`flow.py:581` passes it. One correction to our own pitch: `contract` runs no ORFS but
is **~20 s per block**, not seconds, because intake still makes an LLM call each.
Eleven blocks is about two minutes at two workers. Dropping that call is on our list;
until then budget for it rather than treating `contract` as free.
