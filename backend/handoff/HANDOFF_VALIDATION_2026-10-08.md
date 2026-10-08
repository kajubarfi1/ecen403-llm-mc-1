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

## 2. What we need from `flow.py`

**`--drop_id` is not passed.** You asked us to name the outbox by drop id, but
`stage_backend` sends only `--bundle_dir`, `--out_root`, `--env_file`. We cannot
compute it ourselves without reaching into `Validation/structural/rtl_drop.py`,
which resolves paths through your `rtl_drop.json` to read the Frontend's files —
backend would be coupled to two other subsystems' layout and would stop running
standalone. You have the id in hand at `flow.py:462`, but `record()` appends it to
`state["stages"][-1]`, not to `run.state`, so it needs carrying across. Two lines
- in `stage_rtl_validation`, after `h` is loaded:

```python
run.state["drop_id"] = h["drop_id"]
```

and in `stage_backend`:

```python
if run.state.get("drop_id"):
    cmd += ["--drop_id", run.state["drop_id"]]
```

Our side accepts it and falls back to `git_head` when it is absent, so the order
of landing does not matter.

**The drop_id confirmation in your own contract is not implemented.**
`HANDOFF_CONTRACT.md` §4 says: read `HANDOFF.json`, confirm `drop_id` equals the id
of the drop just written, *else validation has not run on it yet*. `flow.py` never
computes the drop's id - `rtl_drop.drop_id()` is not called anywhere in it - so
that comparison cannot happen. Combined with the stale-report issue below, a round
where `validate_drop.py` fails without refreshing `outbox/current` would be read as
a verdict on the current drop. This is your call, not a backend need, but it is the
check that would have caught our failure today.

**`stage_backend` can report PASS for a run that failed.** `flow.py:583`:

```python
status = rep.get("pipeline_status", "FAIL" if rc else "PASS")
```

The default fires only when the key is *absent*. A `pipeline_final_report_*.json`
left in `run.backend_dir` by an earlier round has the key, so a stale PASS is
taken over a nonzero `rc`. Suggest keying on `rc` first, and treating a report
older than the round's start as not ours:

```python
if rc != 0:
    status = "FAIL"
```

We hit exactly this on our side today: `pipeline_batch.py` read `exit_code` and
never used it, so eleven blocks that died on import in 0.2s reported PASS with
three-week-old area, power, DRC and LVS attached. It is the fifth place this
pattern has turned up in the backend, and it is the most expensive kind of bug we
have had, because the wrong answer looks like a good one. Worth checking
`stage_rtl_validation` for the same shape.

Related, lower stakes: `reports[0]` from an unsorted `os.listdir` picks an
arbitrary report when `run.backend_dir` holds more than one design, which it will
once a multi-block bundle or a second round writes there.

## 3. `to_frontend_error_report.py` loses three things

Rendering our finding through your chain (`retry_adapter.adapt` →
`write_error_reports`) works — `failed_modules: ["scheduler"]`, phase 3, the
`fix` lands. But `_lines()` at `Validation/findings/to_frontend_error_report.py:40`
drops content the model needs:

| line | what the model sees | why |
|---|---|---|
| 49 | `scheduler.sv:None` | `:{a.get('line')}` is unconditional; your own §3 says timing has no line |
| 49 | `cmd_aux` with no bit, no role | reads `signal` and `text` only — `bit` and `role` never arrive |
| 53 | no `repro:` line at all | reads `rep.get("cmd")`; ours is `repro.command`, which the adapter passes through unchanged |
| 58 | `occurrences: 1 on` | `paths` is empty, leaving a dangling "on" |

The third is the substantive one — the reproduction command never reaches the
Frontend. Your handoff said the adapter accepts `command` or `cmd`, and it does;
the renderer does not.

Nitpick, your call: `retry_adapter.adapt` sets `pipeline: "validation"` on our
findings too. `flow.py` overwrites `source`, so provenance is recoverable — but
a reader of the package alone would attribute a timing defect to validation.

## 4. The drop id is not reproducible off Linux

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
teammate's git is configured, and it cannot be undone by a fresh clone. We are
stamping findings with `4b86c7cd3705`, the team's value, not the one our tree
computes.

## 5. Per-block netlists

Agreed - a top-level netlist has no block path to run on. Running
`pipeline_batch.py` over all 11 blocks of drop `4b86c7cd3705` so
`runner/<block>/6_final.v` exists per block. Multi-hour unattended run; expect them
this week.

Note the bundles these are built from: not `backend/bundles/`, which your handoff
named. That set is months old - up to 506 lines adrift from the current drop per
block - and netlists from it would not correspond to anything you have judged. We
re-cut `backend/bundles_frontend2/` from `rtl_drop`'s own resolution, so all 22
files are byte-identical to the drop and every manifest carries the golden revision.
Worth pointing `flow.py` at that path rather than `bundles/`.

Your `wb_port/6_final.v` result (**19/19** on `path_21_wb_port_standalone`) is the
first behavioural confirmation of a backend netlist we have. Thank you for
chasing the two checker defects rather than filing them against the netlist.

## 6. `--backend-mode`

Yes, please. `contract` / `synth` / `build` / `full`; `build` stays the default.
Mapping is literal - pass the string through to `--mode`.

One correction to our own pitch: `contract` runs no ORFS but is **~20 s per block**,
not seconds, because intake still makes an LLM call per block. Eleven blocks is
about two minutes wall clock at two workers. Dropping that call is on our list; until
then, budget for it rather than treating `contract` as free.

Also worth knowing, since it bears on the stale-report issue in §2: we found a sixth
instance of that pattern today, and this one defeats a freshness check. A
contract-mode run reported WNS, area, Fmax and power for all 11 blocks, taken from
ORFS artifacts dated 2026-09-24 - written into a summary file seconds old. The file
was genuinely fresh; its contents were three weeks stale. Our guard only fired on a
nonzero exit code, and a mode that runs nothing exits 0. If `flow.py` ever trusts a
report's mtime as proof of provenance, that is the hole.
