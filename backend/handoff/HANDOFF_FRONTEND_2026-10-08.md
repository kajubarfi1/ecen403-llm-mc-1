# Handoff to Frontend — 2026-10-08

From Backend (Dawson) to Frontend, on drop `4b86c7cd3705`
(`Frontend2/OutputFolders`, rev `golden_ddr3_1600k_x8_2lane_1rank`). Three things:
one bug in the drop, one caveat on the drop id, and where the backend stands on
timing. Nothing in `Frontend2/` was changed by us.

## 1. Thank you for the single-spec drop

The mixed-revision tree was costing us real time. All 11 manifests now carry the
golden revision, `TOPRTL` matches the phase outputs, and we have re-cut our bundles
straight from `rtl_drop`'s resolution - all 22 files byte-identical to yours. The
earlier `compiled_ddr3800_x8_1lane_1rank` revision had us ready to flag a speed-bin
change; that is withdrawn, the 200 MHz target stands.

## 2. `data_path_manifest.json` says the wrong phase

In this drop - the freshly regenerated one, not a stale copy:

```
Frontend2/OutputFolders/PHASE4RTL/data_path.sv          <- the file
Frontend2/OutputFolders/PHASE4RTL/data_path_manifest.json: "phase": 3
```

Every other block agrees with its directory; `data_path` is the one that does not.
It is the Phase 3 -> Phase 4 move showing up in the generator's manifest field but
not in whatever writes it.

This is low-stakes for us now only because we stopped trusting the field. Our
findings have to anchor on the file the frontend regenerates, so we resolve a block
to its phase copy by globbing `PHASE*RTL/<block>.sv` in the drop rather than reading
`phase` from the manifest - per the handoff contract, never choosing `TOPRTL/`. Had
we trusted it, every `data_path` finding we emit would have pointed at a PHASE3RTL
path that does not exist, and the agent reading it would have had nowhere to go.

Anything else keying off `phase` is exposed the same way.

## 3. Your drop id reproduces only on Linux

`4b86c7cd3705` is correct on Olympus. It is not what the same tree computes on a
Windows clone:

| computed on | drop id |
|---|---|
| our checkout, as git delivered it | `ec49d485ca8d` |
| the same tree, LF-normalised | `4b86c7cd3705` |
| your published value | `4b86c7cd3705` |

`drop_id()` hashes raw bytes, the repo has no `.gitattributes`, and git gives a
Windows clone CRLF. So "it equals `rtl_drop.drop_id()` on this tree" is true where
you ran it and false where we did, and the orchestrator's stale-drop check -
`HANDOFF_CONTRACT.md` §2, the whole point of which is comparing like with like -
would report a mismatch on a drop that is identical.

We have raised it with Validation, since `drop_id()` is theirs; the fix is a
one-line normalise in that function or a `.gitattributes` pinning `*.sv` and
`*.json` to LF. Flagging it to you because `Frontend2/scripts/drop.py` computes the
same hash and will disagree with itself across machines for the same reason. We are
stamping our findings `4b86c7cd3705` either way.

## 4. Where the backend stands on 200 MHz

Honest state, so nobody plans around a number we have not measured.

`scheduler` misses: **WNS -0.95 ns at a 5.0 ns period, Fmax 168 MHz**, consistent
across two earlier RTL generations. Stated with one caveat: that figure comes from a
build we cannot now trace to a specific bundle, because the ORFS design directory has
been overwritten since. It has not yet been reproduced on *this* drop's `scheduler`.
The run in progress will confirm or revise it, and we will send the number either way.
We tested the fix we suggested to Lehana - replacing the
serial priority chains with a tree encoder - on a copy, and it recovers only
**0.13 ns of the 0.92 ns needed**, about 14%. Our original diagnosis was wrong: the
chains were never the bottleneck. The time is in the bank-state lookup and 15-bit row
compare *before* selection (~1.9 ns) and the 16-way 15-bit output mux on
`cmd_row`/`cmd_col` *after* it (~3.1 ns), which a cheaper encoder does not touch.

Closing 200 MHz on `scheduler` needs a pipeline stage - register the classification,
or register `sel_idx` and mux the outputs the next cycle. Either costs a cycle of
latency and changes the `cmd_queue` protocol, so it is a spec decision rather than an
RTL cleanup, and it is worth a three-way conversation before anyone implements it.

The tree encoder is still worth taking on its own terms: 0.13 ns for 1.6% area with
no interface change. Just not as the answer.

**The other ten blocks are unmeasured at 5.0 ns.** Nine of our timing reports predate
the period change from 10 ns, where closing is easy and the numbers mean nothing for
this target. A run over all 11 blocks of this drop is in progress; until it lands,
treat `scheduler` as the only block known to miss and the rest as unknown, not as
passing.
