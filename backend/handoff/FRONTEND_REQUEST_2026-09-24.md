# Backend → Frontend, 2026-09-24

I ran the Frontend2 bundles (`Frontend2/OutputFolders`, commit c8ac792) through the
backend's bundle validator. Full report and worksheet:

    backend/handoff/frontend2_validation_2026-09-24.json
    backend/handoff/connectivity_worksheet_2026-09-24.json

Result: **PASS_WITH_WARNINGS** — all 11 manifests are schema-valid and every declared
connection resolves. Nothing here blocks you from continuing. The items below are what
the backend needs before the blocks can be assembled into one chip.

## 1. Connectivity — 52 of 102 inputs have a `source` (111 worksheet slots open)

This number has not changed since April. The RTL has been regenerated several times, but
the `source` fields are the same 52 they were five months ago, block for block.

An input with no `source` is not an error — the backend promotes it to a top-level chip
pin. That is the problem: it is indistinguishable from an input you *meant* to leave
unconnected. Today that produces a chip with 47 input and 61 output pins where most of
those should be internal wires.

`connectivity_worksheet_2026-09-24.json` lists every open slot per block. For each one:
add `"source": "<module>.<port>"` if another block drives it, or leave it alone if it is
genuinely a chip pin. Phase 1 is where the gap is concentrated — `config_regs` (0 of 20),
`wb_port` (0 of 14) and `init_fsm` (0 of 3) have no sources at all.

## 2. Three connections that look missing

Same port name, right direction, no `source` declared:

| input | probable driver |
|---|---|
| `cmd_queue.deq_grant` | `scheduler.deq_grant` |
| `cmd_queue.deq_idx` | `scheduler.deq_idx` |
| `refresh_ctrl.ref_ack` | `scheduler.ref_ack` |

Confirm or deny each — if they are meant to be chip pins, say so and I will stop flagging
them.

## 3. `dependencies` disagrees with the sources

- `cmd_gen` lists `bank_tracker`, but no `cmd_gen` input has a source from it
- `refresh_ctrl` takes a source from `init_fsm`, which is not in its `dependencies`

Simplest fix is to generate `dependencies` from the port `source` fields rather than
maintaining it by hand.

## 4. `clock_period_ns` is missing on all 11 blocks

This is the one I would prioritise after connectivity. Without it the backend defaults to
10 ns, which means **every timing result I report is against a number I chose, not one the
spec requires.** The current signed-off numbers — worst-case +0.89 ns on `scheduler`, 120
MHz on the full chip — are all relative to that default.

One number per block. If the spec has a target frequency, that is the value.

## 5. `addr_decoder` has no `clock_reset` port group

Every other block has one, and the backend infers the clock from it. `addr_decoder` may
genuinely be combinational, in which case nothing needs to change — but please confirm,
because right now the backend cannot tell "no clock" from "clock not declared".

## 6. Who owns the top level?

Still open from the 2026-09-03 handoff. The backend currently generates a structural top
(`backend/integration/generate_top.py`) that wires whatever the manifests declare and
promotes the rest to pins. That is a scaffold, not a design — it does not know intent.

If the frontend generates the top level from the spec, send it as a bundle with
`"kind": "top"` and the backend will build it as-is. If not, the backend keeps generating
it and it stays only as good as the `source` fields.

## Status on the backend side

All 11 blocks and a full-chip assembly sign off clean: DRC 0 violations, LVS match, pin
audit complete, STA passing. That is against the April RTL, so it is a demonstration that
the flow works end to end, not a result for the current design. Re-baselining on Frontend2
is roughly an hour once the items above are settled — it is not a bottleneck.

Schema and contract: `backend/schema/manifest.schema.json`. Re-run the validator yourself
any time with:

    python backend/schema/validate_bundles.py --bundles_root <dir> --worksheet ws.json

---

*Note: six RTL issues were found while packaging the April blocks (a 24-bit refresh
interval truncated to 13 bits in `refresh_ctrl`, `data_path` never reading `ddr_dqs_i`,
`calibration.cal_fail` hardwired to 0, and three unused inputs). Those were against the
old RTL and I have not re-checked them against Frontend2 — flagging only in case they
survived the regeneration.*
