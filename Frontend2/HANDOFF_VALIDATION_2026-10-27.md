# Handoff to Validation — 2026-10-27

From Frontend (Lehana) to Validation (Jacob). Not a reply to an open ask —
a self-audit of `Validation/findings/HANDOFF_CONTRACT.md` against our own
code, one gap found and fixed.

## 1. `drop.py`'s `compute_drop_id` was missing the CRLF normalization

Contract §2 says bytes are hashed with CRLF normalised to LF, and
`rtl_drop.py:drop_id()` does it — but `Frontend2/scripts/drop.py`'s own
`compute_drop_id`, the function `full_pipeline.py` prints as "matches
Validation's" and `Orchestrator/orchestrator_agent.py` uses to check its
drop against `outbox/current/HANDOFF.json`, hashed raw bytes with no
normalization. Same bug class as the backend's `ec49d485ca8d` vs
`4b86c7cd3705` incident on 2026-10-08 — ours just hadn't been hit yet
because every machine we'd run it on so far checked out LF. Fixed with
the same `.replace(b"\r\n", b"\n")` your reference implementation uses.

Verified against your code, not just the contract text: ran both
`drop.compute_drop_id("Frontend2/OutputFolders")` and `rtl_drop.drop_id()`
against the same tree and got the same id (`efece348d04e`) before and
after confirming the fix doesn't change behavior on our LF checkouts.
`tests/test_flow.py` (40 tests) still passes — none of it touches
`compute_drop_id` directly, so this was a silent gap, not a caught one.

Everything else in the contract — the 11-block set (§2), `HANDOFF.json`'s
`design_id`/`spec_id` (§4), and the `confirmed`/`observed`/`unverified`
confidence split with `--yes` acting on `confirmed` only (§5) — was
already correct on our side; no other changes.

Nothing to ask here. Flagging so you know why our drop id agreed with
yours on every run so far and the mechanism that was waiting to bite.
