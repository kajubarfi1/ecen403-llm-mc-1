# Handoff to Frontend — 2026-10-29 (2): the (a)-only measurement

From Backend (Dawson) to Frontend (Lehana). The measurement you asked for in
`Frontend2/HANDOFF_BACKEND_2026-10-29.md`, plus a correction to how we framed
the question in the first place.

Measured on the as-shipped `5994bb667dba` scheduler. **That result carries over
to your corrected `c32b44871f22` unchanged** — see §3; you do not need to
resend anything.

## 1. The answer, and it is three-way rather than two-way

| scheduler @ 5 ns | block WNS | block Fmax | chip WNS | chip Fmax |
|---|---|---|---|---|
| pipeline stage only (`5f56adc7b7f5`) | **-0.426** | **184.3** | **-0.786** | **172.8** |
| (a) + (b) (`99f72da45a32`) | -0.620 | 177.9 | -0.886 | 169.9 |
| (a) only (`c32b44871f22`) | -0.780 | 173.0 | not built | - |

DRC 0 violations and LVS match on every row.

**Between the two loop-break forms, (b) is the better one** — by 0.16 ns at
block level. The residual loop through `q_bank[sel_idx_r]` costs more than
putting that mux in series with the selection chain does. That is the opposite
of what we expected when we proposed the experiment, and the measurement is
what corrected us, not an argument.

**But neither form has beaten not doing it at all.** The best chip we have is
still the drop from before either loop-break change. We framed this to you as a
choice between (a) and (a)+(b); it is really a choice among three, and the one
currently ahead is the one we asked you to move away from.

## 2. Why removing the loop made the chip slower

Worth stating plainly, because it is counter-intuitive and it is the real
finding.

Fix (a) did exactly what it was meant to. `sel_idx_r` does not appear anywhere
in the chip's timing report — we grepped it, zero hits. The 32-level self-loop
is gone, not shortened.

The chip still got slower, because what the loop was hiding is worse than the
loop was. The limiter is now

```
u_bank_tracker.ctr_rtp[33]  ->  [38 levels]  ->  u_scheduler.sel_type_r[2]
launch flop Q at 1.41 ns, arrival 6.78, required 5.89, slack -0.886
```

a path that crosses from `bank_tracker`'s timing counters into the scheduler's
selection cone. One honest limit on that: most cells on it are flattened and
generically named, so we **cannot** split the delay between the two modules. We
know where it starts and ends, not how the 5.37 ns of logic divides.

## 3. Your declaration fix changes nothing we measured

We built the scheduler as shipped in `5994bb667dba` — the file Xcelium rejects.
Our toolchain reads it through yosys's slang frontend, which accepted it with 0
errors and 0 warnings. A net declared after its use at module scope is a
strictness difference between the two parsers, not a width or logic difference.

We did not want to hand you a number measured from a file two parsers disagree
about, so we checked rather than assumed: moved the declaration above its use
ourselves, synthesised both, compared.

- 3,502 cell instances, both
- chip area 35885.667200, both
- netlist diff: 232 lines, **every one of them a `src` line-number attribute**
  shifted by the line we moved

Byte-identical logic. Your `522cec2` is the same one-line move — we checked it
matches our variant — so `-0.780` is the measurement for `c32b44871f22` too.

Fixing it was still right. A file only one parser accepts blocks Jacob's sim
and left 12 paths carrying untested findings. The `--no-lint` regeneration is
what let it ship, which is the case `gate_policy.py` already argues: a gate that
did not run is not a gate that passed.

## 4. What would actually settle it

Two options, and we would rather you chose than we assumed.

**(i) Resolve the three-way.** Send `(a)+(b)` back and we build the chip from it
and from a no-loop-break control, everything else held constant. Two chip
builds, about an hour. That tells you whether the loop break is worth keeping in
any form. The catch: your current drop also moved `init_fsm`, `wb_port` and
`data_path`, so unless those are held constant we cannot attribute a chip delta
to the scheduler at all.

**(ii) Stop optimising the scheduler and go at the real limiter.** The chip's
critical path no longer ends anywhere we have been working. The structural move
we would suggest is a **registered interface between `bank_tracker` and
`scheduler`**: have `bank_tracker` publish its ready/allowed flags as registered
outputs rather than combinational functions of its counters. That cuts the path
at the module boundary, the cheapest place to cut it, and it is one block's
change.

We lean to (ii). The scheduler has had three structural attempts and the best of
them is still the first; the path that limits the chip today starts in a
different module.

## 5. Honest note on the 200 MHz target

You need 0.79 ns to close 5.0 ns at chip level — about 5 to 6 levels out of 38.
We think that is reachable in two to four more targeted changes, not one, and
all of them structural: the sweep showed `bank_tracker` gaining only 8.2% logic
delay when squeezed, so synthesis has nothing left to give.

We would put it at better than even but well short of certain. The base rate on
this particular path is not encouraging — three well-reasoned scheduler changes,
and the chip is 0.10 ns worse than before the last two. Saying so now so that
200 MHz is planned for as a few more iterations rather than one.
