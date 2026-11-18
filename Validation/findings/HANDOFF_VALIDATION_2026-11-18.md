# Handoff to Validation — 2026-11-18

From Backend (Dawson) to Validation (Jacob), on the GUI's live layout frames
not appearing on the Mac. Three faults were mine and are fixed in `fab5c7eb`.
One thing is left that only you can check, and it may mean the feature cannot
work on your machine at all. Section 4 is unrelated and is yours.

## 1. What was broken, and what `fab5c7eb` fixes

The chip card can show the real layout now — OpenROAD renders each ORFS step's
`.odb` as it lands, so the die, power grid, placement, clock tree and routing
appear as the build produces them. On your Mac you saw none of it, just the
procedural illustration, with nothing saying why. Three separate faults:

**The ORFS image was hardcoded.** `gui/chip_render.py` defaulted to
`openroad/orfs:latest` and `flow_gui` never overrode it, so the renderer kept
starting a container from an image that is not on your machine — yours is
`openroad/orfs:arm64-local` (USAGE, "Running the whole flow on a Mac").
`frames_for` now resolves it as `ORFS_DOCKER_IMAGE` → backend `.env` →
default, the same precedence `flow_gui` already used for `ORFS_DIR` and
`PLATFORM`. Nothing for you to set: your `.env` already has the right value.

**The failure was invisible.** `frame_error` was in the status JSON the whole
time and nothing displayed it, so the page drew the illustration as though no
render had been attempted. The chip card now names the reason when there are
no frames (full text on hover) and the server prints it once per failure.
`chip_render._explain()` turns the common cases into something you can act on
rather than a stack trace.

**`docker_available()` probed once per renderer**, and one renderer is made per
run directory. `docker info` against a busy daemon costs its full 20-second
timeout. It is now cached per process. Symptom that found it: the test suite
went from 35 seconds to 19 minutes on one run.

## 2. The one thing to check — your OpenROAD may have no GUI

USAGE line 525, your own build recipe:

```
./build_openroad.sh --no_init --local --openroad_only --threads 6 \
    --openroad-args -no-gui          # ~13 h on 6 cores
```

The frames are rendered with `gui::save_image`, the same call ORFS's own
`flow/scripts/save_images.tcl` uses for its final report. It is a GUI command.
If `-no-gui` left it out of your binary, no amount of configuration will help.

Please run:

```bash
docker run --rm openroad/orfs:arm64-local bash -c \
  '/OpenROAD-flow-scripts/tools/install/OpenROAD/bin/openroad -version'
```

The second line reads `Features included (+) or not (-):`. The x86 image I
build against prints `+GPU +GUI +Python`.

**If it says `+GUI`** — you are done. Pull `fab5c7eb` and the frames should
appear on your next run. If they still do not, the page will now tell you the
reason in words; send me that line.

**If it says `-GUI`** — the feature cannot work on your machine as built, and
the page will now say exactly that instead of staying silent. Two options, and
I would not reach for the first:

- Re-run that `build_openroad.sh` step without `-no-gui`. Your Bazel cache is
  on the `orfs-bazel` volume, so this is not the 13 hours again — it recompiles
  the GUI module and its Qt dependencies against a warm cache. I do not know
  what that actually costs on your setup and I am not going to invent a figure.
- Let me add a KLayout fallback. KLayout **is** in your image (you install it
  right after the OpenROAD build), and it can render `6_final.gds` directly.
  That gives one real layout at the end of the build instead of a nine-frame
  animation — much less effort, and better than nothing. Say the word.

## 3. What the frames cost when they do work

Measured on the 11-12 balanced build, x86, one CPU per render: 3–6 seconds per
frame, about 1.4 MB each, nine or ten frames per build. Rendering is a
background thread, one frame at a time, in a container capped at `--cpus=1`, so
it does not take cores from the build it is watching. Frames land in
`runs/<run>/chipframes/` and are adopted on reopen rather than re-rendered.
`--no-chip-frames` turns the whole thing off; the demo never uses it.

One deliberate choice worth knowing: the block name labels are suppressed over
a real frame. The treemap's areas are real cell counts but its positions are
invented, so printing `scheduler` across a corner of the actual layout would
assert something nothing knows.

## 4. Unrelated, and yours: stage 4a timed out on Olympus

Not a GUI issue, and I have not touched it — flagging it because it cost an
afternoon and I do not think it has been seen.

On the 11-17 full run (`runs/20261117-120637-balanced`), `rtl_validation` took
**79 minutes**, 69 of them in stage 4a. 20 of the 24 constrained-random runs
came back `INCOMPLETE`, were retried, timed out again, and were discarded:

```
path_03_read_return          s1:PASS  s2:INCOMPLETE  s3:INCOMPLETE  s4:INCOMPLETE
path_04_scheduler_bank_loop  s1:PASS  s2:INCOMPLETE  s3:INCOMPLETE  s4:INCOMPLETE
path_07_backpressure         s1:PASS  s2:INCOMPLETE  s3:INCOMPLETE  s4:INCOMPLETE
path_18_full_write           s1:PASS  s2:INCOMPLETE  s3:INCOMPLETE  s4:INCOMPLETE
path_19_row_conflict         s1:INCOMPLETE  (all four)
path_20_refresh_preempt      s1:INCOMPLETE  (all four)
```

The four that returned are exactly the first wave `--jobs 4` starts. Everything
after it timed out at the 1500-second limit. The same stage ran in **3.6
minutes with 24/24 passing on 11-12**, same code, same spec id.

First wave fine, everything after it dead, looks to me like Xcelium licences or
Olympus load rather than a code regression — but that is a guess from the
outside and it is your call. The directed suite was unaffected (20/20), and the
drop still came out PASS, so nothing was wrongly judged. `--random-seeds 0`
skips the stage if you need a quick loop meanwhile.

## 5. Also in your tree since 11-12

Two changes you made in `backend/` that I have read and am keeping:

- `signoff_runner.py`: your detection fix is right — ORFS `f34d4d9` wraps every
  step as `bash -c '... make ... $@' -- do-<step>`, so my
  `yosys|openroad|klayout` regex matched nothing and make silently rebuilt
  placement through routing inside the 900-second CDL timeout. Good catch.
  I am less sure about turning the refusal into a warning; that guard existed
  so a CDL could never be written against results make considered stale. I am
  leaving it as you have it for now, but I want to think about whether
  `assert_gds_is_current` really covers the case the refusal was for.
- `blackbox_cells.txt`: `ha_4` added, eight cells now compared by pin
  connectivity only. Consistent with the existing entries and detected by
  `detect_blackbox.py`, so no objection — just noting that it is what the
  "8 black-boxed instances" line in the validator report refers to, and that
  LVS is not verifying those cells' internals.

— Dawson
