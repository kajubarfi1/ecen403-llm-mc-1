#!/usr/bin/env python3
"""Render the real layout, one frame per ORFS step, while the build runs.

ORFS writes a complete OpenDB (`.odb`) into `results/<platform>/<design>/base/`
as each step finishes, and that directory is bind-mounted from the host, so the
frames of a build appear on disk while it is still going. This renders each one
with OpenROAD's own headless GUI (`gui::show "source ..." false` plus
`save_image`, the same mechanism ORFS's own `scripts/save_images.tcl` uses for
its final report), so the picture is the design as the tool holds it -- not a
drawing of one.

Every frame is saved with an explicit `-area` taken from the die, not from
`gui::fit`. Two reasons: fit would scale each frame to whatever happens to be
placed, so the die would jump between frames of one build, and at
`2_1_floorplan` nothing is placed at all -- fit then collapses to a point and
`save_image` writes a 108-byte empty PNG (measured 2026-11-12).

Rendering is a background thread, one frame at a time, in a container capped at
one CPU: a build is usually running while this works, and the renders must not
take cores from it. Everything degrades to nothing if Docker is unavailable --
the caller just gets an empty frame list.
"""

from __future__ import annotations

import os
import queue
import re
import shutil
import subprocess
import threading
import time

# ORFS step databases worth a frame, in build order: the ODB stem, the backend
# step it belongs to, and the caption. 1_synth is deliberately absent -- it is
# a netlist with no geometry, so there is nothing to draw.
FRAMES = [
    ("2_1_floorplan",       "floorplan", "Die and rows"),
    ("2_4_floorplan_pdn",   "floorplan", "Power grid"),
    ("3_1_place_gp_skip_io", "place",    "Cells placed, first pass"),
    ("3_3_place_gp",        "place",     "Global placement"),
    ("3_place",             "place",     "Placement legalized"),
    ("4_1_cts",             "cts",       "Clock tree"),
    ("5_1_grt",             "grt",       "Global routing"),
    ("5_2_route",           "route",     "Detailed routing"),
    ("6_1_fill",            "finish",    "Fill cells"),
    ("6_final",             "finish",    "Final layout"),
]
FRAME_ORDER = {stem: i for i, (stem, _k, _l) in enumerate(FRAMES)}
FRAME_META = {stem: (k, lab) for stem, k, lab in FRAMES}

# microns per pixel; the sky130 controller die is ~825um, so this is ~1000px
DEFAULT_RESOLUTION = 0.82

_TCL = r"""
set a [[ord::get_db_block] getDieArea]
set x1 [ord::dbu_to_microns [$a xMin]]
set y1 [ord::dbu_to_microns [$a yMin]]
set x2 [ord::dbu_to_microns [$a xMax]]
set y2 [ord::dbu_to_microns [$a yMax]]
gui::clear_highlights -1
gui::clear_selections
gui::set_display_controls "*" visible false
gui::set_display_controls "Layers/*" visible true
gui::set_display_controls "Nets/*" visible true
gui::set_display_controls "Instances/*" visible true
gui::set_display_controls "Shape Types/*" visible true
gui::set_display_controls "Misc/Instances/Pins" visible true
save_image -area [list $x1 $y1 $x2 $y2] -resolution RESOLUTION /out/OUTNAME
"""

OPENROAD = "/OpenROAD-flow-scripts/tools/install/OpenROAD/bin/openroad"


def _docker_path(p):
    """A host path Docker will accept: absolute, forward slashes, drive kept."""
    return os.path.abspath(p).replace("\\", "/")


def docker_available():
    if not shutil.which("docker"):
        return False
    try:
        return subprocess.run(["docker", "info"], capture_output=True,
                              timeout=20).returncode == 0
    except Exception:
        return False


class ChipFrames:
    """Renders step frames for one design, in the background, at most one at a
    time. `poll()` is cheap and never blocks: it queues whatever is new and
    returns what has finished rendering so far."""

    def __init__(self, orfs_dir, platform, out_dir, image="openroad/orfs:latest",
                 resolution=DEFAULT_RESOLUTION, cpus="1"):
        self.orfs_dir = orfs_dir
        self.platform = platform
        self.out_dir = out_dir
        self.image = image
        self.resolution = resolution
        self.cpus = cpus
        self.q = queue.Queue()
        self.done = {}          # stem -> {"file","label","step","mtime","t"}
        self.queued = set()     # stem+mtime already seen
        self.lock = threading.Lock()
        self.enabled = None     # None = still probing, False = no Docker
        self._probing = False
        self.last_error = None
        self.worker = None

    def _probe(self):
        self.enabled = docker_available()
        if not self.enabled:
            self.last_error = "docker unavailable"

    # -- discovery ------------------------------------------------------------

    def results_dir(self, design):
        return os.path.join(self.orfs_dir, "flow", "results", self.platform, design, "base")

    def poll(self, design, since=0.0):
        """Queue any step database written since `since` that has no frame yet,
        and return the frames that exist, in build order."""
        # `docker info` is a subprocess and can hang for seconds on a daemon
        # that is starting; status() is on the page's poll path and must never
        # wait on it. Probe once, on the worker thread, and serve whatever is
        # already rendered until the answer comes back.
        if self.enabled is None and not self._probing:
            self._probing = True
            threading.Thread(target=self._probe, daemon=True).start()
        if self.enabled is False or not design:
            return []
        base = self.results_dir(design)
        if not os.path.isdir(base):
            return []
        self._adopt(base)
        for stem, _step, _label in FRAMES:
            p = os.path.join(base, stem + ".odb")
            try:
                mt = os.path.getmtime(p)
            except OSError:
                continue
            if mt < since - 1:          # a previous build's leftovers
                continue
            key = (stem, int(mt))
            with self.lock:
                if key in self.queued:
                    continue
                self.queued.add(key)
            self.q.put((design, stem, mt))
            self._ensure_worker()
        with self.lock:
            out = sorted(self.done.values(), key=lambda f: FRAME_ORDER.get(f["stem"], 99))
        return out

    def _adopt(self, base):
        """Take up frames a previous session already rendered for this run.
        Without this, reopening the page re-renders every step of a finished
        build -- half a minute of needless work, and a flicker while the
        frames come back one at a time."""
        if getattr(self, "_adopted", False):
            return
        self._adopted = True
        for stem, step, label in FRAMES:
            png = os.path.join(self.out_dir, stem + ".png")
            odb = os.path.join(base, stem + ".odb")
            try:
                pt, ot = os.path.getmtime(png), os.path.getmtime(odb)
            except OSError:
                continue
            if pt < ot or os.path.getsize(png) < 1024:
                continue            # stale against a newer build, or empty
            with self.lock:
                self.done.setdefault(stem, {"stem": stem, "file": stem + ".png",
                                            "label": label, "step": step,
                                            "mtime": ot, "render_s": 0.0})
                self.queued.add((stem, int(ot)))

    # -- rendering ------------------------------------------------------------

    def _ensure_worker(self):
        if self.worker and self.worker.is_alive():
            return
        self.worker = threading.Thread(target=self._run, daemon=True)
        self.worker.start()

    def _run(self):
        while True:
            try:
                design, stem, mt = self.q.get(timeout=5)
            except queue.Empty:
                return
            while self.enabled is None:      # the probe has not answered yet
                time.sleep(0.5)
            if self.enabled is False:        # nothing here can be rendered
                return
            try:
                self._render(design, stem, mt)
            except Exception as e:                       # never kill the page
                self.last_error = f"{type(e).__name__}: {e}"

    def _render(self, design, stem, mt):
        os.makedirs(self.out_dir, exist_ok=True)
        out_name = f"{stem}.png"
        tcl = (_TCL.replace("RESOLUTION", str(self.resolution))
                   .replace("OUTNAME", out_name))
        odb = f"/orfs/flow/results/{self.platform}/{design}/base/{stem}.odb"
        # Both scripts go in the frame directory, which is already mounted
        # read-write. Passing them on stdin instead would need `docker run -i`
        # and quoting Tcl through `bash -lc`; a file needs neither.
        inner = os.path.join(self.out_dir, f"_render_{stem}.tcl")
        outer = os.path.join(self.out_dir, f"_go_{stem}.tcl")
        with open(inner, "w", encoding="utf-8", newline="\n") as f:
            f.write(tcl)
        with open(outer, "w", encoding="utf-8", newline="\n") as f:
            f.write(f"read_db {odb}\n"
                    f'gui::show "source /out/_render_{stem}.tcl" false\n')
        cmd = ["docker", "run", "--rm", f"--cpus={self.cpus}",
               "-e", "QT_QPA_PLATFORM=offscreen",
               "-v", f"{_docker_path(self.orfs_dir)}:/orfs:ro",
               "-v", f"{_docker_path(self.out_dir)}:/out",
               self.image,
               OPENROAD, "-no_init", "-exit", f"/out/_go_{stem}.tcl"]
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
        for tmp in (inner, outer):
            try:
                os.remove(tmp)
            except OSError:
                pass
        path = os.path.join(self.out_dir, out_name)
        if proc.returncode != 0 or not os.path.exists(path):
            self.last_error = (proc.stderr or proc.stdout or "render failed").strip()[-300:]
            return
        if os.path.getsize(path) < 1024:
            # fit collapsed, or the step has nothing to draw: not a frame
            try:
                os.remove(path)
            except OSError:
                pass
            return
        step, label = FRAME_META.get(stem, ("route", stem))
        with self.lock:
            self.done[stem] = {"stem": stem, "file": out_name, "label": label,
                               "step": step, "mtime": mt, "render_s": round(time.time() - t0, 1)}

    # -- serving --------------------------------------------------------------

    def frame_path(self, name):
        """Resolve a frame name from the URL to a file, refusing anything else."""
        if not re.fullmatch(r"[0-9A-Za-z_]+\.png", name or ""):
            return None
        p = os.path.join(self.out_dir, name)
        return p if os.path.isfile(p) else None

    def reset(self):
        with self.lock:
            self.done.clear()
            self.queued.clear()
