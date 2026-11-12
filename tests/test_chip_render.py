#!/usr/bin/env python3
"""gui/chip_render.py -- the real per-step layout frames.

Rendering itself needs Docker and a built design, so it is not exercised here.
What is pinned is everything around it, which is where a frame feature can hurt
a page that must keep answering: the status path never blocks on Docker, a
missing or broken renderer costs nothing, frames already on disk are adopted
instead of re-rendered, and a frame name out of a URL can only ever name a file
inside the frame directory.
"""

import os
import sys
import tempfile
import time
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "gui"))
import chip_render as cr  # noqa: E402

PNG = b"\x89PNG\r\n\x1a\n" + b"\0" * 4000      # big enough to pass the size floor


class FrameTable(unittest.TestCase):

    def test_every_frame_names_a_real_backend_step(self):
        import flow_gui
        keys = {k for k, _l, _w in flow_gui.BACKEND_STEPS}
        for stem, step, label in cr.FRAMES:
            self.assertIn(step, keys, f"{stem} claims step {step!r}")
            self.assertTrue(label and label[0].isupper(), f"{stem} label: {label!r}")

    def test_frames_are_in_build_order(self):
        """The page shows the last frame, so the list order is the timeline."""
        stems = [s for s, _k, _l in cr.FRAMES]
        self.assertEqual(stems, sorted(stems, key=lambda s: cr.FRAME_ORDER[s]))
        self.assertEqual(stems[0], "2_1_floorplan")
        self.assertEqual(stems[-1], "6_final")

    def test_synthesis_has_no_frame(self):
        """1_synth is a netlist: there is no geometry to draw."""
        self.assertNotIn("1_synth", cr.FRAME_ORDER)


class Paths(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chipframe-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.c = cr.ChipFrames("/nowhere", "sky130hd", self.tmp)

    def test_frame_path_only_resolves_png_in_the_frame_dir(self):
        with open(os.path.join(self.tmp, "3_place.png"), "wb") as f:
            f.write(PNG)
        self.assertTrue(self.c.frame_path("3_place.png"))
        for bad in ("../../flow.log", "..\\secrets.png", "/etc/passwd",
                    "3_place.png/../../x.png", "a b.png", "", None, "3_place.txt"):
            self.assertIsNone(self.c.frame_path(bad), f"accepted {bad!r}")

    def test_frame_path_is_none_for_a_name_with_no_file(self):
        self.assertIsNone(self.c.frame_path("6_final.png"))

    def test_docker_path_is_absolute_with_forward_slashes(self):
        p = cr._docker_path(self.tmp)
        self.assertNotIn("\\", p)
        self.assertTrue(os.path.isabs(self.tmp))


class Adoption(unittest.TestCase):
    """A reopened page must not re-render a finished build."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chipframe-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.frames = os.path.join(self.tmp, "frames")
        self.base = os.path.join(self.tmp, "orfs", "flow", "results", "sky130hd",
                                 "ddr3_controller", "base")
        os.makedirs(self.frames)
        os.makedirs(self.base)
        self.c = cr.ChipFrames(os.path.join(self.tmp, "orfs"), "sky130hd", self.frames)
        self.c.enabled = False          # never reach for Docker in a test

    def _pair(self, stem, png=PNG, png_newer=True):
        odb = os.path.join(self.base, stem + ".odb")
        with open(odb, "wb") as f:
            f.write(b"\0" * 10)
        p = os.path.join(self.frames, stem + ".png")
        with open(p, "wb") as f:
            f.write(png)
        t = os.path.getmtime(odb)
        os.utime(p, (t + 10, t + 10) if png_newer else (t - 10, t - 10))
        return p

    def test_existing_frames_are_adopted(self):
        self._pair("3_place")
        self._pair("4_1_cts")
        self.c._adopt(self.base)
        got = {f["stem"] for f in self.c.done.values()}
        self.assertEqual({"3_place", "4_1_cts"}, got)
        self.assertEqual(0.0, self.c.done["3_place"]["render_s"])

    def test_a_frame_older_than_its_odb_is_not_adopted(self):
        """A new build wrote the step again: the old picture is not of it."""
        self._pair("3_place", png_newer=False)
        self.c._adopt(self.base)
        self.assertEqual({}, self.c.done)

    def test_an_empty_frame_is_not_adopted(self):
        """save_image writes a 108-byte PNG when the view collapses."""
        self._pair("3_place", png=b"\x89PNG\r\n\x1a\n" + b"\0" * 50)
        self.c._adopt(self.base)
        self.assertEqual({}, self.c.done)

    def test_adopted_frames_are_not_queued_for_render(self):
        self._pair("3_place")
        self.c.enabled = True           # pretend Docker is there
        self.c.poll("ddr3_controller", since=0)
        self.assertTrue(self.c.q.empty(), "re-rendered a frame already on disk")

    def test_poll_returns_frames_in_build_order(self):
        for s in ("5_1_grt", "2_4_floorplan_pdn", "3_place"):
            self._pair(s)
        self.c.enabled = True
        got = [f["stem"] for f in self.c.poll("ddr3_controller", since=0)]
        self.assertEqual(["2_4_floorplan_pdn", "3_place", "5_1_grt"], got)


class NeverBlocks(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="chipframe-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))

    def test_poll_does_not_wait_on_the_docker_probe(self):
        """status() calls poll(); a daemon that is starting must not stall the
        page while `docker info` sits there."""
        slow = []

        def fake():
            slow.append(1)
            time.sleep(3)
            return False
        real, cr.docker_available = cr.docker_available, fake
        self.addCleanup(lambda: setattr(cr, "docker_available", real))
        c = cr.ChipFrames("/nowhere", "sky130hd", self.tmp)
        t0 = time.time()
        for _ in range(3):
            c.poll("ddr3_controller", since=0)
        self.assertLess(time.time() - t0, 1.0, "poll() blocked on the probe")
        self.assertIsNone(c.enabled, "probe should still be running")

    def test_poll_is_empty_and_quiet_without_docker(self):
        c = cr.ChipFrames("/nowhere", "sky130hd", self.tmp)
        c.enabled = False
        self.assertEqual([], c.poll("ddr3_controller", since=0))

    def test_poll_is_empty_when_the_design_is_unknown(self):
        c = cr.ChipFrames("/nowhere", "sky130hd", self.tmp)
        c.enabled = True
        self.assertEqual([], c.poll(None, since=0))


class WatcherIntegration(unittest.TestCase):

    def test_watcher_can_turn_frames_off(self):
        import flow_gui
        tmp = tempfile.mkdtemp(prefix="chipframe-")
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        w = flow_gui.Watcher(tmp, chip_frames=False)
        self.assertFalse(w.chip_frames)
        self.assertIsNone(w.frames_for(tmp))

    def test_frame_file_refuses_a_run_with_no_renderer(self):
        import flow_gui
        tmp = tempfile.mkdtemp(prefix="chipframe-")
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        w = flow_gui.Watcher(tmp, chip_frames=False)
        self.assertIsNone(w.frame_file("nope", "3_place.png"))




class SharedReads(unittest.TestCase):
    """Reading a log must never block ORFS renaming it (2026-11-12)."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="sharedread-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        self.src = os.path.join(self.tmp, "5_2_route.tmp.log")
        self.dst = os.path.join(self.tmp, "5_2_route.log")

    def _rename_while_open(self, opener):
        with open(self.src, "wb") as f:
            f.write(b"[INFO DRT-0199] Number of violations = 0.\n")
        handle = opener(self.src)
        try:
            os.replace(self.src, self.dst)      # what ORFS's `mv` does
            return True
        except OSError:
            return False
        finally:
            handle.close()

    def test_open_shared_does_not_block_a_rename(self):
        import flow_gui
        self.assertTrue(self._rename_while_open(flow_gui.open_shared),
                        "a reader still blocks ORFS renaming its step log")

    @unittest.skipUnless(sys.platform == "win32", "only Windows locks on rename")
    def test_the_bug_this_guards_is_real(self):
        """Without the share flags the rename fails -- this is the failure
        that killed the 2026-11-12 run after routing had already passed."""
        self.assertFalse(self._rename_while_open(lambda p: open(p, "rb")))

    def test_read_tail_still_reads(self):
        import flow_gui
        with open(self.src, "wb") as f:
            f.write(b"x" * 100 + b"violations = 7\n")
        self.assertIn("violations = 7", flow_gui.read_tail(self.src))

    def test_read_tail_is_quiet_about_a_missing_file(self):
        import flow_gui
        self.assertEqual("", flow_gui.read_tail(os.path.join(self.tmp, "nope.log")))

if __name__ == "__main__":
    unittest.main(verbosity=2)
