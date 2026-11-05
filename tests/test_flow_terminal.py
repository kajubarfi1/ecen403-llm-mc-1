#!/usr/bin/env python3
"""gui/flow_terminal.py and the page's terminal endpoints. A stand-in
script plays flow.py, so nothing here starts a real run."""

import base64
import http.client
import json
import os
import shutil
import sys
import tempfile
import time
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "gui"))
import flow_gui  # noqa: E402
import flow_terminal  # noqa: E402

FAKE_FLOW = r'''
import sys, time
print("tty", sys.stdin.isatty(), sys.stdout.isatty(), "args", sys.argv[1:], flush=True)
if "--sleep" in sys.argv:
    time.sleep(60)
line = input("name? ")
print("got", line, flush=True)
'''


def wait_for(term, text, secs=10):
    end = time.time() + secs
    while time.time() < end:
        out = term.read(0)[0].decode("utf-8", "replace")
        if text in out:
            return out
        time.sleep(0.05)
    raise AssertionError(f"{text!r} never appeared in:\n{term.read(0)[0].decode('utf-8', 'replace')}")


@unittest.skipUnless(flow_terminal.AVAILABLE, "needs a Unix pty")
class Terminal(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        with open(os.path.join(self.root, "flow.py"), "w") as f:
            f.write(FAKE_FLOW)
        self.t = flow_terminal.FlowTerminal(self.root)

    def tearDown(self):
        self.t.close()
        shutil.rmtree(self.root, ignore_errors=True)

    def test_tty_input_and_exit(self):
        self.t.start("--spec 'a b.json' --gui", 90, 20)
        out = wait_for(self.t, "name? ")
        self.assertIn("tty True True", out)                       # flow.py opens its interactive session on a TTY
        self.assertIn("['--spec', 'a b.json']", out)              # quoting kept, --gui dropped
        self.t.write(b"ddr3\r")
        wait_for(self.t, "got ddr3")
        wait_for(self.t, "exited with code 0")
        self.assertFalse(self.t.running())
        self.assertEqual(self.t.state()["exit_code"], 0)

    def test_ctrl_c_and_one_run_at_a_time(self):
        self.t.start("--sleep")
        wait_for(self.t, "tty True")
        with self.assertRaises(RuntimeError):
            self.t.start("")
        self.t.interrupt()
        wait_for(self.t, "exited with code")
        self.assertFalse(self.t.running())
        self.assertNotEqual(self.t.exit_code, 0)

    def test_offsets(self):
        self.t._append(b"x" * 10)
        data, end, reset = self.t.read(4)
        self.assertEqual((data, end, reset), (b"x" * 6, 10, False))
        data, end, reset = self.t.read(999)      # a page from before a server restart
        self.assertTrue(reset)
        self.assertEqual(data, b"x" * 10)


@unittest.skipUnless(flow_terminal.AVAILABLE, "needs a Unix pty")
class Endpoints(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        with open(os.path.join(self.root, "flow.py"), "w") as f:
            f.write(FAKE_FLOW)
        os.makedirs(os.path.join(self.root, "runs"))
        self.term = flow_terminal.FlowTerminal(self.root)
        self.srv, url = flow_gui.serve(flow_gui.Watcher(os.path.join(self.root, "runs")), port=18840,
                                       open_browser=False, terminal=self.term)
        self.port = self.srv.server_address[1]
        page = self.get("/")[1].decode()
        self.token = page.split('const RAW_TOKEN = "')[1].split('"')[0]

    def tearDown(self):
        self.term.close()
        self.srv.shutdown()
        self.srv.server_close()
        shutil.rmtree(self.root, ignore_errors=True)

    def req(self, method, path, body=None, headers=None):
        c = http.client.HTTPConnection("127.0.0.1", self.port, timeout=10)
        c.request(method, path, body=body, headers=headers or {})
        r = c.getresponse()
        out = (r.status, r.read())
        c.close()
        return out

    def get(self, path, **kw):
        return self.req("GET", path, **kw)

    def post(self, path, obj, token=None, host=None):
        h = {"X-Flow-Token": self.token if token is None else token, "Content-Type": "application/json"}
        if host:
            h["Host"] = host
        body = obj if isinstance(obj, bytes) else json.dumps(obj).encode()
        return self.req("POST", path, body=body, headers=h)

    def test_page_carries_a_token(self):
        self.assertEqual(len(self.token), 32)

    def test_start_needs_the_token_and_a_local_host(self):
        self.assertEqual(self.post("/api/term/start", {"args": ""}, token="nope")[0], 403)
        self.assertEqual(self.post("/api/term/start", {"args": ""}, host="evil.example:80")[0], 403)
        self.assertEqual(self.get("/api/term/stream?token=nope")[0], 403)
        self.assertFalse(self.term.running())

    def test_start_type_and_stream(self):
        code, body = self.post("/api/term/start", {"args": "", "cols": 80, "rows": 24})
        self.assertEqual(code, 200, body)
        self.assertTrue(json.loads(body)["running"])
        wait_for(self.term, "name? ")
        self.assertEqual(self.post("/api/term/input", b"hi\r")[0], 200)
        wait_for(self.term, "exited with code 0")
        st = json.loads(self.get("/api/status")[1])["terminal"]
        self.assertEqual(st["exit_code"], 0)
        # the stream replays everything from the start for a page that just opened
        c = http.client.HTTPConnection("127.0.0.1", self.port, timeout=10)
        c.request("GET", f"/api/term/stream?token={self.token}&from=0")
        r = c.getresponse()
        self.assertEqual(r.getheader("Content-Type"), "text/event-stream")
        buf = b""
        while b"\n\n" not in buf:
            buf += r.fp.read1(65536)
        c.close()
        data = [ln[6:] for ln in buf.decode().splitlines() if ln.startswith("data: ")][0]
        self.assertIn("got hi", base64.b64decode(data).decode("utf-8", "replace"))


if __name__ == "__main__":
    unittest.main()
