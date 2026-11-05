#!/usr/bin/env python3
"""flow.py under a pseudo-terminal, for the progress page's terminal panel.

flow.py and the spec agent it opens behave as they do in a terminal: they
see a TTY (flow.py only opens the interactive spec session on one), print
colour, read input() from what is typed on the page, and Ctrl-C reaches
the whole run. Output is kept as scrollback so a page that closes and comes
back picks up where it was. The run belongs to the GUI server: it keeps
going with no page open, and stops when the server does.

Unix only (pty); on Windows the panel says so and the page is watch-only.
"""

import os
import shlex
import signal
import subprocess
import sys
import threading
import time

try:
    import fcntl
    import pty
    import struct
    import termios
    AVAILABLE, WHY_NOT = True, None
except ImportError:            # Windows has no pty
    AVAILABLE, WHY_NOT = False, "needs a Unix pseudo-terminal (macOS or Linux)"

# The child makes the pty its controlling terminal before exec'ing flow.py,
# so Ctrl-C (and a hang-up when the server goes) reach its process group.
_WRAP = ("import fcntl, os, sys, termios\n"
         "fcntl.ioctl(0, termios.TIOCSCTTY, 0)\n"
         "os.execvp(sys.argv[1], sys.argv[1:])\n")


class FlowTerminal:
    MAX_SCROLLBACK = 4 << 20

    def __init__(self, root, script="flow.py", python=sys.executable):
        self.root, self.script, self.python = root, os.path.join(root, script), python
        self.cond = threading.Condition()
        self.buf, self.base = bytearray(), 0      # base = absolute offset of buf[0]
        self.proc = self.master = None
        self.args, self.started, self.ended, self.exit_code = None, None, None, None
        self.cols, self.rows = 120, 36

    # -- state -------------------------------------------------------------
    @property
    def end(self):
        return self.base + len(self.buf)

    def running(self):
        return self.proc is not None and self.proc.poll() is None

    def state(self):
        return {"available": AVAILABLE, "reason": WHY_NOT, "running": self.running(),
                "pid": self.proc.pid if self.proc else None, "args": self.args,
                "started": self.started, "ended": self.ended, "exit_code": self.exit_code}

    def _append(self, data):
        with self.cond:
            self.buf += data
            over = len(self.buf) - self.MAX_SCROLLBACK
            if over > 0:
                del self.buf[:over]
                self.base += over
            self.cond.notify_all()

    def read(self, since):
        """(bytes after `since`, new offset, reset) — reset when `since` is
        from before a server restart (beyond what this buffer has seen)."""
        with self.cond:
            reset = since > self.end
            if reset or since < self.base:
                since = self.base
            return bytes(self.buf[since - self.base:]), self.end, reset

    def wait(self, since, timeout):
        with self.cond:
            return self.cond.wait_for(lambda: self.end != since, timeout)

    # -- control -----------------------------------------------------------
    def start(self, argstr, cols=None, rows=None):
        if not AVAILABLE:
            raise RuntimeError(f"the terminal {WHY_NOT}")
        with self.cond:
            if self.running():
                raise RuntimeError("a run is already going; stop it first")
            args = shlex.split(argstr or "")
            # this page already is the GUI; a second one would only compete for the port
            args = [a for a in args if a != "--gui"]
            self.cols, self.rows = int(cols or self.cols), int(rows or self.rows)
            master, slave = pty.openpty()
            self._winsize(slave)
            env = dict(os.environ, TERM="xterm-256color", COLORTERM="truecolor",
                       FLOW_GUI_TERMINAL="1")
            cmd = [self.python, "-c", _WRAP, self.python, self.script] + args
            try:
                self.proc = subprocess.Popen(cmd, stdin=slave, stdout=slave, stderr=slave,
                                             cwd=self.root, env=env, start_new_session=True,
                                             close_fds=True)
            finally:
                os.close(slave)
            self.master = master
            self.args = args
            self.started, self.ended, self.exit_code = time.time(), None, None
        shown = " ".join(shlex.quote(a) for a in ["python3", "flow.py"] + args)
        self._append(f"\x1b[38;5;110m$ {shown}\x1b[0m\r\n".encode())
        threading.Thread(target=self._pump, args=(self.proc, master), daemon=True).start()
        return self.state()

    def _pump(self, proc, master):
        while True:
            try:
                data = os.read(master, 65536)
            except OSError:          # EIO: every holder of the slave side has exited
                break
            if not data:
                break
            self._append(data)
        rc = proc.wait()
        try:
            os.close(master)
        except OSError:
            pass
        with self.cond:
            if self.master == master:
                self.master = None
            self.exit_code, self.ended = rc, time.time()
        colour = "32" if rc == 0 else "33"
        self._append(f"\r\n\x1b[{colour}m[flow.py exited with code {rc}]\x1b[0m\r\n".encode())

    def write(self, data):
        m = self.master
        if m is None or not self.running():
            return False
        os.write(m, data)
        return True

    def _winsize(self, fd):
        fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", self.rows, self.cols, 0, 0))

    def resize(self, cols, rows):
        self.cols, self.rows = max(20, int(cols)), max(5, int(rows))
        if self.master is not None:
            try:
                self._winsize(self.master)   # the kernel sends SIGWINCH to the run
            except OSError:
                pass

    def interrupt(self):
        """Ctrl-C to the run's foreground process group, like a terminal."""
        if self.running():
            try:
                os.killpg(os.getpgid(self.proc.pid), signal.SIGINT)
            except (ProcessLookupError, PermissionError):
                pass

    def close(self):
        """Server going away: hang up on the run, as closing a terminal does."""
        if self.running():
            try:
                os.killpg(os.getpgid(self.proc.pid), signal.SIGHUP)
            except (ProcessLookupError, PermissionError):
                pass
