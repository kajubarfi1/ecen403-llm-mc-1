# Handoff to Frontend -- 2026-11-05 (2): how did you get Olympus to accept an SSH key?

From Backend (Dawson) to Frontend (Lehana), with a section for Validation
(Jacob) at the end. This is a question, not a report.

**The ask, in one line: what did you do beyond `ssh-copy-id` to make Olympus
accept a passphrase-less key?** You documented the procedure in `USAGE.md`
section 3.6 (`cb2dc77`), so it works for you. It does not work for me, and I
have run out of things to check from an unprivileged shell.

## 1. Why this matters right now

I have been asked to be able to run the **whole flow** for the group -- spec
through validated chip -- because nobody else wants to install OpenROAD. That
is now set up and pushed:

| | |
|---|---|
| `run_flow.ps1` | one command; loads each subsystem's env, reports readiness without printing secrets |
| `docs/RUNNING_THE_FLOW.md` | the runbook |
| flow venv | one interpreter satisfying all three subsystems (`flow.py` uses `sys.executable` for every stage) |
| `--per-block-netlists` | new `flow.py` flag; closes the stage-8 edge (details in section 5) |

Verified end to end on my machine: `spec_synthesis` PASS (27/27 consistency
checks), `spec_review` PASS (0 blocking, 3 advisory, JEDEC 25/0). Then:

```
rtl_generation   HALT   OLYMPUS_KEY unset
```

**That halt is the only thing standing between us and a full-chain run.**
Stages 3, 4, 5, 7 and 8 all need Olympus. Stages 1, 2, 6 and 6b do not, so the
backend half runs today regardless -- but the whole point of the exercise is
the whole chain.

Worth stating plainly so the scope is clear: this is not a problem with
anything you built. `flow.py`'s own check is correct and I am not asking you to
change it. The Frontend phase pipelines reasonably fall back to
`getpass.getpass()` when there is no key, and a non-interactive run cannot
answer a prompt -- so a key is genuinely the right mechanism. I just cannot get
one accepted.

## 2. What I did

Exactly your section 3.6, with `ssh-copy-id` replaced by its equivalent
(Windows OpenSSH does not ship `ssh-copy-id`):

```
ssh-keygen -t ed25519 -f ~/.ssh/olympus -N ""
# then, with the key passed as an argument rather than on stdin:
mkdir -p ~/.ssh; chmod go-w ~; chmod 700 ~/.ssh
echo '<pubkey>' >> ~/.ssh/authorized_keys
chmod 600 ~/.ssh/authorized_keys
restorecon -R -v ~/.ssh
```

Account `dawsoncarpenter`, home `/home/ugrads/d/dawsoncarpenter`.

## 3. What the client sees

```
debug1: Authentications that can continue: publickey,password
debug1: Offering public key: C:\Users\dawca\.ssh\olympus ED25519 SHA256:Pni7lU...
debug1: Authentications that can continue: publickey,password
```

Key offered, server rejects it, no `Server accepts key` line. `publickey` **is**
in the server's accepted list, so pubkey auth is not switched off wholesale.
With `BatchMode=yes`: `Permission denied (publickey,password)`.

## 4. What I have ruled out, with evidence

Listing these so you do not spend time re-suggesting them. I was wrong twice
before getting here, so the eliminations are worth more than my current
hypothesis.

| Candidate | Evidence it is not the cause |
|---|---|
| Wrong key installed | Server copy and local pub key agree: both `ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIGop8c205zFMSiuPzAWSIUWY...`. Offered fingerprint `SHA256:Pni7lU...` equals `ssh-keygen -lf` on my local key. **Byte-identical, right key.** |
| Key not installed at all | `authorized_keys` is 97 bytes, 1 line -- byte-exact for one ed25519 key plus comment |
| Passphrase on the key | Generated with `-N ""`; `BatchMode=yes` would fail differently |
| Home or `.ssh` group/world writable (`StrictModes`) | `drwx------` on both, `-rwx------` on `authorized_keys`. Owner-only throughout |
| **SELinux / NFS labelling** | This was my main theory and it is **wrong**. Context is `nfs_t`, but `getsebool use_nfs_home_dirs --> on`, so sshd is permitted to read keys from an NFS home. `restorecon` also had nothing to change -- the label comes from the mount |
| Windows refusing my private key | No `too open` warning, and the key is offered, so the client reads it fine |
| Off-campus / VPN | Reachable: `Test-NetConnection olympus.ece.tamu.edu:22` succeeds, password auth works |
| CRLF in the key line | There *was* a stray `\r` from a first attempt via a Windows pipe. Cleaned with `tr -d '\r'` and deduplicated; the surviving line is clean |

## 5. What is left, and why I cannot check it

One clue: `/etc/ssh/sshd_config` returns **Permission denied**. That file is
normally world-readable, so this is a hardened, centrally managed
configuration. That fits three explanations, all invisible from a user shell
and all needing either your knowledge or an admin:

1. **`AuthorizedKeysFile` points somewhere else** -- e.g. a central
   `/etc/ssh/authorized_keys/%u`. Common precisely *because* homes are on NFS.
   If so, my key sits in a file sshd never reads, and the fix is knowing the
   real location.
2. **`AuthorizedKeysCommand`** pulling keys from a directory service, in which
   case the key has to be registered somewhere rather than appended to a file.
3. **A `Match` block** restricting `PubkeyAuthentication` to certain users or
   groups.

A detail that may or may not be a clue: my `chmod 600` ran *after* the `mv` and
the file still reports `-rwx------`, so mode changes are not fully taking on
that mount. It is still owner-only, so it should not matter for `StrictModes`,
but it says the NFS mount behaves oddly and I would rather mention it than sit
on it.

## 6. The actual questions

Any one of these probably unblocks it:

1. **Did `ssh-copy-id` just work for you, or did you do something else first?**
2. **Did you have to register the key through a web portal or a helpdesk
   ticket?** TAMU engineering does this on some hosts.
3. **Is your key in `~/.ssh/authorized_keys`, or somewhere else?** If you can
   run `ssh -v ... exit 2>&1 | grep -i 'authorized\|Server accepts key'` and
   tell me what the accepting line says, that settles it.
4. **Is your Olympus home under `/home/ugrads/`** like mine, or a different
   tree? If yours is local and mine is NFS, that alone would explain the split.
5. Your key is named `id_ed25519_olympus2`. **What happened to `olympus1`?**
   Only half joking -- if the first attempt failed the same way, whatever you
   changed is exactly what I need.

If none of this rings a bell, say so and I will open a ticket with
`linux-engr-helpdesk@tamu.edu` asking where sshd reads authorized keys for
ugrad NFS homes. I would just rather not spend two days on a ticket if the
answer is a sentence from you.

## 7. For Jacob

You are clearly automating Olympus -- `7dc209f` adds SSH connect retries to
`flow.py`, and you have run full flows and a spec matrix. **How do you
authenticate?** If you are on a key, same questions as above. If you are not,
how do your unattended runs get past the prompt?

Two other things for you:

- **`--per-block-netlists`** (pushed `83527d1`) builds each block of the run's
  own drop after the top-level build, into the same `out_root`, so
  `runner/<block>/6_final.v` exists for stage 8 to swap in. Stage 8 previously
  halted on a top-level-only build because `find_netlists()` excludes `TOPRTL`
  and `ddr3_controller`. It is opt-in (~1 h, 11 blocks at 2 workers) and
  non-fatal: a block that misses timing standalone still routes and still
  yields a netlist, and the top-level build stays the sign-off.
- **The 4 stale netlists are mine and I will refresh them.** `9d459e5` reports
  "7 current pass, 4 stale". `backend/outputs/NETLISTS.json` is from drop
  `5f56adc7b7f5`, 2026-10-28 -- it predates the deadline narrowing, the
  saturating countdown *and* the priority tree, so `scheduler` there still
  reads WNS -0.4257 / 184.31 MHz, a pre-tree number. Any gate-level verdict
  against those four is against week-old netlists. I will rebuild them from
  the current drop; `--per-block-netlists` keeps it from recurring, since it
  cuts bundles from the run's own drop rather than from committed artifacts.

## 8. One fix worth having regardless

While tracing this I found a pre-existing crash in `flow.py`'s `sh()`, the
helper every stage uses. It called `subprocess.Popen(..., text=True)` with no
encoding, so output was decoded with the platform locale codec -- cp1252 on
Windows. The backend's own status line contains a U+2192 arrow, so reading
stage 6's output raised `UnicodeDecodeError` **after the build had run but
before the stage could return a verdict**. An hour of ORFS, then a traceback
instead of a result.

Fixed in `83527d1` with `encoding="utf-8", errors="replace"`, keeping the
`PYTHONUNBUFFERED` change from `7dc209f` (both were on the same lines; I merged
rather than replaced). This only bites on Windows, so neither of you would have
seen it -- but it would have killed my first full run an hour in.

## Summary

| | |
|---|---|
| Full-flow setup for one machine | **done and pushed** (`b6e4197`, `83527d1`) |
| Stages 1, 2 verified through the launcher | **PASS** |
| Stage 6b verified in `contract` mode | 11/11 bundles, intake 0 FAIL |
| Stages 3, 4, 5, 7, 8 | **blocked on Olympus key auth** |
| What I need | one answer from section 6 |
| What I will do meanwhile | refresh the 4 stale per-block netlists; `build`-mode run of 6b |

Nothing here is blocking on either of you except the one question, and I have a
ticket as the fallback. Thanks -- and Lehana, if the answer is "oh, you have to
do X", section 3.6 of `USAGE.md` is probably worth a line about it, since the
next person on Windows will hit exactly this.
