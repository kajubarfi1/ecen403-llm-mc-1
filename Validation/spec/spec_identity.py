#!/usr/bin/env python3
"""Content identity of a spec.

`revision` is a name the spec gives itself; it has stayed the same while the
content changed (2026-10-08: CTRL_STATUS grew a bit, DM polarity and the
intake fields were added, all under `golden_ddr3_1600k_x8_2lane_1rank`).
Everything Validation records about "the spec this was judged/generated
under" therefore carries the content id too: sha256 of the canonical JSON,
first 16 hex digits. Two specs are the same spec only when the ids match.
"""

import hashlib
import json


def spec_sha256(path):
    with open(path) as f:
        doc = json.load(f)
    canon = json.dumps(doc, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canon.encode()).hexdigest()[:16]


if __name__ == "__main__":
    import sys
    for p in sys.argv[1:]:
        print(spec_sha256(p), p)
