#!/usr/bin/env python3
"""
predictor_gates.py — spec-derived acceptance suites for generated predictors
=============================================================================
The piece that makes an agent-generated oracle trustworthy.

A predictor is written by an LLM from the spec. This grades it using checks
derived from that SAME spec by deterministic code the agent never sees. The
agent cannot satisfy the gate by construction, by luck, or by writing its own
exam — which is precisely how the previous flow's reference models were
accepted (`"ALL TESTS PASSED" in stdout`, audit finding V-05).

Three properties the gates hold to:

  * Every expectation is COMPUTED from the spec here, never obtained by
    calling the predictor being graded, and never hand-typed. A spec with
    more registers or different reset values grades correctly with no edit.
  * Failures are written as instructions, not observations. They are fed back
    into the agent's prompt verbatim, so "TIMING_0.tRCD_nCK: wrote 0x1F, read
    back 0x0 — RW fields must retain what the bus writes" beats "assertion
    failed".
  * A gate that cannot apply says so rather than passing. An unapplicable
    gate returning "no failures" would read as acceptance.

Gate selection is by SHAPE, not by scope name: a gate declares what it needs
from the spec and from the scope's schema, so a different design gets the
right gate without a lookup table naming this design's blocks.

Whether a gate is strong enough is a separate, measurable question — see
Validation/tools/mutate_predictor.py, which injects known bugs and reports
what fraction the gate catches.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "Validation", "txn"))

from txn_contract import Txn


# =============================================================================
# Helpers shared by gates
# =============================================================================

def _parse_bits(bits):
    """'31:24' -> (31, 24);  '7' -> (7, 7)."""
    s = str(bits)
    if ":" in s:
        hi, lo = s.split(":")
        return int(hi), int(lo)
    return int(s), int(s)


def _parse_offset(off):
    return int(str(off), 0)


class GateNotApplicable(Exception):
    """This gate cannot grade this scope. Never confuse with 'no failures'."""


# =============================================================================
# Register-map gate
# =============================================================================

def by_field_name(by_field, reg, hi, lo):
    for n, (r, h, l, _a) in by_field.items():
        if r is reg and h == hi and l == lo:
            return n
    return "?"


class RegisterMapGate:
    """Grades a predictor for a memory-mapped register block.

    Applies when the spec carries a register map and the scope exposes a
    request interface with an address (plus write data) and a response
    interface returning read data. Every expected value below is composed
    from the register map's own field list.
    """

    name = "register_map"

    # ---- applicability -----------------------------------------------------

    @staticmethod
    def _regmap(spec):
        for key, val in spec.items():
            if not isinstance(val, dict) or "registers" not in val:
                continue
            regs = val["registers"]
            if isinstance(regs, list) and regs and "fields" in regs[0]:
                return val
        return None

    @classmethod
    def applies(cls, predictor_cls, spec, schemas):
        """Shape alone is not enough to claim a scope.

        A Wishbone host bridge has the same transaction SHAPE as a register
        block — a request carrying (addr, data) and a response carrying
        (addr, data) — so shape-matching alone selected this gate for
        wb_port, whose predictor it would then have graded against the CSR
        register map: driving 8-bit CSR offsets into a 29-bit memory address
        port and demanding reset values from an unrelated block. The verdict
        would have been meaningless in both directions.

        The address width is what distinguishes them: a register-map gate
        only applies to an interface addressed the way the register map says
        it is addressed."""
        regmap = cls._regmap(spec)
        if regmap is None:
            return False
        try:
            ri, wk, rk, oi, ok = cls._resolve_ifaces(predictor_cls, schemas)
        except GateNotApplicable:
            return False

        declared = regmap.get("address_width_bits")
        if declared is None:
            return False
        actual = schemas[ri]["kinds"][rk].get("addr", {}).get("width")
        if actual != declared:
            return False

        dw = regmap.get("data_width_bits")
        odw = schemas[oi]["kinds"][ok].get("data", {}).get("width")
        if dw is not None and odw is not None and odw != dw:
            return False
        return True

    @staticmethod
    def _resolve_ifaces(predictor_cls, schemas):
        """Find (req_iface, write_kind, read_kind, rsp_iface, rsp_kind).

        Shape-based: a request interface has a kind carrying addr+data (write)
        and a kind carrying addr (read); a response interface has a kind
        carrying addr+data. Names are not assumed.
        """
        ins = [i for i in predictor_cls.INPUT_IFACES if i in schemas]
        outs = [i for i in predictor_cls.OUTPUT_IFACES if i in schemas]
        if not ins or not outs:
            raise GateNotApplicable(
                f"predictor declares INPUT_IFACES={predictor_cls.INPUT_IFACES} "
                f"OUTPUT_IFACES={predictor_cls.OUTPUT_IFACES}; not all are in "
                f"the generated schemas ({sorted(schemas)}).")
        for ri in ins:
            kinds = schemas[ri]["kinds"]
            wk = next((k for k, f in kinds.items()
                       if "addr" in f and "data" in f), None)
            rk = next((k for k, f in kinds.items()
                       if "addr" in f and "data" not in f), None)
            if not (wk and rk):
                continue
            for oi in outs:
                okinds = schemas[oi]["kinds"]
                ok = next((k for k, f in okinds.items()
                           if "addr" in f and "data" in f), None)
                if ok:
                    return ri, wk, rk, oi, ok
        raise GateNotApplicable(
            "no request interface with write(addr,data)+read(addr) kinds "
            "paired with a response interface returning (addr,data).")

    # ---- expectations, composed from the spec ------------------------------

    @staticmethod
    def _fields(reg):
        for f in reg.get("fields", []):
            hi, lo = _parse_bits(f["bits"])
            yield (f["name"], hi, lo, f.get("access", "RO").upper(),
                   int(f.get("reset_value", 0)))

    @classmethod
    def _reset_readback(cls, reg, mask):
        """What a read after reset must return: every non-WO field at its
        reset value, WO reading zero."""
        val = 0
        for _n, hi, lo, acc, rst in cls._fields(reg):
            if acc == "WO":
                continue
            val |= (rst & ((1 << (hi - lo + 1)) - 1)) << lo
        return val & mask

    # ---- grading -----------------------------------------------------------

    @classmethod
    def grade(cls, predictor, spec, schemas):
        """Return a list of actionable failure strings (empty = accepted)."""
        regmap = cls._regmap(spec)
        if regmap is None:
            raise GateNotApplicable("spec carries no register map")
        ri, wk, rk, oi, ok = cls._resolve_ifaces(type(predictor), schemas)

        width = int(regmap.get("data_width_bits", 32))
        mask = (1 << width) - 1
        regs = regmap["registers"]
        fails = []

        def read(addr):
            """Drive one read; return the data field of the single emitted
            response, or a failure string."""
            out = predictor.process(Txn(ri, rk, {"addr": addr}))
            if not isinstance(out, list):
                return None, (f"process() must return a list; a read returned "
                              f"{type(out).__name__}.")
            if len(out) != 1:
                return None, (f"a read of {addr:#04x} produced {len(out)} "
                              f"transaction(s); exactly one response is "
                              f"expected on '{oi}'.")
            t = out[0]
            if t.iface != oi or t.kind != ok:
                return None, (f"a read produced {t.iface}.{t.kind}; it must "
                              f"produce {oi}.{ok}.")
            if "data" not in t.fields:
                return None, (f"the response to a read has no 'data' field "
                              f"(got {sorted(t.fields)}); the schema for "
                              f"{oi}.{ok} requires it.")
            return t.fields["data"], None

        def write(addr, data):
            predictor.process(Txn(ri, wk, {"addr": addr, "data": data}))

        # --- 1. reset readback, every register ------------------------------
        predictor.reset()
        for reg in regs:
            off = _parse_offset(reg["offset"])
            got, err = read(off)
            if err:
                fails.append(f"{reg['name']}: {err}")
                continue
            want = cls._reset_readback(reg, mask)
            if got != want:
                fails.append(
                    f"{reg['name']} (offset {off:#04x}): after reset a read "
                    f"returned {got:#010x}, but the register map's field reset "
                    f"values compose to {want:#010x}. Compose each field's "
                    f"reset_value at its bit position; write-only fields read "
                    f"as zero.")

        # --- 2. RW fields retain what is written ----------------------------
        for reg in regs:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _rst in cls._fields(reg):
                if acc != "RW":
                    continue
                fmask = (1 << (hi - lo + 1)) - 1
                predictor.reset()
                write(off, fmask << lo)
                got, err = read(off)
                if err:
                    fails.append(f"{reg['name']}.{name}: {err}")
                    break
                if ((got >> lo) & fmask) != fmask:
                    fails.append(
                        f"{reg['name']}.{name} (bits {hi}:{lo}, access RW): "
                        f"wrote all-ones, read back {(got >> lo) & fmask:#x} "
                        f"instead of {fmask:#x}. RW fields must retain the "
                        f"value the bus writes.")

        # --- 3. RO fields ignore bus writes ---------------------------------
        for reg in regs:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, rst in cls._fields(reg):
                if acc != "RO":
                    continue
                fmask = (1 << (hi - lo + 1)) - 1
                predictor.reset()
                write(off, mask)
                got, err = read(off)
                if err:
                    break
                if ((got >> lo) & fmask) != (rst & fmask):
                    fails.append(
                        f"{reg['name']}.{name} (bits {hi}:{lo}, access RO): a "
                        f"bus write changed it to {(got >> lo) & fmask:#x}; "
                        f"read-only fields must be unaffected by bus writes "
                        f"and keep {rst & fmask:#x}.")

        # --- 4. RW1C clears on 1, retains on 0 ------------------------------
        for reg in regs:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _rst in cls._fields(reg):
                if acc != "RW1C":
                    continue
                fmask = (1 << (hi - lo + 1)) - 1
                predictor.reset()
                write(off, fmask << lo)          # write ones -> must clear
                got, err = read(off)
                if err:
                    break
                if ((got >> lo) & fmask) != 0:
                    fails.append(
                        f"{reg['name']}.{name} (bits {hi}:{lo}, access RW1C): "
                        f"writing ones left {(got >> lo) & fmask:#x}; RW1C "
                        f"fields clear the bits written as 1.")
                predictor.reset()
                write(off, 0)                    # write zeros -> must retain
                got2, err2 = read(off)
                if err2:
                    break

        # --- 5. WO fields read as zero --------------------------------------
        for reg in regs:
            off = _parse_offset(reg["offset"])
            for name, hi, lo, acc, _rst in cls._fields(reg):
                if acc != "WO":
                    continue
                fmask = (1 << (hi - lo + 1)) - 1
                predictor.reset()
                write(off, fmask << lo)
                got, err = read(off)
                if err:
                    break
                if ((got >> lo) & fmask) != 0:
                    fails.append(
                        f"{reg['name']}.{name} (bits {hi}:{lo}, access WO): "
                        f"read back {(got >> lo) & fmask:#x}; write-only "
                        f"fields always read as zero.")

        # --- 6. state survives unrelated writes -----------------------------
        rw_targets = [(r, n, hi, lo) for r in regs
                      for n, hi, lo, a, _ in cls._fields(r) if a == "RW"]
        if len(rw_targets) >= 2:
            (r1, n1, hi1, lo1), (r2, _n2, _hi2, _lo2) = rw_targets[0], rw_targets[-1]
            if r1 is not r2:
                predictor.reset()
                o1, o2 = _parse_offset(r1["offset"]), _parse_offset(r2["offset"])
                fm1 = (1 << (hi1 - lo1 + 1)) - 1
                write(o1, fm1 << lo1)
                write(o2, mask)
                got, err = read(o1)
                if not err and ((got >> lo1) & fm1) != fm1:
                    fails.append(
                        f"{r1['name']}.{n1}: a later write to {r2['name']} "
                        f"({o2:#04x}) disturbed it. Registers are independent; "
                        f"a write must only affect the register it addresses.")

        # --- 7. writes are masked to the bus width --------------------------
        if rw_targets:
            reg, name, hi, lo = rw_targets[0]
            predictor.reset()
            off = _parse_offset(reg["offset"])
            write(off, (1 << (width + 4)) - 1)
            got, err = read(off)
            if not err and got >> width:
                fails.append(
                    f"{reg['name']}: a write of a value wider than the "
                    f"{width}-bit bus left bits above {width - 1} set "
                    f"({got:#x}). Mask incoming data to the bus width.")

        # --- 8. the model must not be vacuous -------------------------------
        predictor.reset()
        got, err = read(_parse_offset(regs[0]["offset"]))
        if not err:
            all_same = True
            for reg in regs[1:]:
                g, e = read(_parse_offset(reg["offset"]))
                if e or g != got:
                    all_same = False
                    break
            if all_same and len(regs) > 2:
                fails.append(
                    f"every register read returns the same value ({got:#010x}). "
                    f"The model is not distinguishing registers — decode the "
                    f"address against the register map's offsets.")

        # --- 9. configuration broadcasts follow the registers ---------------
        # A register block also drives level streams downstream (cfg_timing,
        # cfg_refresh): each stream field's port is named after a register
        # field (cfg_<field>), so the expectation composes from the register
        # map alone. After a write that changes a mapped field, the stream
        # must carry an update in which every mapped field equals the
        # register's current field value. Fields with no register behind
        # them (self-clearing pulses) are not graded here.
        fails += cls._grade_broadcasts(predictor, regs, schemas, type(predictor),
                                       ri, wk, oi, write, rk)

        # --- 10. read-only fields mirror the hardware levels, full width ----
        fails += cls._grade_level_mirrors(predictor, regs, schemas, type(predictor),
                                          ri, read, mask)
        return fails

    @classmethod
    def _grade_level_mirrors(cls, predictor, regs, schemas, pcls, ri, read, mask):
        """A read-only field whose port is a hardware level (`sts_<field>`)
        reads back exactly the level, at the field's bit position, over the
        field's WHOLE width. Drive the top bit alone and all ones: a model
        built for a narrower field (the 3-bit `ref_pending_cnt` of an
        earlier spec, masked `& 0x7` after the spec made it 4 bits) passes
        every other step and fails here. Every other mirrored field must
        still read zero, so a field driven at the wrong offset is named."""
        fails = []
        by_field = {}
        for reg in regs:
            for name, hi, lo, acc, rst in cls._fields(reg):
                by_field[name] = (reg, hi, lo, acc)
        for li in pcls.INPUT_IFACES:
            if li == ri or li not in schemas:
                continue
            for kind, fields in schemas[li]["kinds"].items():
                mapped = {}
                for fname, info in fields.items():
                    port = info.get("port", "")
                    for pre in ("sts_",):
                        stem = port[len(pre):] if port.startswith(pre) else None
                        if stem in by_field and by_field[stem][3] == "RO":
                            mapped[fname] = by_field[stem] + (int(info.get("width", 1)),)
                if not mapped:
                    continue
                for fname, (reg, hi, lo, _acc, w) in mapped.items():
                    fw = hi - lo + 1
                    if w != fw:
                        fails.append(
                            f"{li}.{kind}.{fname} is {w} bit(s) wide but mirrors "
                            f"{reg['name']}.{by_field_name(by_field, reg, hi, lo)} "
                            f"[{hi}:{lo}] ({fw} bits); the schema and the register "
                            f"map disagree -- not the model's fault, but it cannot be "
                            f"graded on this field.")
                        continue
                    for val in sorted({1, 1 << (fw - 1), (1 << fw) - 1}):
                        predictor.reset()
                        lv = {f2: 0 for f2 in fields}
                        lv[fname] = val
                        predictor.process(Txn(li, kind, lv))
                        got, err = read(_parse_offset(reg["offset"]))
                        if err:
                            fails.append(f"{reg['name']} after {li}.{kind}.{fname}={val:#x}: {err}")
                            break
                        want = (val << lo) & mask
                        if got != want:
                            fails.append(
                                f"{reg['name']}: with hardware level {li}.{kind}.{fname} = "
                                f"{val:#x} (port {fields[fname]['port']}, {fw} bits) a read "
                                f"returned {got:#010x}; the read-only field at bits "
                                f"[{hi}:{lo}] mirrors that level over its whole width, so "
                                f"the register must read {want:#010x}. Take the field's "
                                f"width and position from the register map, never from a "
                                f"literal.")
                            break
        return fails

    @classmethod
    def _grade_broadcasts(cls, predictor, regs, schemas, pcls, ri, wk, rsp_iface, write, rk):
        fails = []
        by_field = {}
        for reg in regs:
            for name, hi, lo, acc, rst in cls._fields(reg):
                by_field[name] = (reg, hi, lo, acc, rst)
        for oi in pcls.OUTPUT_IFACES:
            if oi == rsp_iface or oi not in schemas:
                continue
            for kind, fields in schemas[oi]["kinds"].items():
                mapped = {}
                for fname, info in fields.items():
                    port = info["port"]
                    for pre in ("cfg_",):
                        if port.startswith(pre) and port[len(pre):] in by_field:
                            mapped[fname] = by_field[port[len(pre):]]
                if not mapped:
                    continue
                # nothing is emitted for reset itself: the fields hold their
                # reset values through reset and the first CHANGE is the first
                # update. A model that broadcasts its baseline on the first
                # transaction it sees predicts an update the monitor (change-
                # qualified) never records, and every path fails on it.
                predictor.reset()
                any_reg = regs[0]
                quiet = []
                for probe, txn in (("a read", Txn(ri, rk, {"addr": _parse_offset(any_reg["offset"])})),
                                   ("a write that changes nothing",
                                    Txn(ri, wk, {"addr": _parse_offset(any_reg["offset"]),
                                                 "data": cls._reset_readback(any_reg, (1 << 64) - 1)}))):
                    out = predictor.process(txn) or []
                    if any(t.iface == oi and t.kind == kind for t in out):
                        quiet.append(probe)
                if quiet:
                    fails.append(
                        f"{oi}: after reset, {' and '.join(quiet)} produced a {oi}.{kind}. "
                        f"Nothing is emitted for reset itself: the fields hold their reset "
                        f"values through reset and the first change after it is the first "
                        f"update. Seed the 'last emitted' state with the reset values, not "
                        f"with None.")
                # one write per register that carries a mapped RW field
                regs_hit = {}
                for fname, (reg, hi, lo, acc, rst) in mapped.items():
                    if acc == "RW":
                        regs_hit.setdefault(reg["name"], (reg, []))[1].append((fname, hi, lo, rst))
                for rname, (reg, flds) in regs_hit.items():
                    predictor.reset()
                    off = _parse_offset(reg["offset"])
                    # compose a value that changes every mapped field of this
                    # register and keeps the others at reset
                    val = cls._reset_readback(reg, (1 << 64) - 1)
                    want = {}
                    # distinct new values per field (fields of one register
                    # often share a reset value; a swapped mapping would pass
                    # a uniform change)
                    for i, (fname, hi, lo, rst) in enumerate(flds):
                        fm = (1 << (hi - lo + 1)) - 1
                        new = (rst + 1 + i) & fm
                        if new == rst or new in want.values():
                            new = (new + 1) & fm
                        val = (val & ~(fm << lo)) | (new << lo)
                        want[fname] = new
                    out = predictor.process(Txn(ri, wk, {"addr": off, "data": val}))
                    ups = [t for t in (out or []) if t.iface == oi and t.kind == kind]
                    if not ups:
                        fails.append(
                            f"{oi}: a write of {val:#010x} to {rname} ({off:#04x}) changed "
                            f"{', '.join(want)} but no {oi}.{kind} followed. {oi} is a "
                            f"level stream: emit one update whenever any of its fields "
                            f"changes, carrying every field's current value.")
                        continue
                    last = ups[-1].fields
                    for fname, new in want.items():
                        if last.get(fname) != new:
                            fails.append(
                                f"{oi}.{kind}.{fname}: after writing {rname}.{fname} = "
                                f"{new:#x} the update carried {last.get(fname)!r}. The "
                                f"field mirrors register field {rname}.{fname}.")
                    for fname, (r2, hi, lo, acc, rst) in mapped.items():
                        if fname in want or fname not in last:
                            continue
                        fm = (1 << (hi - lo + 1)) - 1
                        if last[fname] != (rst & fm):
                            fails.append(
                                f"{oi}.{kind}.{fname}: an update caused by a write to {rname} "
                                f"carried {last[fname]!r} for {r2['name']}.{fname}, which was "
                                f"not written and must still read its reset value "
                                f"{rst & fm:#x}. Every update carries every field's current value.")
        return fails


class BusBridgeGate:
    """Grades a predictor for a block that TRANSLATES one request stream into
    another — a host bus into internal descriptors, for instance.

    A bridge is not a register block: it holds no state to read back, so the
    register gate's reset/access checks say nothing about it. What the spec
    does determine is the correspondence: how many descriptors an accepted
    access produces, which direction flag it carries, and which fields carry
    across (including renames like sel -> mask).

    That correspondence is DECLARED in interface_catalog.json under
    `derives_from`, not inferred and not hardcoded here, so a different design
    with a different bridge is graded by editing data. What this gate supplies
    is the checking: drive values through, demand they arrive intact.

    Deliberately NOT checked: fields the spec does not determine. A read
    response's data comes from downstream memory, so demanding a value for it
    would assert a requirement the specification never makes of this block —
    the same error as gating a scope against the wrong register map.
    """

    name = "bus_bridge"

    @staticmethod
    def _numeric(sv):
        """Encoding values may be plain ints or SystemVerilog literals."""
        txt = str(sv)
        if "'" in txt:
            body = txt.split("'")[1]
            return int(body[1:], {"b": 2, "h": 16, "d": 10, "o": 8}[body[0].lower()])
        return int(txt)

    @staticmethod
    def _split_expectations(asplit, spec, addr):
        """Expected {field: value} for one address, computed FROM THE SPEC.

        The slice positions are never written down anywhere: the field order
        comes from the spec's address_mapping string (high to low), the
        widths from the named geometry fields, the low-order discard from the
        channel width in bytes, and burst alignment from burst_length. A spec
        with a different geometry produces different expectations from the
        same declaration."""
        import math
        geo = spec[asplit.get("geometry_section", "memory_geometry")]
        order = [f.strip() for f in str(geo["address_mapping"]).split("-")]
        widths = {f: int(geo[w]) for f, w in asplit["output_fields"].items()}
        ch_bytes = int(geo["$derived"]["channel_data_width_bits"]) // 8
        discard = int(math.log2(ch_bytes)) if ch_bytes > 1 else 0
        aligned = set(asplit.get("burst_aligned_fields", []))
        align_bits = int(math.log2(int(geo["burst_length"])))

        # The mapping string uses the spec's own vocabulary ("column"),
        # while transaction fields use the schema's ("col"). Match a mapping
        # token to a declared output field via the geometry width name it
        # points at: "col" -> "column_bits" -> token "column". An earlier
        # version compared tokens to txn-field names directly, so "column"
        # matched nothing and was skipped WITHOUT advancing the bit offset —
        # which shifted every remaining slice 10 bits low and made the gate
        # reject a correct decoder.
        token_to_field = {}
        for txn_field, width_name in asplit["output_fields"].items():
            token_to_field[str(width_name).replace("_bits", "")] = txn_field
            token_to_field[txn_field] = txn_field

        # address_mapping lists fields high-to-low; slices stack from the
        # discard bits upward, so walk the order REVERSED.
        expected, lo = {}, discard
        for token in reversed(order):
            field = token_to_field.get(token)
            if field is None:
                # An unrecognised token cannot be skipped: doing so would
                # misplace every slice above it. Refuse to produce
                # expectations instead.
                raise GateNotApplicable(
                    f"address_mapping token {token!r} matches no declared "
                    f"output field ({sorted(asplit['output_fields'])}); the "
                    f"split cannot be computed.")
            w = widths[field]
            val = (addr >> lo) & ((1 << w) - 1)
            if field in aligned:
                val &= ~((1 << align_bits) - 1)
            expected[field] = val
            lo += w
        return expected

    @staticmethod
    def _pack_geometry(decl, spec):
        geo = spec[decl.get("geometry_section", "data_path_mapping")]
        host = int(geo["host_width_bits"])
        chan = int(geo["ddr_channel_width_bits"])
        if host % chan:
            raise GateNotApplicable(
                f"host width {host} is not a multiple of channel width "
                f"{chan}; the pack expectation cannot be computed.")
        return host, chan, host // chan, geo.get("endianness", "little")

    @classmethod
    def _grade_pack(cls, predictor, spec, schemas, oi, d, src):
        """A read command then N channel beats must yield ONE host word."""
        p = d["pack"]
        host, chan, n, endian = cls._pack_geometry(p, spec)
        cmd_iface, cmd_kind = p["command_iface"], p["command_kind"]
        beat_kind = next(iter(schemas[src]["kinds"]))
        fails = []

        for pat in range(3):
            beats = [((0xBEEF ^ (pat * 0x1357) ^ (i * 0x2468)) & ((1 << chan) - 1))
                     for i in range(n)]
            order = beats if endian == "little" else list(reversed(beats))
            want = 0
            for i, b in enumerate(order):
                want |= b << (i * chan)

            predictor.reset()
            cmd_fields = {f: 0 for f in schemas[cmd_iface]["kinds"][cmd_kind]}
            early = list(predictor.process(Txn(cmd_iface, cmd_kind, cmd_fields))
                         or [])
            for b in beats[:-1]:
                early += predictor.process(
                    Txn(src, beat_kind, {p["from_field"]: b})) or []
            premature = [t for t in early if t.iface == oi]
            if premature:
                fails.append(
                    f"{oi!r} emitted after only {n - 1} of {n} beats; a "
                    f"{spec[p.get('geometry_section', 'data_path_mapping')]['pack_mode']} "
                    f"response exists only once the full burst has arrived.")

            late = list(predictor.process(
                Txn(src, beat_kind, {p["from_field"]: beats[-1]})) or [])
            late += predictor.drain() or []
            mine = [t for t in late if t.iface == oi]
            if len(mine) != 1:
                fails.append(
                    f"a {cmd_kind} on {cmd_iface} followed by {n} beats on "
                    f"{src} produced {len(premature) + len(mine)} {oi!r} "
                    f"transaction(s); exactly one host word is required.")
                continue
            got = mine[0].fields.get(p["data_field"])
            if got != want:
                fails.append(
                    f"{oi}.{p['data_field']} is "
                    f"{got if got is None else hex(got)} for beats "
                    f"{[hex(b) for b in beats]}; the spec's mapping "
                    f"({endian}-endian, {chan}-bit channel into a {host}-bit "
                    f"host word) packs them as {want:#x}. The "
                    f"{'first' if endian == 'little' else 'last'} beat is the "
                    f"least significant half.")
        return fails

    @classmethod
    def _grade_unpack(cls, predictor, spec, schemas, oi, d, src):
        """One accepted host word must yield N channel beats, in order."""
        u = d["unpack"]
        host, chan, n, endian = cls._pack_geometry(u, spec)
        fails = []

        for skind, sfields in schemas[src]["kinds"].items():
            for pat in range(3):
                drive, seed = {}, pat * 11
                for fname, info in sfields.items():
                    w = info["width"]
                    if not isinstance(w, int):
                        continue
                    seed += 1
                    drive[fname] = ((0xDEADBEEF >> pat) ^ (seed * 0x91))\
                        & ((1 << w) - 1)
                word = drive[u["from_field"]]
                halves = [(word >> (i * chan)) & ((1 << chan) - 1)
                          for i in range(n)]
                want = halves if endian == "little" else list(reversed(halves))

                predictor.reset()
                mine = [t for t in (predictor.process(Txn(src, skind, drive))
                                    or []) if t.iface == oi]
                if len(mine) != n:
                    fails.append(
                        f"a {src}.{skind} produced {len(mine)} beat(s) on "
                        f"{oi!r}; the spec's mapping ({host}-bit host word, "
                        f"{chan}-bit channel) requires exactly {n}.")
                    continue
                got = [t.fields.get(u["data_field"]) for t in mine]
                if got != want:
                    fails.append(
                        f"{oi}.{u['data_field']} beats are "
                        f"{[hex(g) if g is not None else None for g in got]} "
                        f"for {src}.{u['from_field']}={word:#x}; the "
                        f"{endian}-endian mapping requires "
                        f"{[hex(w_) for w_ in want]} — the "
                        f"{'low' if endian == 'little' else 'high'} half of "
                        f"the word is the first beat driven.")
                    continue
                fails += cls._grade_unpack_mask(spec, u, oi, src, drive, mine, chan, endian, n)
        return fails

    @classmethod
    def _grade_unpack_mask(cls, spec, u, oi, src, drive, mine, chan, endian, n):
        """The per-beat data mask follows the host byte enables, sliced per
        beat like the data, with the polarity the spec declares
        (`ddr_dm_polarity`: active_high_mask = DM is 1 for a byte NOT
        written, i.e. the inverted enable; active_low_mask = DM equals the
        enable). Ungraded when the catalog declares no mask fields or the
        spec is silent -- then the two models may still disagree on it."""
        mf, mff = u.get("mask_field"), u.get("mask_from_field")
        if not (mf and mff) or mff not in drive:
            return []
        pol = (spec.get(u.get("geometry_section", "data_path_mapping"), {})
               .get(u.get("polarity_key", "ddr_dm_polarity")))
        if pol not in ("active_high_mask", "active_low_mask"):
            return []
        ch_bytes = chan // 8
        enables = drive[mff]
        slices = [(enables >> (i * ch_bytes)) & ((1 << ch_bytes) - 1) for i in range(n)]
        if endian != "little":
            slices = list(reversed(slices))
        want = [(~e & ((1 << ch_bytes) - 1)) if pol == "active_high_mask" else e
                for e in slices]
        got = [t.fields.get(mf) for t in mine]
        if got != want:
            return [f"{oi}.{mf} beats are {got} for {src}.{mff}={enables:#x}; the spec "
                    f"declares ddr_dm_polarity = {pol}, so each beat's mask is the "
                    f"{'INVERTED ' if pol == 'active_high_mask' else ''}byte-enable "
                    f"slice for that beat: {want}. Take the polarity from the spec's "
                    f"data_path_mapping, never assume it."]
        return []

    @staticmethod
    def _bridges(predictor_cls, catalog, schemas):
        """Output interfaces that declare a source, with that source among the
        predictor's inputs."""
        out = []
        for oi in predictor_cls.OUTPUT_IFACES:
            d = catalog.get(oi, {}).get("derives_from")
            if not d:
                continue
            src = d.get("interface")
            if src in predictor_cls.INPUT_IFACES and src in schemas and oi in schemas:
                out.append((oi, d, src))
        return out

    @classmethod
    def applies(cls, predictor_cls, spec, schemas, catalog=None):
        if catalog is None:
            catalog = _load_catalog()
        return bool(cls._bridges(predictor_cls, catalog, schemas))

    @classmethod
    def _grade_encoded(cls, predictor, schemas, catalog, oi, d, src,
                       vmap, cmap, no_out):
        """Grade a bridge that re-encodes a command value, once per command."""
        fails = []
        skind = next(iter(schemas[src]["kinds"]))
        sfields = schemas[src]["kinds"][skind]
        okind = next(iter(schemas[oi]["kinds"]))

        for ofield, spec_ in vmap.items():
            sfield = spec_["from_field"]
            senc = {k: v for k, v in
                    catalog[spec_["source_encoding_iface"]]["command_encoding"].items()
                    if not k.startswith("$")}
            tenc = {k: v for k, v in
                    catalog[spec_["target_encoding_iface"]]["command_encoding"].items()
                    if not k.startswith("$")}

            for name, sval in senc.items():
                if name in no_out.get(sfield, []):
                    continue
                if name not in tenc:
                    continue
                drive, seed = {}, 0
                for fname, info in sfields.items():
                    w = info["width"]
                    if not isinstance(w, int):
                        continue
                    seed += 1
                    drive[fname] = (0xC3C3C3C3 ^ (seed * 0x77)) & ((1 << w) - 1)
                drive[sfield] = cls._numeric(sval)
                # Two drive patterns, the second the bitwise complement of the
                # first: a single pattern leaves half of every field's bits
                # untested at one polarity (a PRECHARGE that leaked row bit 10
                # onto A10 passed for months because the pattern's bit 10 was 0).
                inv = dict(drive)
                for fname, info in sfields.items():
                    if fname != sfield and isinstance(info['width'], int):
                        inv[fname] = drive[fname] ^ ((1 << info['width']) - 1)
                for drive in (drive, inv):

                    predictor.reset()
                    mine = [t for t in (predictor.process(Txn(src, skind, drive)) or [])
                            if t.iface == oi]
                    if len(mine) != 1:
                        fails.append(
                            f"a {src} command {name} produced {len(mine)} "
                            f"transaction(s) on {oi!r}; exactly one is required.")
                        continue
                    t = mine[0]

                    want = cls._numeric(tenc[name])
                    got = t.fields.get(ofield)
                    if got != want:
                        fails.append(
                            f"{oi}.{ofield} is {got} for a {name} command; the "
                            f"{spec_['target_encoding_iface']} encoding of {name} "
                            f"is {want}. The two buses use different encodings and "
                            f"the bridge must translate between them, not copy "
                            f"the value through.")

                    # Plain field correspondences still apply on an encoded
                    # bridge. An earlier version checked only the value and
                    # conditional maps here, so a bridge that dropped the bank
                    # passed every command — the gate was grading the
                    # interesting half and ignoring the rest.
                    for ofld, sfld in d.get("field_map", {}).items():
                        if sfld not in drive:
                            continue
                        if t.fields.get(ofld) != drive[sfld]:
                            fails.append(
                                f"{oi}.{ofld} is {t.fields.get(ofld)!r} for a "
                                f"{name}, but {src}.{sfld} was driven as "
                                f"{drive[sfld]:#x}. This field carries across "
                                f"unchanged on every command.")

                    for cf, csp in cmap.items():
                        src_for = csp["by_command"].get(name)
                        if isinstance(src_for, dict) and "bits" in src_for:
                            # Declared constant bits for this command (e.g. a
                            # single-bank PRECHARGE drives A10 low). Only the
                            # declared bits are graded; the rest stay don't-care.
                            got = t.fields.get(cf) or 0
                            for bit, val in src_for["bits"].items():
                                if (got >> int(bit)) & 1 != int(val):
                                    fails.append(
                                        f"{oi}.{cf} bit {bit} is "
                                        f"{(got >> int(bit)) & 1} for a {name}; it "
                                        f"must be {val}. {src_for.get('why', '')} "
                                        f"(driven with {src} fields "
                                        f"{ {k: hex(v) for k, v in drive.items()} })")
                            continue
                        if src_for is None or src_for not in drive:
                            continue
                        if t.fields.get(cf) != drive[src_for]:
                            fails.append(
                                f"{oi}.{cf} is {t.fields.get(cf):#x} for a {name}; "
                                f"a {name} carries {src}.{src_for} "
                                f"({drive[src_for]:#x}) there. That field is "
                                f"multiplexed by command type.")

            # a command declared to produce nothing must produce nothing
            for name in no_out.get(sfield, []):
                if name not in senc:
                    continue
                drive = {f: 0 for f in sfields}
                drive[sfield] = cls._numeric(senc[name])
                predictor.reset()
                mine = [t for t in (predictor.process(Txn(src, skind, drive)) or [])
                        if t.iface == oi]
                if mine:
                    fails.append(
                        f"a {name} produced {len(mine)} {oi!r} transaction(s); "
                        f"it must produce none — the pins idle at {name} and "
                        f"that is not a transaction.")
        return fails

    @classmethod
    def grade(cls, predictor, spec, schemas, catalog=None):
        if catalog is None:
            catalog = _load_catalog()
        cls_ = type(predictor)
        bridges = cls_._bridges(cls_, catalog, schemas) if hasattr(cls_, "_bridges") \
            else cls._bridges(cls_, catalog, schemas)
        if not bridges:
            raise GateNotApplicable("no interface declares a derives_from source")

        fails = []
        for oi, d, src in bridges:
            src_kinds = schemas[src]["kinds"]
            out_kinds = schemas[oi]["kinds"]
            out_kind = next(iter(out_kinds))
            only = d.get("only_for_kinds")
            fmap = d.get("field_map", {})
            dirf = d.get("direction_field")
            absent = d.get("fields_absent_on", {})

            vmap = d.get("value_map", {})
            cmap = d.get("conditional_map", {})
            no_out = d.get("no_output_for", {})

            # Width conversion declared from the spec's data-path mapping:
            # pack (N channel beats -> one host word) or unpack (one host
            # word -> N channel beats). Both are graded from the geometry
            # section alone — beat count, width and endianness are the spec's
            # numbers, never constants here.
            if d.get("pack"):
                fails.extend(cls._grade_pack(
                    predictor, spec, schemas, oi, d, src))
                continue
            if d.get("unpack"):
                fails.extend(cls._grade_unpack(
                    predictor, spec, schemas, oi, d, src))
                continue

            # A bridge that re-encodes a command is exercised once per COMMAND,
            # not once per kind: driving a single arbitrary value would leave
            # every other encoding unchecked.
            if vmap:
                fails.extend(cls._grade_encoded(
                    predictor, schemas, catalog, oi, d, src, vmap, cmap, no_out))
                continue

            # Several distinct patterns when an address split is declared:
            # one address cannot tell a swapped slice from a correct one, and
            # an all-zero or degenerate value hides misalignment entirely.
            n_patterns = 5 if d.get("address_split") else 1
            for skind, sfields in src_kinds.items():
                if only and skind not in only:
                    continue
                for pat in range(n_patterns):
                    # Distinctive per-field values, so a swapped or dropped
                    # field is visible rather than coincidentally equal.
                    drive, seed = {}, pat * 17
                    for fname, info in sfields.items():
                        w = info["width"]
                        if not isinstance(w, int):
                            continue
                        seed += 1
                        drive[fname] = (((0xA5A5A5A5 >> pat) ^ (seed * 0x1234)
                                         ^ (pat * 0x0F0F0F1))
                                        & ((1 << w) - 1))

                    predictor.reset()
                    emitted = predictor.process(Txn(src, skind, drive))
                    if not isinstance(emitted, list):
                        fails.append(f"process() must return a list; a "
                                     f"{src}.{skind} returned "
                                     f"{type(emitted).__name__}.")
                        continue
                    mine = [t for t in emitted if t.iface == oi]

                    # An output that COMPLETES on a second stream (a read
                    # response carrying data that arrives later on another
                    # interface) is due only once that transaction has been
                    # seen: nothing may be emitted for the request alone, and
                    # exactly one for the completion, carrying its fields.
                    comp = d.get("completes_on")
                    comp_drive = None
                    if comp and skind in comp.get("for_kinds", list(src_kinds)):
                        if mine:
                            fails.append(
                                f"a {src}.{skind} produced {len(mine)} "
                                f"transaction(s) on {oi!r} before its "
                                f"{comp['interface']}.{comp['kind']} arrived; the "
                                f"response completes on that stream and must "
                                f"wait for it.")
                            continue
                        cfields = schemas[comp["interface"]]["kinds"][comp["kind"]]
                        comp_drive = {}
                        for fname, info in cfields.items():
                            w = info["width"]
                            if isinstance(w, int):
                                seed += 1
                                comp_drive[fname] = ((0x3C3C3C3C ^ (seed * 0x51))
                                                     & ((1 << w) - 1))
                        emitted = predictor.process(
                            Txn(comp["interface"], comp["kind"], comp_drive))
                        mine = [t for t in (emitted or []) if t.iface == oi]

                    card = d.get("cardinality", "one_per_source_transaction")
                    if card.startswith("one_per") and len(mine) != 1:
                        fails.append(
                            f"a {src}.{skind} produced {len(mine)} "
                            f"transaction(s) on {oi!r}; exactly one is "
                            f"required. Every accepted host access translates "
                            f"into exactly one descriptor."
                            + (f" (emitted when its {comp['interface']}."
                               f"{comp['kind']} arrives)" if comp_drive else ""))
                        continue
                    t = mine[0]

                    if comp_drive:
                        for ofield, cfield in comp.get("field_map", {}).items():
                            if t.fields.get(ofield) != comp_drive[cfield]:
                                fails.append(
                                    f"{oi}.{ofield} is {t.fields.get(ofield)!r} "
                                    f"but the completing {comp['interface']}."
                                    f"{cfield} carried {comp_drive[cfield]:#x}. "
                                    f"The response returns that value, not one "
                                    f"the model computed itself.")

                    if dirf:
                        want = dirf["by_source_kind"].get(skind)
                        got = t.fields.get(dirf["field"])
                        if want is not None and got != want:
                            fails.append(
                                f"{oi}.{dirf['field']} is {got} for a "
                                f"{src}.{skind}; it must be {want}. That flag "
                                f"is how downstream tells a read from a write.")

                    asplit = d.get("address_split")
                    if asplit and asplit["from_field"] in drive:
                        addr = drive[asplit["from_field"]]
                        geo = asplit.get("geometry_section", "memory_geometry")
                        for f, want in cls._split_expectations(
                                asplit, spec, addr).items():
                            got = t.fields.get(f)
                            if got != want:
                                fails.append(
                                    f"{oi}.{f} is "
                                    f"{got if got is None else hex(got)} for "
                                    f"{src}.{asplit['from_field']}={addr:#x}; "
                                    f"the spec's {geo}.address_mapping "
                                    f"({spec[geo]['address_mapping']}) puts "
                                    f"{want:#x} there. Fields stack "
                                    f"high-to-low above the channel "
                                    f"byte-offset bit(s); a burst-aligned "
                                    f"field zeroes its low "
                                    f"log2(burst_length) bits.")

                    for ofield, sfield in fmap.items():
                        if sfield in absent.get(skind, []):
                            continue
                        if sfield not in drive:
                            continue
                        want, got = drive[sfield], t.fields.get(ofield)
                        if got != want:
                            rename = "" if ofield == sfield else (
                                f" ({src}.{sfield} carries across as "
                                f"{oi}.{ofield})")
                            fails.append(
                                f"{oi}.{ofield} is {got!r} but {src}.{sfield} "
                                f"was driven as {want:#x}{rename}. The bridge "
                                f"must carry this field through unchanged.")

            # a source transaction the bridge does not model must be ignored,
            # not answered
            predictor.reset()
            spurious = [t for t in predictor.process(
                Txn("__nonexistent__", "noop", {})) if t.iface == oi]
            if spurious:
                fails.append(
                    f"a transaction on an unmodelled interface produced "
                    f"{len(spurious)} {oi!r} transaction(s); the bridge must "
                    f"emit nothing for input it does not model.")
        return fails


class LegalityCheckerGate:
    """Grades an agent-generated LegalityChecker by trying to fool it.

    A predictor is graded by asking "does it say the right thing". That
    question is meaningless for a checker, which says nothing until something
    is wrong. The right question is the inverse: DOES IT CATCH WHAT IT CLAIMS
    TO CATCH — so this gate synthesises a trace violating each id the checker
    declares in COVERS and requires a Violation carrying that id.

    Two failure modes, and both must be checked, because each alone is
    trivially passable:

      * missing a violation  -> a checker that returns nothing passes every
                                clean run and is worthless
      * flagging a legal trace -> a checker that always reports a violation
                                catches every bug and is equally worthless

    The violating traces are synthesised from checkable_rules.json, which is
    derived from the spec's own failure_taxonomy. The checker never sees them.
    """

    name = "legality_checker"

    @staticmethod
    def _rules():
        import json as _json
        with open(os.path.join(HERE, "checkable_rules.json")) as f:
            return _json.load(f)

    @classmethod
    def applies(cls, checker_cls, spec, schemas):
        from txn_contract import LegalityChecker
        if not (isinstance(checker_cls, type)
                and issubclass(checker_cls, LegalityChecker)):
            return False
        rules = cls._rules()
        return rules["interface"] in schemas

    @classmethod
    def _trace(cls, steps, rules, schemas, catalog):
        """Build a ddr_cmd transaction list from [[CMD, bank], ...]."""
        iface = rules["interface"]
        enc = {k: v for k, v in catalog[iface]["command_encoding"].items()
               if not k.startswith("$")}
        kind = next(iter(schemas[iface]["kinds"]))
        fields = schemas[iface]["kinds"][kind]

        def numeric(sv):
            # "4'b0011" -> 3
            txt = str(sv)
            if "'" in txt:
                base, digits = txt.split("'")[1][0], txt.split("'")[1][1:]
                return int(digits, {"b": 2, "h": 16, "d": 10, "o": 8}[base.lower()])
            return int(txt)

        out = []
        for i, (cmdname, bank) in enumerate(steps):
            f = {}
            for fname in fields:
                if fname == rules["command_field"]:
                    f[fname] = numeric(enc[cmdname])
                elif fname == rules["bank_field"]:
                    f[fname] = bank
                else:
                    f[fname] = 0
            out.append(Txn(iface, kind, f, seq=i))
        return out

    @classmethod
    def _run(cls, checker, trace):
        checker.reset()
        found = []
        for t in trace:
            found.extend(checker.observe(t) or [])
        found.extend(checker.final() or [])
        return found

    @classmethod
    def grade(cls, checker, spec, schemas, catalog=None):
        if catalog is None:
            catalog = _load_catalog()
        rules = cls._rules()
        covers = tuple(getattr(type(checker), "COVERS", ()) or ())
        if not covers:
            return ["COVERS is empty. Declare the failure_taxonomy ids this "
                    "checker detects (for example ('PROTO_001','PROTO_002')). "
                    "A checker that claims nothing is graded on nothing, and "
                    "claiming less is not a way to pass."]

        known = {c["id"]: c for c in rules["checkable"]}
        elsewhere = {i: g["owner"] for g in rules["not_checkable_here"]
                     for i in g["ids"]}
        fails = []

        for cid in covers:
            if cid in elsewhere:
                fails.append(
                    f"this checker claims {cid}, which a transaction-level "
                    f"checker cannot detect — it is owned by {elsewhere[cid]}. "
                    f"A checker sees the ORDER of transactions and carries no "
                    f"cycle information. Remove it from COVERS.")
                continue
            if cid not in known:
                fails.append(
                    f"this checker claims {cid}, which has no synthesisable "
                    f"violating trace in checkable_rules.json, so the claim "
                    f"cannot be verified. Claim only {sorted(known)}.")
                continue

            rule = known[cid]
            bad = cls._trace(rule["violating"], rules, schemas, catalog)
            got = cls._run(checker, bad)
            if not any(getattr(v, "taxonomy_id", "") == cid for v in got):
                other = sorted({getattr(v, "taxonomy_id", "?") for v in got})
                fails.append(
                    f"{cid}: the checker did not report a violation for a trace "
                    f"that breaks it. {rule['why']} Requirement: "
                    f"{rule['requirement']} "
                    + (f"It reported {other} instead."
                       if got else "It reported nothing at all.")
                    + f" Return a Violation with taxonomy_id={cid!r}.")

            good = cls._trace(rule["legal"], rules, schemas, catalog)
            got_ok = [v for v in cls._run(checker, good)
                      if getattr(v, "taxonomy_id", "") == cid]
            if got_ok:
                fails.append(
                    f"{cid}: the checker reported a violation on a LEGAL "
                    f"trace ({' '.join(c for c, _ in rule['legal'])}). A rule "
                    f"that fires on correct behaviour is worse than no rule — "
                    f"it trains people to ignore the checker.")
        return fails


class StageInvariantGate:
    """Grades the invariant checker a composed-path STAGE needs.

    Stages whose output stream is order-nondeterministic under the spec's
    policy (sched_cmd under FR-FCFS) cannot be checked by exact stream
    comparison, so the chain requires an agent-generated LegalityChecker over
    the stage's input AND output streams. This gate grades one the same way
    LegalityCheckerGate does — catch every claimed violation, stay silent on
    legal traces — but over multi-interface traces from
    stage_invariant_rules.json, and with one stricter demand: the checker
    must cover EVERY rule the stage lists. The rules define what the stage
    checker is for; claiming a subset is not a way to pass.
    """

    name = "stage_invariant"

    @staticmethod
    def _rules():
        import json as _json
        with open(os.path.join(HERE, "stage_invariant_rules.json")) as f:
            return _json.load(f)

    @classmethod
    def _match_stage(cls, checker_cls):
        ins = set(getattr(checker_cls, "INPUT_IFACES", ()) or ())
        outs = set(getattr(checker_cls, "OUTPUT_IFACES", ()) or ())
        for name, st in cls._rules()["stages"].items():
            if ins == set(st["input_ifaces"]) and outs == set(st["output_ifaces"]):
                return name, st
        return None, None

    @classmethod
    def applies(cls, checker_cls, spec, schemas):
        from txn_contract import LegalityChecker
        if not (isinstance(checker_cls, type)
                and issubclass(checker_cls, LegalityChecker)):
            return False
        name, st = cls._match_stage(checker_cls)
        if st is None:
            return False
        return all(i in schemas for i in
                   st["input_ifaces"] + st["output_ifaces"])

    @classmethod
    def _trace(cls, steps, stage, schemas, catalog):
        # A stage without a command stream (pure event ordering, e.g. init
        # completion versus refresh requests) has no encoding to resolve.
        enc_iface = stage.get("encoding_iface")
        enc = ({k: v for k, v in
                catalog[enc_iface]["command_encoding"].items()
                if not k.startswith("$")} if enc_iface else {})
        cmd_iface = stage.get("command_iface")
        cmd_field = stage.get("command_field")
        out = []
        for i, (iface, kind, given) in enumerate(steps):
            fields = {}
            for fname in schemas[iface]["kinds"][kind]:
                v = given.get(fname, 0)
                if iface == cmd_iface and fname == cmd_field and isinstance(v, str):
                    # Encodings are plain ints (sched side) or SystemVerilog
                    # literals like "4'b0011" (DDR pin side).
                    v = BusBridgeGate._numeric(enc[v])
                fields[fname] = v
            out.append(Txn(iface, kind, fields, seq=i))
        return out

    @classmethod
    def _run(cls, checker, trace):
        checker.reset()
        found = []
        for t in trace:
            found.extend(checker.observe(t) or [])
        found.extend(checker.final() or [])
        return found

    @classmethod
    def grade(cls, checker, spec, schemas, catalog=None):
        if catalog is None:
            catalog = _load_catalog()
        name, stage = cls._match_stage(type(checker))
        if stage is None:
            return ["this checker's INPUT_IFACES/OUTPUT_IFACES match no stage "
                    "in stage_invariant_rules.json"]

        rule_ids = [r["id"] for r in stage["rules"]]
        covers = tuple(getattr(type(checker), "COVERS", ()) or ())
        missing = [i for i in rule_ids if i not in covers]
        if missing:
            return [f"stage {name!r} requires the checker to cover ALL of "
                    f"{rule_ids}; COVERS is missing {missing}. These rules "
                    f"define what this stage checker is for — claiming a "
                    f"subset is not a way to pass."]
        unknown = [c for c in covers if c not in rule_ids]
        fails = []
        if unknown:
            fails.append(
                f"COVERS claims {unknown}, which have no synthesisable trace "
                f"for stage {name!r}, so the claim cannot be verified. Claim "
                f"exactly {rule_ids}.")

        for rule in stage["rules"]:
            cid = rule["id"]
            bad = cls._trace(rule["violating"], stage, schemas, catalog)
            got = cls._run(checker, bad)
            if not any(getattr(v, "taxonomy_id", "") == cid for v in got):
                other = sorted({getattr(v, "taxonomy_id", "?") for v in got})
                fails.append(
                    f"{cid}: no violation reported for a trace that breaks "
                    f"it. {rule['why']} Requirement: {rule['requirement']} "
                    + (f"It reported {other} instead."
                       if got else "It reported nothing at all.")
                    + f" Return a Violation with taxonomy_id={cid!r}.")

            # the rule's legal trace, plus any named legal variants (a
            # variant pins a convention: e.g. the ACTIVATE after an illegal
            # REFRESH is not a second PROTO_002, because REFRESH closes every
            # bank whether or not it was legal)
            legals = [("legal", rule["legal"])] + sorted(
                (k, v) for k, v in rule.get("legal_variants", {}).items() if not k.startswith("$"))
            for lname, ltrace in legals:
                good = cls._trace(ltrace, stage, schemas, catalog)
                got_ok = [v for v in cls._run(checker, good)
                          if getattr(v, "taxonomy_id", "") == cid]
                if got_ok:
                    fails.append(
                        f"{cid}: the checker reported a violation on a LEGAL "
                        f"trace ({lname}). A rule that fires on correct behaviour is worse "
                        f"than no rule — it trains people to ignore the checker. "
                        + (f"Requirement: {rule['requirement']} " if lname != "legal" else "")
                        + f"Legal trace: "
                        + "; ".join(f"{i}.{k} {f}" for i, k, f in ltrace))
        return fails


def _load_catalog():
    import json as _json
    with open(os.path.join(ROOT, "Validation", "txn",
                           "interface_catalog.json")) as f:
        return _json.load(f)["interfaces"]


# StageInvariantGate sits before LegalityCheckerGate: both apply() to
# LegalityChecker subclasses, and a stage checker (matched by its interface
# sets) must be graded on the stage's multi-stream rules, not on the
# single-stream ddr_cmd rules.
GATES = [RegisterMapGate, BusBridgeGate, StageInvariantGate,
         LegalityCheckerGate]


def select_gate(predictor_cls, spec, schemas):
    """The gate that can grade this predictor, or None.

    None means NO gate applies — which is not acceptance. A caller must treat
    it as 'this scope has no behavioural gate yet' and refuse to sign the
    model off on structural checks alone.
    """
    for gate in GATES:
        try:
            if gate.applies(predictor_cls, spec, schemas):
                return gate
        except TypeError:
            try:
                if gate.applies(predictor_cls, spec, schemas, _load_catalog()):
                    return gate
            except Exception:
                continue
        except Exception:
            continue
    return None
