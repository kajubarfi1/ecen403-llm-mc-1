#!/usr/bin/env python3
"""
+======================================================================+
|                    USE-CASE GOAL PROFILES                            |
|                                                                      |
|  Deterministic. No LLM. Canned domain knowledge, not model output.   |
|                                                                      |
|  The leading question the CLI asks before English intake: "what's    |
|  the primary goal for this controller?" Each profile is a fixed set  |
|  of recommendations (drawn from Spec/customizable_parameters_guide.md |
|  Tier-1 tradeoff table) plus a Tier-1/2 "bias" the intake agent is    |
|  told to prefer unless the user's own words say otherwise.           |
+======================================================================+
"""
from __future__ import annotations

GOALS: dict[str, dict] = {
    "performance": {
        "label": "Best performance",
        "summary": "Maximize bandwidth and minimize access latency.",
        "recommend": [
            "Higher speed grade (DDR3-1600) for maximum bandwidth",
            "FR-FCFS scheduler -- ~20-40% better bandwidth utilization than "
            "in-order, at the cost of more area (comparators, reorder logic)",
            "Open-page row policy -- faster for sequential/locality workloads",
            "Deeper command queue (16-32) and lookahead (8-16) for more "
            "reordering opportunity",
            "More byte lanes if pin/area budget allows -- wider channel, "
            "more bandwidth",
        ],
        "tradeoffs": "Larger area (deep queue, comparators, reorder logic) "
                     "and higher power than a cost- or power-optimized build.",
        "bias": {"speed_grade": "DDR3-1600", "scheduler_policy": "fr_fcfs",
                 "row_policy": "open_page", "command_queue_depth": 32,
                 "lookahead_depth": 16, "byte_lanes": 4},
    },
    "power": {
        "label": "Best power savings",
        "summary": "Minimize energy per access and idle power draw.",
        "recommend": [
            "Lower speed grade (DDR3-800/1066) -- lower switching activity",
            "Close-page row policy -- avoids holding rows open, better for "
            "power-sensitive/idle-heavy workloads",
            "Auto self-refresh -- powers the DRAM down automatically when idle",
            "Fewer byte lanes -- less I/O switching power",
            "Smaller command queue -- less always-on flip-flop logic",
        ],
        "tradeoffs": "Lower peak bandwidth; close-page hurts latency on "
                     "sequential/streaming access patterns.",
        "bias": {"speed_grade": "DDR3-800", "row_policy": "close_page",
                 "self_refresh_mode": "auto", "command_queue_depth": 4,
                 "byte_lanes": 1},
    },
    "cost": {
        "label": "Lowest cost / smallest area",
        "summary": "Minimize die area and part cost.",
        "recommend": [
            "Lower speed grade -- simpler timing closure, cheaper PHY",
            "Single byte lane and a smaller density (1Gb/2Gb) -- smallest, "
            "cheapest device",
            "In-order scheduler -- no reorder/comparator logic",
            "ECC off -- no extra byte lane",
            "Small command queue (4) -- minimal flip-flops",
        ],
        "tradeoffs": "Lowest bandwidth and the worst tolerance to random-"
                     "access or bursty workloads.",
        "bias": {"speed_grade": "DDR3-800", "density": "2Gb", "byte_lanes": 1,
                 "scheduler_policy": "in_order", "ecc_mode": 0,
                 "command_queue_depth": 4},
    },
    "balanced": {
        "label": "Balanced / not sure yet",
        "summary": "A reasonable default with no extreme tradeoff.",
        "recommend": [
            "Mid speed grade (DDR3-1333) -- solid bandwidth without the "
            "tightest timing margins",
            "FR-FCFS + open-page -- good general-purpose performance",
            "2 byte lanes, moderate command queue depth (16)",
        ],
        "tradeoffs": "Not optimal on any single axis, but a safe starting "
                     "point you can push toward performance/power/cost later.",
        "bias": {"speed_grade": "DDR3-1333", "scheduler_policy": "fr_fcfs",
                 "row_policy": "open_page", "byte_lanes": 2,
                 "command_queue_depth": 16},
    },
}

GOAL_ORDER = ["performance", "power", "cost", "balanced"]


def list_goals() -> list[tuple[str, str]]:
    return [(k, GOALS[k]["label"]) for k in GOAL_ORDER]


def describe_goal(key: str) -> str:
    """Human-readable recommendation block for a goal key."""
    g = GOALS[key]
    lines = [f"Goal: {g['label']} -- {g['summary']}", "Recommended for this goal:"]
    lines += [f"  - {r}" for r in g["recommend"]]
    lines.append(f"Tradeoff: {g['tradeoffs']}")
    return "\n".join(lines)


# Same Tier-1/2/3 breakdown as Spec/customizable_parameters_guide.md --
# "what's a knob on this controller and what does turning it cost you."
# (name, tradeoff, range/options)
CUSTOMIZABLE: dict[str, list[tuple[str, str, str]]] = {
    "Tier 1 -- high impact, pick these first": [
        ("Speed grade",
         "Higher speed = more bandwidth but tighter timing margins, harder "
         "PHY design, higher power",
         "DDR3-800 / 1066 / 1333 / 1600"),
        ("Device density",
         "Larger density = more capacity per chip but longer tRFC (refresh "
         "penalty)",
         "1Gb / 2Gb / 4Gb / 8Gb"),
        ("Ranks",
         "More ranks = more capacity but higher power, ODT complexity, "
         "rank-switching latency",
         "1-4"),
        ("Byte lanes",
         "More lanes = wider data bus = more bandwidth but more pins, "
         "area, power",
         "1-8"),
        ("ECC mode",
         "ECC adds reliability but costs an extra byte lane, reduces "
         "usable bandwidth ~12%, increases latency",
         "0 off, 1 SEC-DED, 2, 3"),
        ("Scheduler policy",
         "FR-FCFS gives ~20-40% better bandwidth utilization than "
         "in-order, but costs more area (comparators, reorder logic)",
         "in_order / fr_fcfs"),
        ("Row policy",
         "Open-page is faster for sequential/locality workloads; "
         "close-page is better for random access and saves power",
         "open_page / close_page"),
    ],
    "Tier 2 -- medium impact, advanced options": [
        ("Command queue depth",
         "Deeper queue = more reordering opportunity = better bandwidth, "
         "but more area (flip-flops, comparators) and more latency for "
         "lightly-loaded traffic",
         "4-32"),
        ("Lookahead depth",
         "Higher lookahead = smarter scheduling but more combinational "
         "logic, longer critical path",
         "0-16, <= queue depth"),
        ("Address mapping",
         "Row-bank-column is better for sequential access; bank-row-column "
         "is better for interleaving across banks with random access",
         "row-bank-column / bank-row-column"),
        ("Burst length",
         "BL8 is standard and higher bandwidth; BL4 (burst chop) reduces "
         "latency for small transfers at the cost of bus efficiency",
         "4 / 8"),
        ("Host bus data width",
         "Wider bus = higher throughput from the host but more routing "
         "area, potentially harder timing closure",
         "32 / 64 / 128 bits"),
        ("Read / write buffer depth",
         "Deeper buffers absorb burst traffic better but cost SRAM area",
         "4-64"),
        ("Interface type",
         "Pipelined Wishbone gives ~2x throughput over classic but is "
         "more complex",
         "wishbone_classic / wishbone_pipelined"),
        ("Self-refresh mode",
         "Auto self-refresh saves power when idle but adds wake-up "
         "latency",
         "disabled / manual / auto"),
    ],
    "Tier 3 -- implementation tuning, usually backend-facing": [
        ("Target frequency",
         "Higher controller frequency = more throughput but harder timing "
         "closure, more power",
         "100-300 MHz"),
        ("Area optimization goal",
         "Area-optimized = smaller die, cheaper; performance-optimized = "
         "faster, larger",
         "area / balanced / performance"),
        ("Power optimization goal",
         "Low-power = clock gating, fewer buffers; performance = "
         "always-on, deeper pipelines",
         "low_power / balanced / performance"),
        ("Pipeline latency",
         "More pipeline stages = easier timing closure at high frequency "
         "but adds fixed latency to every transaction",
         "1-4 cycles"),
    ],
}


def describe_customizable() -> str:
    """Human-readable Tier-1/2/3 knob listing for the 'what can I "
    customize' menu option -- no LLM, straight from the parameter guide."""
    lines = ["What's customizable on this DDR3 memory controller:"]
    for tier, params in CUSTOMIZABLE.items():
        lines.append(f"\n{tier}:")
        for name, tradeoff, rng in params:
            lines.append(f"  - {name}  [{rng}]")
            lines.append(f"      {tradeoff}")
    lines.append("\nEverything else (tRCD, tRP, CL, CWL, tRFC, ...) is never "
                 "user-set -- it's derived automatically from JEDEC tables "
                 "once you pick speed grade + density.")
    return "\n".join(lines)


def goal_prompt_context(key: str) -> str:
    """Text block injected into the LLM request so the intake agent treats
    this goal's bias as the default direction, overridable by the user's
    own words."""
    g = GOALS[key]
    bias = ", ".join(f"{k}={v}" for k, v in g["bias"].items())
    return (f"Primary stated goal: {g['label']} ({g['summary']}).\n"
            f"Recommended defaults for this goal unless the user's request "
            f"says otherwise: {bias}.\n"
            f"Tradeoff the user is implicitly accepting: {g['tradeoffs']}")
