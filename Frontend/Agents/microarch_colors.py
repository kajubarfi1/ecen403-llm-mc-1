#!/usr/bin/env python3
"""
Minimal ANSI color helpers shared by microarch_cli.py and microarch_agent.py,
so the goal menu, recommendation previews, and resolved-config printouts
look the same regardless of which entry point is driving them.

Auto-disables for non-tty stdout (redirected/piped/--json output) or when
NO_COLOR is set, so scripted use stays clean plain text.
"""
from __future__ import annotations

import os
import sys

ENABLED = (sys.stdout.isatty()
           and os.environ.get("TERM") != "dumb"
           and "NO_COLOR" not in os.environ)

_CODES = {
    "reset": "0", "bold": "1", "dim": "2",
    "red": "31", "green": "32", "yellow": "33", "blue": "34",
    "magenta": "35", "cyan": "36", "white": "37",
}


def c(text: str, *styles: str) -> str:
    """Wrap text in the given style codes (e.g. c('x', 'bold', 'cyan'))."""
    if not ENABLED or not styles:
        return text
    codes = ";".join(_CODES[s] for s in styles)
    return f"\033[{codes}m{text}\033[0m"


def header(text: str) -> str:
    return c(text, "bold", "cyan")


def label(text: str) -> str:
    return c(text, "bold")


def prompt(text: str) -> str:
    return c(text, "bold", "cyan")


def ok(text: str) -> str:
    return c(text, "green")


def warn(text: str) -> str:
    return c(text, "yellow")


def err(text: str) -> str:
    return c(text, "red", "bold")


def dim(text: str) -> str:
    return c(text, "dim")


def accent(text: str) -> str:
    return c(text, "magenta")
