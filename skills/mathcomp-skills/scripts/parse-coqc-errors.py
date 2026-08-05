#!/usr/bin/env python3
"""Classify coqc / rocq error output into structured JSON.

Reads coqc output from a FILE argument or stdin, parses each error block
(default and `-emacs` location formats), classifies the error type with a
small regex table, and prints a JSON list of:

    {file, line, col, end_line, errorType, message}

Standard library only (no third-party deps). Python 3.

Location formats understood:

  default:
    File "theories/foo.v", line 42, characters 5-12:
    Error: <message...>

  -emacs (byte offsets, no "characters" keyword on a separate axis):
    File "theories/foo.v", line 42, characters 5-12:
    <\032 sentinel lines may appear>
    Error: <message...>

  multi-line spans (default coqc 8.16+ / Rocq):
    File "theories/foo.v", line 10, column 3, line 12, column 8:
    Error: <message...>

Usage:
    parse-coqc-errors.py [FILE]
    coqc theories/foo.v 2>&1 | parse-coqc-errors.py
    parse-coqc-errors.py --help
"""

import argparse
import json
import re
import sys

# ── error-type classification table ──────────────────────────────────────
# Ordered: first matching pattern wins. Patterns are matched case-
# insensitively against the full (possibly multi-line) error message.
CLASSIFIERS = [
    ("unification",
     re.compile(r"unable to unify|cannot unify", re.IGNORECASE)),
    ("canonical_structure",
     re.compile(
         r"cannot infer|canonical|"
         r"hb\b.*(instance|resolution)|"
         r"missing canonical|no.*canonical structure|"
         r"unable to (find|satisfy).*instance",
         re.IGNORECASE)),
    ("not_subterm",
     re.compile(r"not a subterm|recursive call.*not|"
                r"ill-formed recursive", re.IGNORECASE)),
    ("non_functional",
     re.compile(r"illegal application|non-functional construction",
                re.IGNORECASE)),
    ("scope_notation",
     re.compile(r"not found in scope|unknown interpretation|"
                r"no interpretation for|"
                r"unbound (notation|interpretation)",
                re.IGNORECASE)),
    ("universe",
     re.compile(r"universe inconsistency|universe.*incompatible",
                re.IGNORECASE)),
    ("syntax",
     re.compile(r"syntax error|illegal begin of|"
                r"^\s*error: there is no|"
                r"unexpected token|this command is incompatible",
                re.IGNORECASE)),
]

# Recognize the "hb_instance" subcase within canonical_structure for
# callers that want finer granularity (still returned as its own type).
HB_INSTANCE = re.compile(r"\bHB\b|forgetful|mixin|factory", re.IGNORECASE)

# ── location-line regexes ─────────────────────────────────────────────────
# File "X", line L, characters C-E:
RE_LOC_CHARS = re.compile(
    r'^File\s+"(?P<file>[^"]*)",\s+line\s+(?P<line>\d+),\s+'
    r'characters?\s+(?P<col>\d+)-(?P<endcol>\d+)\s*:')
# File "X", line L1, column C1, line L2, column C2: (multi-line span)
RE_LOC_SPAN = re.compile(
    r'^File\s+"(?P<file>[^"]*)",\s+line\s+(?P<line>\d+),\s+'
    r'column\s+(?P<col>\d+),\s+line\s+(?P<end_line>\d+),\s+'
    r'column\s+(?P<endcol>\d+)\s*:')
# A bare "Error:" / "Error (...)" start, with no File header (rare).
RE_ERROR_START = re.compile(r'^(Error\b|Syntax error)', re.IGNORECASE)


def classify(message):
    """Return the errorType string for a (possibly multi-line) message."""
    for name, pat in CLASSIFIERS:
        if pat.search(message):
            if name == "canonical_structure" and HB_INSTANCE.search(message):
                return "hb_instance"
            return name
    return "unknown"


def parse(text):
    """Parse coqc output text into a list of error dicts."""
    lines = text.splitlines()
    results = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        loc = None
        m = RE_LOC_SPAN.match(line)
        if m:
            loc = {
                "file": m.group("file"),
                "line": int(m.group("line")),
                "col": int(m.group("col")),
                "end_line": int(m.group("end_line")),
            }
        else:
            m = RE_LOC_CHARS.match(line)
            if m:
                loc = {
                    "file": m.group("file"),
                    "line": int(m.group("line")),
                    "col": int(m.group("col")),
                    "end_line": int(m.group("line")),
                }

        if loc is not None:
            # Gather the message: lines after the location header up to the
            # next File header / blank-separated next block / EOF.
            j = i + 1
            msg_lines = []
            while j < n:
                nxt = lines[j]
                if RE_LOC_CHARS.match(nxt) or RE_LOC_SPAN.match(nxt):
                    break
                msg_lines.append(nxt)
                j += 1
            message = "\n".join(msg_lines).strip()
            results.append({
                "file": loc["file"],
                "line": loc["line"],
                "col": loc["col"],
                "end_line": loc["end_line"],
                "errorType": classify(message),
                "message": message,
            })
            i = j
            continue

        # Location-less error (e.g. a toplevel "Error:" with no File line).
        if RE_ERROR_START.match(line):
            j = i + 1
            msg_lines = [line]
            while j < n:
                nxt = lines[j]
                if (RE_LOC_CHARS.match(nxt) or RE_LOC_SPAN.match(nxt)
                        or RE_ERROR_START.match(nxt)):
                    break
                msg_lines.append(nxt)
                j += 1
            message = "\n".join(msg_lines).strip()
            results.append({
                "file": None,
                "line": None,
                "col": None,
                "end_line": None,
                "errorType": classify(message),
                "message": message,
            })
            i = j
            continue

        i += 1

    return results


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Classify coqc/rocq error output into structured JSON.")
    parser.add_argument(
        "file", nargs="?", default="-",
        help="coqc output file to read (default: stdin)")
    parser.add_argument(
        "--indent", type=int, default=2,
        help="JSON indent (default: 2; use 0 for compact)")
    args = parser.parse_args(argv)

    if args.file == "-":
        text = sys.stdin.read()
    else:
        try:
            with open(args.file, "r", encoding="utf-8", errors="replace") as fh:
                text = fh.read()
        except OSError as exc:
            print(f"parse-coqc-errors: cannot read {args.file}: {exc}",
                  file=sys.stderr)
            return 2

    errors = parse(text)
    indent = args.indent if args.indent and args.indent > 0 else None
    json.dump(errors, sys.stdout, indent=indent)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
