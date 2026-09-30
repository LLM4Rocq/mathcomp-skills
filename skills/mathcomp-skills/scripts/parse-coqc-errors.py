#!/usr/bin/env python3
"""Classify coqc / rocq error output into structured JSON.

Reads coqc output from a FILE argument or stdin, parses each error or
warning block (default and `-emacs` location formats), classifies it
with a small regex table, and prints a JSON list of:

    {file, line, col, end_line, severity, errorType, message}

plus, for warnings only, `category` (first name of the trailing
`[cat,...]` list, e.g. "notation-overridden") and `categories` (the
whole list).

  severity   "error" or "warning" (from the first message line).
  errorType  for errors: a class from CLASSIFIERS below, or "unknown";
             for warnings: always "warning" (use `category`).

Pass --errors-only to drop the warning blocks (a bare `all_boot` import
prints 11 benign [notation-overridden] warnings). errors.md §9 says
which warning categories are benign and which are actionable.

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

  warnings (same headers, category list on the last line):
    File "theories/foo.v", line 1, characters 0-38:
    Warning: Notation "_ + _" was already used in scope nat_scope.
    [notation-overridden,parsing,default]

Usage:
    parse-coqc-errors.py [--errors-only] [FILE]
    coqc theories/foo.v 2>&1 | parse-coqc-errors.py --errors-only
    parse-coqc-errors.py --help
"""

import argparse
import json
import re
import sys

# ── error-type classification table ──────────────────────────────────────
# Ordered: first matching pattern wins. Patterns are matched case-
# insensitively against the full (possibly multi-line) error message.
# The definition-time and bookkeeping classes come first: their messages
# print the environment, where HB display names such as
# `Datatypes_nat__canonical__eqtype_Equality` would otherwise trigger
# `canonical_structure`. `bookkeeping` must also precede `syntax`
# (`rewrite: h` is reported as a syntax error mentioning [ssrrwargs]).
CLASSIFIERS = [
    # errors.md §8: Fixpoint guard failures.
    ("ill_formed_fix",
     re.compile(r"Recursive definition of .* is ill-formed|"
                r"Cannot guess decreasing argument",
                re.IGNORECASE | re.DOTALL)),
    ("non_exhaustive",
     re.compile(r"Non exhaustive pattern-matching", re.IGNORECASE)),
    ("non_positive",
     re.compile(r"Non strictly positive occurrence", re.IGNORECASE)),
    # errors.md §9: reported at Qed (open goals left by a branch).
    ("incomplete_proof",
     re.compile(r"Attempt to save an incomplete proof", re.IGNORECASE)),
    # errors.md §7: `:` push / intro pattern / clear does not fit.
    ("bookkeeping",
     re.compile(r"is used in (hypothesis|conclusion)|"
                r"was not completely instantiated|"
                r"No assumption in|"
                r"The variable \S+ was not found in the current environment|"
                r"\[ssrrwargs\]",
                re.IGNORECASE)),
    ("unification",
     re.compile(r"unable to unify|cannot unify", re.IGNORECASE)),
    ("canonical_structure",
     re.compile(
         r"cannot infer|canonical|"
         r"hb\b.*(instance|resolution)|"
         r"missing canonical|no.*canonical structure|"
         r"unable to (find|satisfy).*instance",
         re.IGNORECASE)),
    # errors.md §3: failed rewrite only (recursion errors are above).
    ("not_subterm",
     re.compile(r"not a subterm|does not match any subterm",
                re.IGNORECASE)),
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
# First message line of a warning block.
RE_WARNING = re.compile(r'^\s*Warning\b', re.IGNORECASE)
# Trailing category list of a warning: `[notation-overridden,parsing,...]`.
RE_CATEGORIES = re.compile(r'\[([A-Za-z0-9_.+-]+(?:,[A-Za-z0-9_.+-]+)*)\]\s*$')


def classify(message):
    """Return the errorType string for a (possibly multi-line) message."""
    for name, pat in CLASSIFIERS:
        if pat.search(message):
            if name == "canonical_structure" and HB_INSTANCE.search(message):
                return "hb_instance"
            return name
    return "unknown"


def make_record(loc, message):
    """Build the output dict for one error or warning block."""
    first = next((ln for ln in message.splitlines() if ln.strip()), "")
    rec = {
        "file": loc["file"],
        "line": loc["line"],
        "col": loc["col"],
        "end_line": loc["end_line"],
    }
    if RE_WARNING.match(first):
        rec["severity"] = "warning"
        rec["errorType"] = "warning"
        cats = RE_CATEGORIES.search(message)
        names = cats.group(1).split(",") if cats else []
        rec["category"] = names[0] if names else None
        rec["categories"] = names
    else:
        rec["severity"] = "error"
        rec["errorType"] = classify(message)
    rec["message"] = message
    return rec


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
            results.append(make_record(loc, message))
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
            results.append(make_record(
                {"file": None, "line": None, "col": None, "end_line": None},
                message))
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
    parser.add_argument(
        "--errors-only", action="store_true",
        help="drop warning blocks (severity == \"warning\")")
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
    if args.errors_only:
        errors = [e for e in errors if e["severity"] != "warning"]
    indent = args.indent if args.indent and args.indent > 0 else None
    json.dump(errors, sys.stdout, indent=indent)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
