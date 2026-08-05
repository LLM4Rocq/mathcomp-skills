#!/usr/bin/env bash
# Axiom-hygiene check: run `Print Assumptions <name>` for one or more lemmas
# in a .v file and FLAG anything beyond the expected mathcomp-analysis boolp
# trio. CI-usable: exits non-zero only when an UNEXPECTED axiom is found.
#
# The boolp `funext`/`propext`/`pselect` trio (reference.md §36) bottoms out
# in exactly these three stdlib axioms, which are EXPECTED in analysis proofs:
#   - functional_extensionality_dep
#   - propositional_extensionality
#   - constructive_indefinite_description
# Anything else (incl. admit-/Admitted-derived axioms) is a red flag.
#
# Usage:
#   print-assumptions-check.sh [opts] <file.v> <lemma...>
#   print-assumptions-check.sh [opts] --all <file.v>
#
# Options:
#   --all                scan top-level Lemma|Theorem|Corollary names in <file>
#   -R <dir> <logical>   passthrough -R to coqc (repeatable; build context)
#   -Q <dir> <logical>   passthrough -Q to coqc (repeatable; build context)
#   -p, --project FILE   read extra coqc args from a _CoqProject file
#   --strict             also fail on warnings (e.g. opaque/uncheckable)
#   -h, --help           this help
#
# Graceful degrade: no rocq/coqc -> clear message + exit 0 (never blocks).
#
# Pure bash + POSIX coreutils. Tested on macOS (BSD) and Linux (GNU).

set -u

PROG="$(basename "$0")"
ALL=0
STRICT=0
COQ_RQ=""
PROJECT=""

usage() {
  sed -n '2,27p' "$0" | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

# Expected axioms (the boolp trio's stdlib bottom). Newline-separated.
EXPECTED="functional_extensionality_dep
propositional_extensionality
constructive_indefinite_description"

add_rq() {  # $1=flag $2=dir $3=logical
  COQ_RQ="$COQ_RQ $1 $2 $3"
}

FILE=""
NAMES=""
while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage 0 ;;
    --all) ALL=1 ;;
    --strict) STRICT=1 ;;
    -R) shift; [ $# -ge 2 ] || { echo "$PROG: -R needs <dir> <logical>" >&2; exit 2; }
        add_rq -R "$1" "$2"; shift ;;
    -Q) shift; [ $# -ge 2 ] || { echo "$PROG: -Q needs <dir> <logical>" >&2; exit 2; }
        add_rq -Q "$1" "$2"; shift ;;
    -p|--project) shift; [ $# -gt 0 ] || { echo "$PROG: -p needs a file" >&2; exit 2; }
        PROJECT="$1" ;;
    --) shift; break ;;
    -*) echo "$PROG: unknown option: $1" >&2; usage 2 ;;
    *)  break ;;
  esac
  shift
done

# First positional = file; rest = lemma names.
if [ $# -gt 0 ]; then FILE="$1"; shift; fi
for a in "$@"; do
  if [ -z "$NAMES" ]; then NAMES="$a"; else NAMES="$NAMES $a"; fi
done

if [ -z "$FILE" ]; then
  echo "$PROG: no .v file given" >&2
  usage 2
fi
if [ ! -r "$FILE" ]; then
  echo "$PROG: $FILE not readable" >&2
  exit 2
fi
if [ "$ALL" -eq 0 ] && [ -z "$NAMES" ]; then
  echo "$PROG: give lemma names or use --all" >&2
  usage 2
fi

# --all: extract top-level Lemma|Theorem|Corollary names.
if [ "$ALL" -eq 1 ]; then
  NAMES="$(grep -nE '^[[:space:]]*(Lemma|Theorem|Corollary)[[:space:]]+[A-Za-z_]' "$FILE" \
    | sed -E 's/^[0-9]+:[[:space:]]*(Lemma|Theorem|Corollary)[[:space:]]+([A-Za-z_][A-Za-z0-9_'\'']*).*/\2/' \
    | tr '\n' ' ')"
  if [ -z "$(printf '%s' "$NAMES" | tr -d '[:space:]')" ]; then
    echo "$PROG: --all found no Lemma/Theorem/Corollary in $FILE" >&2
    exit 0
  fi
fi

# Locate the Rocq compiler. Rocq >= 9 ships a single `rocq` binary whose
# `c` subcommand replaces coqc; there is no `rocqc`. `coqc` survives on
# Coq <= 8.20 and via Rocq's transitional coq-core package.
COQC=""
if command -v rocq >/dev/null 2>&1; then
  COQC="rocq c"
elif command -v coqc >/dev/null 2>&1; then
  COQC="coqc"
fi

# Graceful degrade.
if [ -z "$COQC" ]; then
  echo "rocq/coqc not found -- skipping axiom check (cannot run Print Assumptions)." >&2
  echo "To check manually, append per lemma in your IDE / rocq-mcp:" >&2
  for nm in $NAMES; do echo "  Print Assumptions $nm." >&2; done
  exit 0
fi

# Read extra args from a _CoqProject (-R/-Q/-I lines), if given.
PROJ_ARGS=""
if [ -n "$PROJECT" ]; then
  if [ ! -r "$PROJECT" ]; then
    echo "$PROG: project file $PROJECT not readable" >&2; exit 2
  fi
  # Keep only -R/-Q/-I directives; drop comments and .v file lines.
  PROJ_ARGS="$(grep -E '^[[:space:]]*-(R|Q|I)\b' "$PROJECT" \
    | sed 's/#.*//' | tr '\n' ' ')"
fi

# Build a temp copy of the file with Print Assumptions appended, compile it,
# and capture output. We copy so we never mutate the user's source.
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORK="$(mktemp -d "${TMPDIR_BASE%/}/pacheck.XXXXXX")" || {
  echo "$PROG: cannot create temp dir" >&2; exit 2; }
trap 'rm -rf "$WORK"' EXIT INT TERM

BASE="$(basename "$FILE")"
VF="$WORK/$BASE"
cp "$FILE" "$VF" || { echo "$PROG: copy failed" >&2; exit 2; }
{
  printf '\n'
  for nm in $NAMES; do printf 'Print Assumptions %s.\n' "$nm"; done
} >> "$VF"

# Compile the temp copy in the source dir's context if -R/-Q point relative,
# but run from the file's directory so relative project paths resolve.
SRCDIR="$(dirname "$FILE")"
OUT="$WORK/out.txt"
# $COQC may be `rocq c`; $COQ_RQ/$PROJ_ARGS are token lists. All three are
# intentionally word-split.
# shellcheck disable=SC2086
( cd "$SRCDIR" && $COQC -q $COQ_RQ $PROJ_ARGS "$VF" ) > "$OUT" 2>&1
status=$?

if [ "$status" -ne 0 ]; then
  echo "$PROG: $COQC failed (exit $status) — likely missing build context" \
       "or mathcomp not installed. Output:" >&2
  cat "$OUT" >&2
  exit "$status"
fi

# Parse the Print Assumptions output. Axioms are listed as `name : type`
# under an "Axioms:" section. We collect every axiom identifier that is not
# in EXPECTED, plus any admit-/Admitted-derived axiom.
#
# Print Assumptions output shape:
#   Axioms:
#   classical_axioms.functional_extensionality_dep : ...
#   foo_admitted : ...           (* from Admitted *)
# It may also print "Closed under the global context" (no axioms).
UNEXPECTED="$(awk '
  /Closed under the global context/ { next }
  /^Axioms:/  { sect=1; next }
  /^Axiom:/   { sect=1; next }
  /^(Constants|Variables|Opaque|Parameters|Propositions):/ { sect=0; next }
  sect && /^[A-Za-z_]/ {
    # take the identifier up to the first ":" or whitespace; strip module path
    id=$1
    sub(/:.*$/, "", id)
    n=split(id, parts, ".")
    short=parts[n]
    print short
  }
' "$OUT" | sort -u)"

# Also detect explicit admit-derived axioms by name pattern from full output.
ADMITS="$(grep -iE '(_admitted|admit_|^[[:space:]]*[A-Za-z_].*: *admit)\b' "$OUT" \
  | sed -E 's/[[:space:]]*:.*//; s/^[[:space:]]*//' | sort -u)"

# Strict-mode warnings (opaque/uncheckable advisories from coqc).
WARNINGS="$(grep -iE 'Warning:|cannot be checked|opaque' "$OUT" || true)"

flagged=0

# Filter UNEXPECTED down to axioms NOT in the expected trio (no subshell var
# leakage: capture the filtered list into a plain variable).
REMAIN=""
if [ -n "$UNEXPECTED" ]; then
  REMAIN="$(printf '%s\n' "$UNEXPECTED" | while IFS= read -r ax; do
    [ -z "$ax" ] && continue
    printf '%s\n' "$EXPECTED" | grep -qx "$ax" || echo "$ax"
  done)"
fi

if [ -n "$REMAIN" ]; then
  printf '%s\n' "$REMAIN" | while IFS= read -r ax; do
    [ -z "$ax" ] && continue
    echo "[UNEXPECTED-AXIOM] $ax"
  done
  flagged=1
fi

if [ -n "$ADMITS" ]; then
  printf '%s\n' "$ADMITS" | while IFS= read -r a; do
    [ -z "$a" ] && continue
    echo "[ADMIT-AXIOM] $a"
  done
  flagged=1
fi

if [ -n "$WARNINGS" ]; then
  printf '%s\n' "$WARNINGS" | while IFS= read -r w; do
    [ -z "$w" ] && continue
    echo "[WARN] $w"
  done
  if [ "$STRICT" -eq 1 ]; then flagged=1; fi
fi

if [ "$flagged" -eq 0 ]; then
  echo "OK: only the expected boolp trio (or no) axioms in: $NAMES"
  exit 0
fi
exit 1
