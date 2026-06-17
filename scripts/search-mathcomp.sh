#!/usr/bin/env bash
# Run a Rocq Search / About / Print query against mathcomp from the CLI.
# Operationalizes reference.md §37 (Search discipline): build a tiny .v with
# the right imports, run `coqc -q` on it, and print the results.
#
# Usage:
#   search-mathcomp.sh [opts] <query...>
#
# Options:
#   -i "<import line>"   override the import line
#                        (default: From mathcomp Require Import all_ssreflect.)
#   -m <Module>          run `Search <query> inside <Module>.`
#   --outside <Module>   run `Search <query> outside <Module>.`
#   --about <NAME>       run `About <NAME>.` instead of Search
#   --print <NAME>       run `Print <NAME>.` instead of Search
#                        (NAME may be `HB.structures` / `HB.about X`)
#   -R <dir> <logical>   passthrough -R to coqc (repeatable; project context)
#   -Q <dir> <logical>   passthrough -Q to coqc (repeatable; project context)
#   -h, --help           this help
#
# Query forms (anything coqc's Search accepts):
#   name substring:   "_le"        -> Search "_le".
#   term pattern:     "(?x + ?y)"  -> Search (?x + ?y).
#   head pattern:     "_ (_ + _)"  -> Search _ (_ + _).
#
# Graceful degrade: if no rocqc/coqc on PATH, print the exact `Search ...`
# command to paste into your IDE / rocq-mcp `rocq_query` and exit 0.
#
# Pure bash + POSIX coreutils. Tested on macOS (BSD) and Linux (GNU).

set -u

PROG="$(basename "$0")"
IMPORTS="From mathcomp Require Import all_ssreflect."
MODE="search"        # search | about | print
INSIDE=""
OUTSIDE=""
NAME=""

usage() {
  sed -n '2,29p' "$0" | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

# Collect -R/-Q passthrough into an array (portable: use positional rebuild).
COQ_RQ=""
add_rq() {  # $1=flag(-R/-Q) $2=dir $3=logical
  COQ_RQ="$COQ_RQ $1 $2 $3"
}

QUERY=""
while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help) usage 0 ;;
    -i) shift; [ $# -gt 0 ] || { echo "$PROG: -i needs an argument" >&2; exit 2; }
        IMPORTS="$1" ;;
    -m) shift; [ $# -gt 0 ] || { echo "$PROG: -m needs a module" >&2; exit 2; }
        INSIDE="$1" ;;
    --outside) shift; [ $# -gt 0 ] || { echo "$PROG: --outside needs a module" >&2; exit 2; }
        OUTSIDE="$1" ;;
    --about) shift; [ $# -gt 0 ] || { echo "$PROG: --about needs a name" >&2; exit 2; }
        MODE="about"; NAME="$1" ;;
    --print) shift; [ $# -gt 0 ] || { echo "$PROG: --print needs a name" >&2; exit 2; }
        MODE="print"; NAME="$1" ;;
    -R) shift; [ $# -ge 2 ] || { echo "$PROG: -R needs <dir> <logical>" >&2; exit 2; }
        add_rq -R "$1" "$2"; shift ;;
    -Q) shift; [ $# -ge 2 ] || { echo "$PROG: -Q needs <dir> <logical>" >&2; exit 2; }
        add_rq -Q "$1" "$2"; shift ;;
    --) shift; break ;;
    -*) echo "$PROG: unknown option: $1" >&2; usage 2 ;;
    *)  break ;;
  esac
  shift
done

# Remaining args form the query body (joined with spaces).
for a in "$@"; do
  if [ -z "$QUERY" ]; then QUERY="$a"; else QUERY="$QUERY $a"; fi
done

# Build the command string we want Rocq to run.
build_command() {
  case "$MODE" in
    about) printf 'About %s.' "$NAME" ;;
    print) printf 'Print %s.' "$NAME" ;;
    search)
      _q="Search $QUERY"
      if [ -n "$INSIDE" ];  then _q="$_q inside $INSIDE"; fi
      if [ -n "$OUTSIDE" ]; then _q="$_q outside $OUTSIDE"; fi
      printf '%s.' "$_q"
      ;;
  esac
}

if [ "$MODE" = "search" ] && [ -z "$QUERY" ]; then
  echo "$PROG: no query given" >&2
  usage 2
fi

CMD="$(build_command)"

# Locate the Rocq compiler.
COQC=""
if command -v rocqc >/dev/null 2>&1; then
  COQC="rocqc"
elif command -v coqc >/dev/null 2>&1; then
  COQC="coqc"
fi

# Graceful degrade: no compiler — print the paste-able query and exit 0.
if [ -z "$COQC" ]; then
  echo "rocqc/coqc not found -- paste this into your IDE or rocq-mcp rocq_query:" >&2
  echo "$IMPORTS"
  echo "$CMD"
  exit 0
fi

# Build a temp .v and compile it.
TMPDIR_BASE="${TMPDIR:-/tmp}"
WORK="$(mktemp -d "${TMPDIR_BASE%/}/searchmc.XXXXXX")" || {
  echo "$PROG: cannot create temp dir" >&2; exit 2; }
trap 'rm -rf "$WORK"' EXIT INT TERM
VF="$WORK/query.v"

{
  printf '%s\n' "$IMPORTS"
  printf '%s\n' "$CMD"
} > "$VF"

# coqc -q : ignore rcfiles. $COQ_RQ is intentionally word-split (token list).
# shellcheck disable=SC2086
"$COQC" -q $COQ_RQ "$VF"
status=$?

if [ "$status" -ne 0 ]; then
  echo "$PROG: $COQC exited $status (mathcomp not installed, or query/import error)." >&2
  echo "$PROG: query was:" >&2
  echo "  $IMPORTS" >&2
  echo "  $CMD" >&2
fi
exit "$status"
