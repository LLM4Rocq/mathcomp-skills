#!/usr/bin/env bash
# Lint the skill's own markdown against the rules it preaches.
#
# Checks:
#   width   lines INSIDE a ```coq / ```rocq fence longer than 80 cols
#           (the guide's §1 rule applied to its own code samples).
#   fence   unbalanced ``` fences (odd count in a file).
#   ph      stray authoring leftovers: TODO/FIXME/XXX markers and
#           empty ```...``` code fences. (Bare "..." is intentional
#           elision in this corpus, so it is NOT flagged.)
#
# Each finding is one line:  [tag] file:line  message
#
# Exit codes:
#   0  clean (or only --warn categories triggered).
#   1  a blocking category triggered (fence imbalance always blocks;
#      width/ph block only without --warn-width / --warn-ph).
#   2  usage error.
#
# Pure POSIX shell + awk/grep. Tested on macOS (BSD) and Linux (GNU),
# matching audit-quick.sh.

set -u

PROG=$(basename "$0")
WARN_WIDTH=0
WARN_PH=0
MAXCOL=80

usage() {
  cat <<EOF
$PROG -- lint the skill's markdown against its own §1 / hygiene rules.

Usage:
  $PROG [options] <file.md> [<file.md> ...]

Options:
  --warn-width   Report >${MAXCOL}-col fenced lines but do not fail on them.
  --warn-ph      Report stray placeholders but do not fail on them.
  --max-col N    Override the column limit (default ${MAXCOL}).
  -h, --help     Show this help.

Fence imbalance always fails (exit 1). With no --warn-* flag, width
and placeholder findings also fail.
EOF
}

FILES=""
while [ $# -gt 0 ]; do
  case "$1" in
    --warn-width) WARN_WIDTH=1; shift ;;
    --warn-ph)    WARN_PH=1; shift ;;
    --max-col)
      [ $# -ge 2 ] || { echo "$PROG: --max-col needs a value" >&2; exit 2; }
      MAXCOL=$2; shift 2 ;;
    -h|--help)    usage; exit 0 ;;
    -*) echo "$PROG: unknown option '$1'" >&2; usage >&2; exit 2 ;;
    *)  FILES="$FILES $1"; shift ;;
  esac
done

[ -n "$FILES" ] || { echo "$PROG: no files given" >&2; usage >&2; exit 2; }
case "$MAXCOL" in ''|*[!0-9]*)
  echo "$PROG: --max-col must be a number" >&2; exit 2 ;;
esac

n_width=0; n_fence=0; n_ph=0

for f in $FILES; do
  if [ ! -r "$f" ]; then
    echo "$PROG: skip $f (not readable)" >&2
    continue
  fi

  # width + fence balance in one awk pass.
  out=$(awk -v file="$f" -v maxcol="$MAXCOL" '
    /^[[:space:]]*```/ { fences++ }
    /^[[:space:]]*```(coq|rocq)[[:space:]]*$/ && !inb { inb=1; next }
    /^[[:space:]]*```/ && inb { inb=0; next }
    inb && length > maxcol {
      printf "[width] %s:%d  fenced code line %d cols (>%d)\n",
        file, NR, length, maxcol
      w++
    }
    END {
      if (fences % 2 != 0)
        printf "[fence] %s:EOF  unbalanced ``` (%d fence markers)\n",
          file, fences
      printf "@@ %d %d\n", w, (fences % 2)
    }
  ' "$f")
  stats=$(printf '%s\n' "$out" | sed -n 's/^@@ //p')
  printf '%s\n' "$out" | grep -v '^@@ ' | grep -E '^\[' || true
  # Intentional word-split: $stats is "<width> <fence>" (two integers).
  # shellcheck disable=SC2086
  set -- $stats
  n_width=$((n_width + ${1:-0}))
  n_fence=$((n_fence + ${2:-0}))

  # Stray authoring leftovers. In these docs "..." and "<name>" are
  # *intentional* (elision, notation grammars, naming grammar), so we
  # do NOT flag them. We flag unambiguous leftovers: TODO/FIXME/XXX
  # markers, and empty code fences (``` immediately followed by ```).
  ph=$(awk -v file="$f" '
    /(^|[^A-Za-z])(TODO|FIXME|XXX)([^A-Za-z]|$)/ {
      printf "[ph]    %s:%d  TODO/FIXME/XXX marker\n", file, NR
    }
    /^[[:space:]]*```/ {
      if (prev_fence && NR == prev_ln + 1)
        printf "[ph]    %s:%d  empty code fence\n", file, NR
      prev_fence = 1; prev_ln = NR; next
    }
    { prev_fence = 0 }
  ' "$f")
  if [ -n "$ph" ]; then
    cnt=$(printf '%s\n' "$ph" | grep -c .)
    n_ph=$((n_ph + cnt))
    printf '%s\n' "$ph"
  fi
done

echo "----------------------------------------------------------------"
echo "$PROG: width $n_width  fence $n_fence  placeholder $n_ph"

rc=0
[ "$n_fence" -gt 0 ] && rc=1
[ "$n_width" -gt 0 ] && [ "$WARN_WIDTH" -eq 0 ] && rc=1
[ "$n_ph"    -gt 0 ] && [ "$WARN_PH"    -eq 0 ] && rc=1
exit "$rc"
