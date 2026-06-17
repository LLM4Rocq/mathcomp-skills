#!/usr/bin/env bash
# Verify the `file.v:line` / `(l. NNN)` citations in this skill still
# point at the lemma/definition they claim, in an installed mathcomp.
#
# The skill cites mathcomp source by file + line number. Mathcomp
# reorganizes ~10%/year and line numbers drift silently. This script
# is the automated re-validation tool described in LAST_VERIFIED.md.
#
# Citation forms recognized in reference.md + domains/*.md:
#   `ident` (l. NNN)         -- identifier in backticks, line in (l. .)
#   `ident` (l. NNN, MMM)    -- first line number is used
#   file.v l. NNN            -- coupled file + line
#   file.v:NNN               -- coupled file + line (templates style)
# The *file* for the `(l. NNN)` form is the nearest preceding
# `mathcomp/<path>/<file>.v` reference in the same markdown file (the
# section's source-file context).
#
# Outcomes per citation:
#   ERROR  file or identifier not found at all  (rename/removal/reorg)
#   WARN   identifier found but >tolerance lines away from the citation
#   OK     identifier found within tolerance (quiet unless --verbose)
#
# Exit non-zero only on ERROR (or on WARN too, with --strict). If
# mathcomp is not installed, prints a notice and exits 0 (so it never
# breaks a contributor without the full stack) unless --require-mathcomp.
#
# Pure POSIX shell + grep/awk/sed (no gawk extensions). Tested on
# macOS (BSD tools) and Linux (GNU coreutils), matching audit-quick.sh.

set -u

PROG=$(basename "$0")
# Resolve the skill root as the parent of this script's dir, so the
# tool works regardless of the caller's working directory.
SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/.." && pwd)

TOL=5
VERBOSE=0
STRICT=0
REQUIRE_MC=0

usage() {
  cat <<EOF
$PROG -- verify mathcomp file:line citations in the skill docs.

Usage:
  $PROG [options]

Options:
  -t, --tolerance N    Max line drift before a citation WARNs (default 5).
  -v, --verbose        Also print OK citations.
  -s, --strict         Exit non-zero on WARN as well as ERROR.
      --require-mathcomp
                       Exit non-zero (instead of 0) if mathcomp is not
                       found. Use this in CI to force a real check.
  -h, --help           Show this help.

Sources scanned: reference.md and domains/*.md under the skill root.

mathcomp location (first that exists wins):
  \$MATHCOMP_ROOT
  \$(rocqc -where)/user-contrib/mathcomp
  \$(coqc  -where)/user-contrib/mathcomp
  \$(rocqc -where)/../coq/user-contrib/mathcomp   (sibling layout)

Exit codes:
  0  no ERRORs (and no WARNs under --strict); or mathcomp absent
     without --require-mathcomp.
  1  at least one ERROR (or WARN under --strict); or mathcomp absent
     with --require-mathcomp.
  2  usage error.
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    -t|--tolerance)
      [ $# -ge 2 ] || { echo "$PROG: $1 needs a value" >&2; exit 2; }
      TOL=$2; shift 2 ;;
    -v|--verbose)        VERBOSE=1; shift ;;
    -s|--strict)         STRICT=1; shift ;;
    --require-mathcomp)  REQUIRE_MC=1; shift ;;
    -h|--help)           usage; exit 0 ;;
    *) echo "$PROG: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$TOL" in
  ''|*[!0-9]*) echo "$PROG: tolerance must be a number" >&2; exit 2 ;;
esac

# ── Locate the installed mathcomp tree ────────────────────────────
find_mathcomp() {
  if [ -n "${MATHCOMP_ROOT:-}" ] && [ -d "$MATHCOMP_ROOT" ]; then
    printf '%s\n' "$MATHCOMP_ROOT"; return 0
  fi
  for tool in rocqc coqc; do
    command -v "$tool" >/dev/null 2>&1 || continue
    where=$("$tool" -where 2>/dev/null) || continue
    [ -n "$where" ] || continue
    for cand in \
      "$where/user-contrib/mathcomp" \
      "$where/../coq/user-contrib/mathcomp" \
      "$where/../coq-core/user-contrib/mathcomp"
    do
      [ -d "$cand" ] && { (cd "$cand" && pwd); return 0; }
    done
  done
  return 1
}

if ! MC=$(find_mathcomp); then
  echo "$PROG: mathcomp not found -- skipping" \
       "(install rocq/coq + mathcomp to validate citations)." >&2
  if [ "$REQUIRE_MC" -eq 1 ]; then
    echo "$PROG: --require-mathcomp set; failing." >&2
    exit 1
  fi
  exit 0
fi
echo "$PROG: using mathcomp tree at $MC" >&2

# ── Collect the markdown sources ──────────────────────────────────
SOURCES=""
[ -f "$ROOT/reference.md" ] && SOURCES="$ROOT/reference.md"
for d in "$ROOT"/domains/*.md; do
  [ -f "$d" ] && SOURCES="$SOURCES $d"
done
if [ -z "$SOURCES" ]; then
  echo "$PROG: no reference.md / domains/*.md found under $ROOT" >&2
  exit 2
fi

# ── Extract citations ─────────────────────────────────────────────
# Emit TSV: <file-rel-path>\t<ident-or-_>\t<line>\t<srcmd>:<srcline>
# A literal underscore means "no identifier captured" (file:line form).
# The current source-file context is the nearest preceding
# `mathcomp/<path>.v` mention in the same markdown file.
extract_citations() {
  for md in $SOURCES; do
    awk -v md="$md" '
      # Update the file context whenever a mathcomp path appears.
      {
        if (match($0, /mathcomp\/[A-Za-z0-9_\/]+\.v/)) {
          ctx = substr($0, RSTART, RLENGTH)
          sub(/^mathcomp\//, "", ctx)
        }
      }
      # Coupled "file.v:NNN" or "file.v l. NNN" / "file.v NNN".
      {
        line = $0
        while (match(line,
            /[A-Za-z_][A-Za-z0-9_]*\.v(:[0-9]+|[: ]+l\.[ ]?[0-9]+|[ ]+[0-9]+)/)) {
          m = substr(line, RSTART, RLENGTH)
          rest = substr(line, RSTART + RLENGTH)
          line = rest
          f = m; sub(/\.v.*$/, ".v", f)
          n = m; sub(/^[^0-9]*/, "", n)
          # Map a bare basename onto the current path context.
          path = f
          if (f !~ /\//) {
            if (ctx != "" && ctx ~ ("/" f "$")) path = ctx
          }
          printf "%s\t_\t%s\t%s:%d\n", path, n, md, NR
        }
      }
      # Backticked ident immediately followed by "(l. NNN)".
      {
        line = $0
        while (match(line, /`[A-Za-z_][A-Za-z0-9_'"'"']*`[ ]*(,[ ]*`[A-Za-z_][A-Za-z0-9_'"'"']*`[ ]*)*\(l\.[ ]?[0-9]+/)) {
          chunk = substr(line, RSTART, RLENGTH)
          line  = substr(line, RSTART + RLENGTH)
          # First backticked identifier in the chunk.
          id = chunk
          sub(/^`/, "", id); sub(/`.*$/, "", id)
          # First line number after "(l.".
          n = chunk; sub(/^.*\(l\.[ ]?/, "", n); sub(/[^0-9].*$/, "", n)
          # Skip single-letter tokens: these are notation bound vars
          # (`n`, `R`, `x`), never citable lemma/def names.
          if (length(id) < 2) continue
          if (ctx == "") continue
          printf "%s\t%s\t%s\t%s:%d\n", ctx, id, n, md, NR
        }
      }
    ' "$md"
  done
}

# ── Look up one citation in the tree ──────────────────────────────
# A declaration keyword set covering what the docs cite.
DECL_KW='Lemma|Definition|Notation|Theorem|Fixpoint|Record|Structure|Class|Variant|Inductive|HB\.instance|HB\.factory|HB\.structure|Corollary|Fact|Canonical'

n_ok=0; n_warn=0; n_err=0; n_total=0

check_one() {
  rel=$1; ident=$2; cited=$3; origin=$4
  src="$MC/$rel"
  if [ ! -f "$src" ]; then
    # Fall back to a tree-wide search by basename (file may have moved).
    base=$(basename "$rel")
    found=$(find "$MC" -name "$base" -type f 2>/dev/null | head -n 1)
    if [ -z "$found" ]; then
      n_err=$((n_err + 1))
      echo "ERROR $rel:$cited  file not found in tree" \
           "(${ident}) [$origin]"
      return
    fi
    src=$found
    echo "WARN  $rel:$cited  file moved to ${src#"$MC"/} [$origin]"
    n_warn=$((n_warn + 1))
    rel=${src#"$MC"/}
  fi

  if [ "$ident" = "_" ]; then
    # No identifier captured: just confirm the line exists in the file.
    nlines=$(awk 'END{print NR}' "$src")
    if [ "$cited" -le "$nlines" ]; then
      n_ok=$((n_ok + 1))
      [ "$VERBOSE" -eq 1 ] && echo "OK    $rel:$cited  (line present)"
    else
      n_err=$((n_err + 1))
      echo "ERROR $rel:$cited  past EOF ($nlines lines) [$origin]"
    fi
    return
  fi

  # Grep for the identifier as a declaration, collect the line numbers.
  hits=$(grep -nE "(^|[^A-Za-z0-9_.])($DECL_KW)[ ]+${ident}([^A-Za-z0-9_']|$)" \
           "$src" 2>/dev/null | cut -d: -f1)
  if [ -z "$hits" ]; then
    # Looser fallback: ident at start of a declaration without the kw
    # on the same token (e.g. multi-line statements, HB notations).
    hits=$(grep -nE "(^|[^A-Za-z0-9_.])${ident}[ ]+:" "$src" 2>/dev/null \
             | cut -d: -f1)
  fi
  if [ -z "$hits" ]; then
    n_err=$((n_err + 1))
    echo "ERROR $rel:$cited  '$ident' not declared in file [$origin]"
    return
  fi

  # Pick the hit closest to the cited line.
  best=$(printf '%s\n' "$hits" | awk -v c="$cited" '
    { d = $1 - c; if (d < 0) d = -d;
      if (NR == 1 || d < bd) { bd = d; bl = $1 } }
    END { print bl, bd }')
  newline=${best% *}
  drift=${best#* }

  if [ "$drift" -le "$TOL" ]; then
    n_ok=$((n_ok + 1))
    [ "$VERBOSE" -eq 1 ] && \
      echo "OK    $rel:$cited  $ident (drift $drift)"
  else
    n_warn=$((n_warn + 1))
    echo "WARN  $rel:$cited  $ident now at $newline" \
         "(drift $drift) -- update to (l. $newline) [$origin]"
  fi
}

# ── Drive ─────────────────────────────────────────────────────────
CITES=$(extract_citations | sort -u)
if [ -z "$CITES" ]; then
  echo "$PROG: no citations extracted (regex/sources mismatch?)" >&2
  exit 2
fi

# Use a here-doc-free loop that survives subshell variable scoping by
# reading from a temp file (counters must persist).
TMP=$(mktemp 2>/dev/null || echo "/tmp/$PROG.$$")
printf '%s\n' "$CITES" >"$TMP"
while IFS='	' read -r rel ident cited origin; do
  [ -n "$rel" ] || continue
  n_total=$((n_total + 1))
  check_one "$rel" "$ident" "$cited" "$origin"
done <"$TMP"
rm -f "$TMP"

echo "----------------------------------------------------------------"
echo "$PROG: $n_total citations  |  OK $n_ok  WARN $n_warn  ERROR $n_err"

if [ "$n_err" -gt 0 ]; then
  exit 1
fi
if [ "$STRICT" -eq 1 ] && [ "$n_warn" -gt 0 ]; then
  echo "$PROG: --strict and $n_warn warning(s); failing." >&2
  exit 1
fi
exit 0
