#!/usr/bin/env bash
# Quick mechanical audit for mathcomp-style violations in a .v file.
# Catches the high-yield cross-cutting issues without launching agents.
#
# Usage: audit-quick.sh <file.v> [<file.v> ...]
# Output: one line per finding, prefixed with [§N.X] keyed to
#         reference.md sections.
#
# Uses bash + POSIX awk/grep/sed (no gawk extensions). Tested on
# Linux GNU coreutils and macOS BSD tools. On Windows, run under WSL
# or Git Bash.
# Patterns are heuristics — verify each finding before applying a
# fix. The §25 detector in particular has a high false-positive rate
# (~70-80%) on HB-heavy code; treat it as candidate-only.

set -u

if [ $# -eq 0 ]; then
  echo "usage: $0 <file.v> [<file.v> ...]" >&2
  exit 2
fi

for f in "$@"; do
  if [ ! -r "$f" ]; then
    echo "skip: $f not readable" >&2
    continue
  fi

  # ─── §1: lines > 80 chars ───
  awk -v file="$f" 'length > 80 {
    snippet = substr($0, 1, 60)
    printf "[§1] %s:%d\tline >80 chars (%d)\t%s...\n",
      file, NR, length, snippet
  }' "$f"

  # ─── §9: tactic spacing — `apply :`, `move :`, `case :`, `elim :` ───
  # House style: no space between the keyword and `:`. Excludes
  # `have :=` (different construct), `apply: foo` (correct), inside-
  # comment occurrences, and quoted strings.
  grep -nE "(^|[^a-zA-Z_])(apply|move|case|elim)[[:space:]]+:" "$f" 2>/dev/null \
    | grep -v "(\\*" \
    | awk -F: -v file="$f" '{
        ln = $1
        $1=""; $2=""
        sub(/^::/, "")
        printf "[§9] %s:%d\ttactic spacing (drop space before :)\t%s\n",
          file, ln, $0
      }'

  # ─── §22.3: candidate scope delimiters (scope-aware) ───
  # Track the most recent `Local Open Scope X.` and only flag
  # delimiters that match that scope as removable.
  awk -v file="$f" '
    /^[[:space:]]*Local Open Scope ring_scope/  { scope = "R"; next }
    /^[[:space:]]*Local Open Scope ereal_scope/ { scope = "E"; next }
    /^[[:space:]]*Local Open Scope nat_scope/   { scope = "N"; next }
    /^[[:space:]]*Local Open Scope/             { scope = "";  next }
    /^[[:space:]]*\(\*/ { next }
    {
      if (scope == "R" && match($0, /[a-zA-Z0-9_)][[:space:]]*%R/)) {
        printf "[§22.3] %s:%d\tcandidate removable %%R inside ring_scope\t%s\n",
          file, NR, $0
      }
      if (scope == "E" && match($0, /[a-zA-Z0-9_)][[:space:]]*%E/)) {
        printf "[§22.3] %s:%d\tcandidate removable %%E inside ereal_scope\t%s\n",
          file, NR, $0
      }
      if (scope == "N" && match($0, /[a-zA-Z0-9_)][[:space:]]*%N/)) {
        printf "[§22.3] %s:%d\tcandidate removable %%N inside nat_scope\t%s\n",
          file, NR, $0
      }
    }
  ' "$f"

  # ─── §23: fully-qualified module names in source body ───
  # Allow lowercase identifiers after the dot (the cases the playbook
  # actually targets: derive.derivableM, trigo.pi, exp.expRD, etc.).
  # Skip Import lines (and continuation lines) and Local Notation.
  awk -v file="$f" '
    /^[[:space:]]*Import / {
      if (/\.[[:space:]]*$/) { in_import = 0 } else { in_import = 1 }
      next
    }
    in_import { if (/\.[[:space:]]*$/) in_import = 0; next }
    /^[[:space:]]*From /          { next }
    /^[[:space:]]*\(\*/           { next }
    /^[[:space:]]*Local Notation/ { next }
    /(^|[^a-zA-Z_])(order|boolp|filter|charge|derive|ftc|exp|trigo|num_normedtype|archimedean|ereal)\.[A-Za-z_]/ {
      printf "[§23] %s:%d\tfully-qualified module name in source\t%s\n",
        file, NR, $0
    }
  ' "$f"

  # ─── §22.1: useless `have -> : ... by [].` / `have <- : ... by [].` ───
  # Multi-line aware: capture from `have ->` or `have <-` until the
  # statement-terminating `.`. Avoid leaking across statement boundaries.
  awk -v file="$f" '
    /have (->|<-) :/ && !capturing {
      capturing = 1
      buf = $0
      lineno = NR
      arrow = ($0 ~ /have <- :/) ? "<-" : "->"
      if (match($0, /by \[\]\.[[:space:]]*$/)) {
        snippet = substr(buf, 1, 80)
        printf "[§22.1] %s:%d\tcandidate useless have %s : ... by [].\t%s...\n",
          file, lineno, arrow, snippet
        capturing = 0
        next
      }
      if (match($0, /\.[[:space:]]*$/)) capturing = 0
      next
    }
    capturing {
      buf = buf " " $0
      if (match($0, /by \[\]\.[[:space:]]*$/)) {
        snippet = substr(buf, 1, 80)
        printf "[§22.1] %s:%d\tcandidate useless have %s : ... by [].\t%s...\n",
          file, lineno, arrow, snippet
        capturing = 0
      } else if (match($0, /\.[[:space:]]*$/)) {
        capturing = 0
      }
    }
  ' "$f"

  # ─── §24.1: candidate [the X of T] over canonical instances ───
  grep -nE "\[the [a-zA-Z0-9_ ]+ of " "$f" 2>/dev/null \
    | awk -F: -v file="$f" '{
        ln = $1
        line = $0
        sub("^[0-9]+:", "", line)
        printf "[§24.1] %s:%d\tcandidate useless [the X of T]\t%s\n",
          file, ln, line
      }'

  # ─── §25: @ on user lemmas (NOT HB Builders / canonical structures) ───
  # HB Builders are CamelCase after `@` (e.g., `@isFoo.Build`,
  # `@Module.Pack`). User lemmas are typically lowercase. Skip
  # idiomatic `@id`/`@idfun` and lines using `.Build`/`.Pack` (HB
  # context).
  awk -v file="$f" '
    /^[[:space:]]*\(\*/        { next }
    /\.Build|\.Pack/           { next }
    /(^|[^a-zA-Z_])@(id|idfun|comp)([^a-zA-Z_]|$)/ { next }
    /(^|[^a-zA-Z_])@[a-z][a-zA-Z0-9_]*/ {
      printf "[§25] %s:%d\tcandidate @ on user lemma (verify needed)\t%s\n",
        file, NR, $0
    }
  ' "$f"

  # ─── §27.4: name-then-immediately-consume patterns ───
  # `move=> ... H; exact: H.` — the same name introduced and then
  # immediately consumed by exact:/apply:.
  # POSIX-portable: extract candidates with grep, then verify the name
  # equality with awk.
  grep -nE "move=>.*;[[:space:]]*(by[[:space:]]+)?(exact|apply):" "$f" 2>/dev/null \
    | awk -F: -v file="$f" '
        {
          ln = $1
          line = $0
          sub("^[^:]+:[0-9]+:", "", line)
          # Get the last identifier before `;` and the identifier after `exact:`/`apply:`
          if (match(line, /move=>[^;]*[[:space:]]([a-zA-Z_][a-zA-Z0-9_]*)[[:space:]]*;/)) {
            before = substr(line, RSTART, RLENGTH)
            sub(/.* /, "", before)
            sub(/[[:space:]]*;.*/, "", before)
          } else { next }
          if (match(line, /(exact|apply):[[:space:]]+([a-zA-Z_][a-zA-Z0-9_]*)/)) {
            after = substr(line, RSTART, RLENGTH)
            sub(/^[^:]*:[[:space:]]+/, "", after)
          } else { next }
          if (before == after && length(before) > 0) {
            printf "[§27.4] %s:%d\tname-then-consume (use exact / apply)\t%s\n",
              file, ln, line
          }
        }
      '

  # ─── §27.5: `have := f; move=> [a b]` should be `have [a b] := f` ───
  grep -nE "have := .*;[[:space:]]*move=>[[:space:]]*\[" "$f" 2>/dev/null \
    | awk -F: -v file="$f" '{
        ln = $1
        line = $0
        sub("^[^:]+:[0-9]+:", "", line)
        printf "[§27.5] %s:%d\thave := X; move=> [a b] -> have [a b] := X\t%s\n",
          file, ln, line
      }'

  # ─── §27.8: 2-subgoal split followed by exactly two `-` bullets ───
  awk -v file="$f" '
    /^[[:space:]]*split\.[[:space:]]*$/ { lineno=NR; b1=0; b2=0; b3=0; armed=1; next }
    armed && /^[[:space:]]*-/  { b1++ }
    armed && /^[[:space:]]*\+/ { b2++ }
    armed && /^[[:space:]]*\*/ { b3++ }
    armed && /^[[:space:]]*Qed\./ {
      if (b1 == 2 && b2 == 0 && b3 == 0) {
        printf "[§27.8] %s:%d\tsplit + 2 bullets - drop bullets, use 2-space indent\n",
          file, lineno
      }
      armed = 0
    }
  ' "$f"

  # ─── §32.1: _is_ in lemma name on what looks like an equation ───
  grep -nE "^Lemma [a-zA-Z_]+_is_[a-z]" "$f" 2>/dev/null \
    | awk -F: -v file="$f" '{
        ln = $1
        line = $0
        sub("^[^:]+:[0-9]+:", "", line)
        printf "[§32.1] %s:%d\t_is_ suffix on lemma - rename to E if equational\t%s\n",
          file, ln, line
      }'

  # ─── §45.5: lia/nia without `Require Import zify` in the file ───
  # Stdlib lia accepts nat natively but does NOT reify divn/modn/dvdn/
  # gcdn/Order.le/eq_op. Without `From mathcomp Require Import zify`,
  # most mathcomp goals are out of reach.
  if ! grep -qE "(From [a-zA-Z._]+[[:space:]]+)?Require[[:space:]]+(Import|Export)?[[:space:]]*([a-zA-Z._]+[[:space:]]+)*zify" "$f"; then
    grep -nE "(^|[^a-zA-Z_])(lia|nia)[[:space:]]*\." "$f" 2>/dev/null \
      | awk -F: -v file="$f" '{
          ln = $1
          line = $0
          sub("^[^:]+:[0-9]+:", "", line)
          printf "[§45.5] %s:%d\tlia/nia without `From mathcomp Require Import zify`\t%s\n",
            file, ln, line
        }'
  fi

  # ─── §46.4: deprecated `Pascal` / `triangular_sum` (mathcomp 2.3.0+) ───
  # Pascal -> expnDn ; triangular_sum -> bin2_sum.
  grep -nE "(^|[^a-zA-Z_])(Pascal|triangular_sum)([^a-zA-Z_]|$)" "$f" 2>/dev/null \
    | awk -F: -v file="$f" '{
        ln = $1
        line = $0
        sub("^[^:]+:[0-9]+:", "", line)
        printf "[§46.4] %s:%d\tdeprecated lemma — use expnDn / bin2_sum\t%s\n",
          file, ln, line
      }'

  # ─── §47.4: `Definition X : {ffun ...} := fun ...` (missing builder) ───
  # `{ffun T -> R}` cannot be constructed from a raw `fun x => ...`
  # without the `[ffun x => ...]` builder (or `finfun`). Multi-line
  # aware in case the `:= fun` falls on a continuation line.
  awk -v file="$f" '
    function check_line(    snippet) {
      if (match($0, /:=[[:space:]]*fun[[:space:]]/)) {
        snippet = substr(buf, 1, 100)
        printf "[§47.4] %s:%d\tDefinition : {ffun ...} := fun (use [ffun x => ...])\t%s...\n",
          file, lineno, snippet
        armed = 0
        return 1
      }
      if (match($0, /:=[[:space:]]*\[ffun/)) { armed = 0; return 1 }
      if (match($0, /\.[[:space:]]*$/))      { armed = 0; return 1 }
      return 0
    }
    /Definition[[:space:]]+[a-zA-Z_][a-zA-Z0-9_]*([[:space:]]|[^.])*:[[:space:]]*\{ffun[[:space:]]/ {
      armed = 1; lineno = NR; buf = $0
      check_line()
      next
    }
    armed {
      buf = buf " " $0
      check_line()
    }
  ' "$f"

  # ─── §47.8: `apply: funext` on ffun-ish goals ───
  # If the file imports finfun (directly or via all_ssreflect),
  # funext is the wrong extensionality lemma — use apply/ffunP.
  if grep -qE "Require[[:space:]]+(Import|Export)?[[:space:]]*([a-zA-Z._]+[[:space:]]+)*(finfun|all_ssreflect|all_boot)" "$f"; then
    grep -nE "apply:[[:space:]]+funext" "$f" 2>/dev/null \
      | awk -F: -v file="$f" '{
          ln = $1
          line = $0
          sub("^[^:]+:[0-9]+:", "", line)
          printf "[§47.8] %s:%d\tapply: funext on ffun-context — use apply/ffunP\t%s\n",
            file, ln, line
        }'
  fi

done
