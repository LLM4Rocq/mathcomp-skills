# Scripts bundled with the mathcomp-skills skill

## `audit-quick.sh`

Mechanical scan of a `.v` file for high-yield mathcomp style
violations. Pure POSIX shell + grep + awk + sed; no gawk extensions.

Output is one finding per line, prefixed with the `reference.md`
section number:

```
[§N.X] file:LINE   short description   first 60 chars of line
```

### Usage

From inside a project directory:
```sh
${CLAUDE_SKILL_DIR}/scripts/audit-quick.sh theories/*.v
```

Or directly (substitute the actual path on your machine):
```sh
~/.claude/skills/mathcomp-skills/scripts/audit-quick.sh \
  path/to/file1.v path/to/file2.v
```

### Categories detected

| Tag | What it catches |
|-----|-----------------|
| `§1`     | Lines >80 chars |
| `§9`     | Tactic spacing: `apply :`, `move :`, `case :`, `elim :` (space before `:`) |
| `§22.3`  | Scope delimiters (`%R`/`%E`/`%N`) inside the matching open scope |
| `§23`    | Fully-qualified module names in source body (`derive.X`, `boolp.Y`, etc.) |
| `§22.1`  | `have -> : ... by [].` rewrites at definitional equalities |
| `§24.1`  | `[the X of T]` ascriptions (canonical-instance noise candidates) |
| `§25`    | `@` on user lemmas (HB Builders are excluded) |
| `§27.4`  | name-then-immediately-consume (`move=> H; exact: H`) |
| `§27.5`  | `have := f; move=> [a b]` should be `have [a b] := f` |
| `§27.8`  | 2-bullet `split.` followed by `-` `-` |
| `§32.1`  | `_is_` suffix on a lemma (likely an equational lemma named like a predicate) |
| `§45.5`  | `lia` / `nia` without `From mathcomp Require Import zify` in the file |
| `§46.4`  | Deprecated `Pascal` / `triangular_sum` (mathcomp 2.3.0+) — use `expnDn` / `bin2_sum` |
| `§47.4`  | `Definition X : {ffun T -> R} := fun ...` (missing `[ffun x => ...]` builder) |
| `§47.8`  | `apply: funext` in a finfun-importing file (use `apply/ffunP`) |

### False-positive expectations

- **§25** (~70-80% FP rate): the heuristic flags every `@user_lemma`,
  but `@` is required in many HB-related contexts that the script
  can't always detect from a single line. **Always verify** with the
  build before stripping.
- **§22.3** (low FP after the scope-tracking rewrite): only flags
  delimiters that match the active `Local Open Scope`. Should be
  near-zero false positives.
- **§22.1** (low FP): the multi-line matcher correctly handles
  statement boundaries.
- **§24.1** (medium FP): doesn't check if the underlying type has an
  HB instance attached; verify by reading nearby `HB.instance`.
- **§9**, **§27.4**, **§27.5**, **§27.8**, **§32.1**: very low FP rate.
- **§45.5** (low FP): keyed on the absence of any `Require ... zify`
  in the file. False positive only if zify is transitively brought in
  via a re-exporting module (rare).
- **§46.4** (zero FP for `Pascal`; can match `triangular_sum` in
  comments — verify before fixing).
- **§47.4** (low FP): keyed on `Definition ... : {ffun ...} := fun`
  exactly. Will not catch `Variable f : {ffun ...}` / `let f := fun
  ...` patterns; those need a different pass.
- **§47.8** (low FP): only fires when a finfun-importing file uses
  `apply: funext`. Will not flag `apply: funext` in non-mathcomp code.

### Portability

Pure POSIX shell + standard `grep`/`awk`/`sed`. No gawk-specific
features. Should work on macOS (BSD tools) and Linux (GNU tools).

## `check-citations.sh`

Re-validates the `file.v:line` / `(l. NNN)` citations in
`reference.md` and `domains/*.md` against an **installed** mathcomp
tree. This is the automated answer to the skill's #1 long-term risk
(citation rot): mathcomp reorganizes ~10%/year and line numbers go
stale silently. Pure POSIX shell + grep + awk + sed, like
`audit-quick.sh`.

### What it checks

For every citation it extracts the cited identifier, its line number,
and the source `.v` file (the nearest preceding
`mathcomp/<path>/<file>.v` context for the `(l. NNN)` form), then:

| Outcome | Meaning |
|---------|---------|
| `OK`    | identifier declared within the tolerance of the cited line (quiet unless `--verbose`) |
| `WARN`  | identifier found but the line drifted beyond tolerance — prints the new line and a suggested `(l. N)` fix |
| `ERROR` | the file or the identifier is gone (rename / removal / reorg — the fatal case) |

Single-letter backticked tokens (`n`, `R`, `x` — notation bound vars)
are skipped; they are never citable lemma names.

### Usage

```sh
${CLAUDE_SKILL_DIR}/scripts/check-citations.sh [options]
```

| Option | Effect |
|--------|--------|
| `-t, --tolerance N` | max line drift before a citation WARNs (default `5`) |
| `-v, --verbose`     | also print `OK` citations |
| `-s, --strict`      | exit non-zero on WARN as well as ERROR |
| `--require-mathcomp`| exit non-zero (instead of 0) when mathcomp is absent |
| `-h, --help`        | usage |

### Finding the mathcomp tree

First match wins:
`$MATHCOMP_ROOT` → `$(rocqc -where)/user-contrib/mathcomp` →
`$(coqc -where)/user-contrib/mathcomp` → a sibling `../coq/...` layout.

### Graceful degrade

If neither `rocqc`/`coqc` nor a mathcomp tree is present, the script
prints `mathcomp not found -- skipping` and **exits 0**, so a
contributor without the full stack is never blocked. Pass
`--require-mathcomp` (CI does) to turn that into a hard failure.

### Exit codes

| Code | Meaning |
|------|---------|
| `0`  | no ERRORs (and no WARNs under `--strict`); or mathcomp absent without `--require-mathcomp` |
| `1`  | at least one ERROR (or WARN under `--strict`); or mathcomp absent with `--require-mathcomp` |
| `2`  | usage error |

The weekly `.github/workflows/citations.yml` job opam-installs the
pinned stack (Rocq 9.1.1 / mathcomp 2.5.0 / analysis 1.16.0) and runs
`check-citations.sh --strict --require-mathcomp`, so drift surfaces as
a failed scheduled run.

## `search-mathcomp.sh`

CLI wrapper that operationalizes reference.md §37 (Search discipline):
builds a tiny temp `.v` with the right imports and runs `Search` /
`About` / `Print` (incl. `Print HB.structures` / `HB.about X`) against
mathcomp via `coqc -q`. Pure POSIX shell.

### Usage

```sh
search-mathcomp.sh [opts] <query...>
```

| Option | Effect |
|--------|--------|
| `-i "<import line>"` | override the import line (default `From mathcomp Require Import all_ssreflect.`) |
| `-m <Module>` | `Search <query> inside <Module>.` |
| `--outside <Module>` | `Search <query> outside <Module>.` |
| `--about <NAME>` | `About <NAME>.` instead of Search |
| `--print <NAME>` | `Print <NAME>.` (e.g. `--print HB.structures`, `--print "HB.about T"`) |
| `-R <dir> <logical>` | passthrough `-R` to coqc (repeatable; project context) |
| `-Q <dir> <logical>` | passthrough `-Q` to coqc (repeatable; project context) |
| `-h, --help` | usage |

Query forms (anything coqc's `Search` accepts):

```sh
search-mathcomp.sh "_le"                     # Search "_le".
search-mathcomp.sh "(?x + ?y)"               # Search (?x + ?y).
search-mathcomp.sh -m ssrnat "addn"          # Search addn inside ssrnat.
search-mathcomp.sh -i "From mathcomp Require Import all_analysis." "_ @ _"
search-mathcomp.sh --about addnC             # About addnC.
```

### Graceful degrade

If neither `rocqc` nor `coqc` is on `PATH`, the script prints the exact
import + `Search ...` lines to paste into your IDE or the rocq-mcp
`rocq_query` tool, and **exits 0**.

### Exit codes

| Code | Meaning |
|------|---------|
| `0`  | query ran (or graceful-degrade paste emitted) |
| `2`  | usage error (bad/missing option or empty query) |
| other | the coqc exit status (mathcomp absent, or query/import error) |

## `parse-coqc-errors.py`

Stdlib-only Python 3 classifier: reads coqc/rocqc error output from a
file arg or stdin (default and `-emacs` location formats, plus multi-line
`line L, column C, line L2, column C2` spans) and emits a JSON list of
`{file, line, col, end_line, errorType, message}`.

### Usage

```sh
coqc theories/foo.v 2>&1 | scripts/parse-coqc-errors.py
scripts/parse-coqc-errors.py errors.log
scripts/parse-coqc-errors.py --help          # also: --indent 0 for compact
```

### `errorType` classification

First matching pattern wins (case-insensitive):

| `errorType` | Triggered by (regex gist) |
|-------------|---------------------------|
| `unification` | `Unable to unify` / `Cannot unify` |
| `hb_instance` | a `canonical_structure` match that also mentions `HB` / `mixin` / `factory` / `forgetful` |
| `canonical_structure` | `Cannot infer`, `canonical`, HB instance/resolution, `unable to find/satisfy ... instance` |
| `not_subterm` | `not a subterm`, `recursive call ... not`, `ill-formed recursive` |
| `non_functional` | `Illegal application`, `Non-functional construction` |
| `scope_notation` | `not found in scope`, `Unknown interpretation`, `No interpretation for` |
| `universe` | `Universe inconsistency` |
| `syntax` | `Syntax error`, `Illegal begin of`, `Unexpected token`, … |
| `unknown` | fallback (no pattern matched) |

Standard library only — no third-party deps. Python 3.

## `print-assumptions-check.sh`

Axiom-hygiene gate. Runs `Print Assumptions <name>` for one or more
lemmas in a `.v` file (or `--all` to scan top-level `Lemma|Theorem|
Corollary`) and **flags any axiom beyond the expected mathcomp-analysis
boolp trio**. The boolp `funext`/`propext`/`pselect` lemmas
(reference.md §36) bottom out in exactly these three stdlib axioms,
which are EXPECTED in analysis proofs:

- `functional_extensionality_dep`
- `propositional_extensionality`
- `constructive_indefinite_description`

Anything else — including `admit`/`Admitted`-derived axioms — is
reported as `[UNEXPECTED-AXIOM]` / `[ADMIT-AXIOM]`.

### Usage

```sh
print-assumptions-check.sh [opts] <file.v> <lemma...>
print-assumptions-check.sh [opts] --all <file.v>
```

| Option | Effect |
|--------|--------|
| `--all` | scan top-level `Lemma|Theorem|Corollary` names in `<file>` |
| `-R <dir> <logical>` | passthrough `-R` to coqc (build context; repeatable) |
| `-Q <dir> <logical>` | passthrough `-Q` to coqc (build context; repeatable) |
| `-p, --project FILE` | read extra `-R/-Q/-I` args from a `_CoqProject` |
| `--strict` | also fail on warnings (opaque/uncheckable advisories) |
| `-h, --help` | usage |

It copies the file to a temp dir, appends the `Print Assumptions`
commands, and compiles the copy (never mutates your source).

### Graceful degrade

No `rocqc`/`coqc` on `PATH` -> prints the `Print Assumptions <name>.`
lines to run manually and **exits 0** (never blocks).

### Exit codes (CI-usable)

| Code | Meaning |
|------|---------|
| `0`  | only the expected trio (or no) axioms; or graceful degrade |
| `1`  | at least one unexpected / admit-derived axiom (or a warning under `--strict`) |
| `2`  | usage error |
| other | the coqc exit status (missing build context / mathcomp absent) |

## `lint-markdown.sh`

Lints the skill's own markdown against the rules it preaches. Used by
`.github/workflows/markdown-lint.yml` on every push/PR (no opam).

| Tag | What it catches |
|-----|-----------------|
| `[width]` | a line **inside a ```coq / ```rocq fence** longer than 80 cols (the §1 rule applied to the guide's own code samples) |
| `[fence]` | an odd number of ` ``` ` markers in a file (unbalanced fence) |
| `[ph]`    | `TODO`/`FIXME`/`XXX` markers and empty code fences |

Fence imbalance always fails. `--warn-width` / `--warn-ph` downgrade
those categories to advisory (the CI uses them, since the corpus has
intentional >80 examples and documents the `TODO:` convention).
`--max-col N` overrides the limit. Bare `...` is **not** flagged — it
is idiomatic elision throughout these docs.

```sh
scripts/lint-markdown.sh [--warn-width] [--warn-ph] [--max-col N] f.md ...
```

## Multi-agent audit (no script — use Claude's Agent tool)

For a thorough audit, launch parallel agents. The prompt template
is in `playbook.md` § "Multi-agent audit workflow". Pseudo-pattern:

```
For file_group in [PR-1 file 1, PR-1 file 2, all other files split into N batches]:
    spawn an Agent with the audit prompt
After all return, run the consolidator prompt to merge into a single
ranked punch list.
```

The skill body (`SKILL.md`) instructs Claude to do this when the
user asks for an audit; you don't run it as a shell script.

## Live proof inspection (no script — use rocq-mcp)

When working on a specific proof, use the rocq-mcp MCP tools listed
in `SKILL.md` § "rocq-mcp integration" rather than a custom script.
They expose Rocq's interactive engine directly: `rocq_compile`,
`rocq_compile_file`, `rocq_check`, `rocq_query`, `rocq_step_multi`,
etc.
