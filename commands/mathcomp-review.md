---
name: mathcomp-review
description: Read-only mathcomp / mathcomp-analysis style review of .v files
user_invocable: true
argument-hint: "[file.v ...] | --scope=changed|project"
---

# mathcomp-review

Read-only style review of math-comp / mathcomp-analysis Rocq (`.v`)
files. Runs the mechanical scanner, the SKILL.md Reviewer Checklist,
and axiom hygiene, then emits a structured punch list keyed to
`reference.md` section numbers.

**Non-destructive:** never edits, stages, or commits `.v` files. Every
finding is a CANDIDATE — the build is the oracle.

## Usage

```
/mathcomp-review                       # changed .v files (git diff)
/mathcomp-review theories/foo.v        # one explicit target
/mathcomp-review theories/*.v          # several explicit targets
/mathcomp-review --scope=project       # whole project (prompts first)
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | One or more `.v` files (or a directory) to review |
| --scope | No | `changed` (default), `project`, or implicit when targets set |

Defaults:
- No args → `--scope=changed` (files modified since last commit).
- One or more targets → review exactly those.
- `--scope=project` → review every tracked `.v` (requires confirmation).

Project-wide confirmation:

```
This will review every .v file in the project. Proceed? (yes / no)
```

## Scope Behavior

1. **changed** — `git diff --name-only` and `git diff --name-only
   --cached`, filtered to `*.v`. If empty, report "no changed .v files"
   and stop.
2. **explicit targets** — exactly the paths passed (glob-expanded by
   the shell). Skip non-`.v` and unreadable paths with a note.
3. **project** — `git ls-files '*.v'` after the confirmation prompt.

The header of the report always echoes the resolved scope.

## Actions

Run per resolved scope, naming the exact tool for each step.

1. **Resolve scope** — compute the target list (changed via
   `git diff --name-only` | explicit targets | `git ls-files '*.v'`).

2. **Build status** — `mcp__rocq-mcp__rocq_compile_file` on each target
   (`file=<path>`); surface any errors. If the rocq-mcp server is not
   configured/available, emit "build: skipped (rocq-mcp absent)" and
   continue — the rest of the review is static and does not depend on
   it. A broken build is reported but does not abort the review.

3. **Mechanical audit** — run the bundled scanner:
   ```bash
   ${CLAUDE_SKILL_DIR}/scripts/audit-quick.sh <targets>
   ```
   It emits `[§N.X] file:LINE …` lines keyed to `reference.md`. Treat
   every line as a candidate; the §25 (`@`) detector in particular has
   a ~70-80% false-positive rate on HB-heavy code.

4. **Checklist review** — walk the SKILL.md "Reviewer Checklist"
   groups against each file, recording violations:
   - **Structural** — line length (`awk 'length > 80'`), import order
     (HB → mathcomp base → analysis → project), `(**md … *)` header
     coverage, `Set Implicit Arguments.` block, `Local Open Scope`,
     no fully-qualified module names in the body.
   - **Naming** — `mainSymbol_suffixes`, suffix table (§11), no generic
     hypothesis names (`H`, `H'`), `_neq0` vs `_nonempty`.
   - **Proof scripts** — goal-closers start `by`/`exact:`, no `Focus`
     or `{}`, no bullets for 2 subgoals (use 2-space indent +
     `last first`), tactic spacing (`move=>`, `apply:`, `apply/`;
     `rewrite /def`), no numeric occurrence selectors.
   - **Concision** — useless `exact:`/`apply:` args, useless scope
     delimiters, `[the X of T]` over canonical HB instances, stray
     `@`, explicit inferable display args, name-then-consume, lines
     that could be `by [].`/`done.`.
   - **HB and metadata** — `HB.instance Definition _ :=
     MixinName.Build T proof.`, `Arguments` after `End` only when
     verified needed, `Local`/`Let`/`Fact` for auxiliary lemmas,
     operator spacing (§9).

5. **Axiom hygiene** — for the key lemmas in scope (public results,
   anything the user names), run `mcp__rocq-mcp__rocq_assumptions`
   (`name=<lemma> file=<path>`). Flag anything beyond the boolp trio —
   `functional_extensionality_dep`, `propositional_extensionality`,
   `constructive_indefinite_description` — and flag any `Admitted`
   (`Axioms: <lemma> is admitted`). Skip with a note if rocq-mcp is
   absent.

6. **Emit findings** — one line per finding in the format
   `[§N.X] file:LINE — desc — fix`, grouped by § number ascending.
   Merge mechanical (step 3) and checklist (step 4) findings; drop
   duplicates. Then add a "Top 10 worst offenses" list and a
   violation-density estimate (`X violations across N lines`).

For larger jobs (many files), fan out the `mathcomp-style-auditor`
subagent **one per file** — it is read-only, so same-file safety is not
a concern across the fleet; consolidate the returned punch lists into
the single report below.

## Output

Emit exactly this markdown skeleton:

```markdown
## mathcomp Review Report
**Scope:** <changed | project | listed targets>
**Files:** <N> · **Lines:** <total>

### Build Status
<✓ all targets compile | ✗ errors below | skipped (rocq-mcp absent)>

### Axiom Hygiene
<✓ boolp trio only | flags below | skipped (rocq-mcp absent)>
- [Axioms] file:lemma — <extra axiom / Admitted> — <action>

### Findings (by § ascending)
- [§1] file:LINE — line >80 chars — wrap
- [§9] file:LINE — tactic spacing — drop space before `:`
- [§23] file:LINE — fully-qualified module name — Import it
- … (every finding, grouped by § number ascending)

### Top 10 Worst Offenses
1. [§N.X] file:LINE — desc — fix
… (up to 10)

### Violation Density
<X violations across N lines> (~<X/N> per line);
cross-cutting clusters: §23 (imports), §24.1 ([the X of T]).

### Notes
- Findings are CANDIDATES; per-site verify before applying.
- Suggested cleanup order: imports (§23) → [the X of T] (§24.1) →
  Local/Fact (§18) → @-stripping (§25) → 2-bullet (§27.8) →
  concision (§22.1, §27.1, §27.4) → naming (§10, §32.1) → header (§4).
```

## Safety

- **READ-ONLY.** This command never edits, stages, or commits `.v`
  files. It produces a report only.
- **The build is the oracle.** Static findings are plausibilities;
  `mcp__rocq-mcp__rocq_compile_file` (or `make`) decides truth.
- **Findings are CANDIDATES.** Several detectors flag real-looking
  issues that are unsound to "fix". Before acting on any finding,
  cross-reference playbook.md § "Audit recommendations that don't pan
  out" — known false positives include stripping `@` from HB Builder
  calls (`@isFoo.Build R X Y f hf`), inlining `mfun_Sub (mem_set h)`
  chains, moving section-local `Arguments` post-`End`, and inlining
  wrappers that anchor type inference. Per-site verify, then apply, then
  re-build after each change.
- Apply cross-cutting fixes (§23, §24.1) first; they resolve many
  findings at once and are low-risk.

## See Also

- `agents/mathcomp-style-auditor.md` — the per-file worker subagent.
- SKILL.md § "Reviewer Checklist" — the source-of-truth checklist.
- playbook.md § "Multi-agent audit" — prompt template + consolidation.
- playbook.md § "Audit recommendations that don't pan out" — false
  positives to filter before applying any fix.
- reference.md — section numbers referenced by every finding.
