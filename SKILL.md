---
name: mathcomp-skills
description: Use when writing or reviewing .v files that import `From mathcomp` or `From HB` — math-comp, mathcomp-analysis, Rocq style, ssreflect tactics, HB hierarchy builder, HB factory, forgetful inheritance, canonical structures, Arguments directives, lemma naming (mainSymbol_suffixes, abbreviation suffixes), intro patterns, case-analysis idioms (leP, ltgtP, eqVneq, altP), bigop, under eq_bigr, choice/decidability, eqType, choiceType, finType, boolp, classical reasoning, Search discipline, PR review prep against mathcomp/analysis, code cleanup. Also covers the rocq-mcp tools for live proof inspection.
allowed-tools: Bash(grep *), Bash(find *), Bash(awk *), Bash(sed *), Bash(make *), Read, Glob, mcp__rocq-mcp__rocq_start, mcp__rocq-mcp__rocq_compile, mcp__rocq-mcp__rocq_compile_file, mcp__rocq-mcp__rocq_check, mcp__rocq-mcp__rocq_query, mcp__rocq-mcp__rocq_step_multi, mcp__rocq-mcp__rocq_assumptions, mcp__rocq-mcp__rocq_notations, mcp__rocq-mcp__rocq_toc, mcp__rocq-mcp__rocq_verify, mcp__rocq-mcp__rocq_diag
---

# math-comp / mathcomp-analysis Rocq style

This skill bundles a comprehensive style guide and a set of validated
cleanup patterns for math-comp / mathcomp-analysis Rocq code. Use it
when writing new code, reviewing existing code, or preparing a PR
against an upstream mathcomp project.

## Target versions

Citations verified against **Rocq 9.1.1**, **mathcomp 2.5.0**,
**mathcomp-analysis 1.16.0**, **mathcomp-algebra-tactics 1.2.7**,
**HB 1.10.2**. Minimum supported: Rocq 9.0, mathcomp 2.4, analysis
1.13, HB 1.8. See `LAST_VERIFIED.md` for the full per-section table.
If your installed version differs, lemma **names** should still
resolve but `file.v:line` numbers may drift — run
`grep -n "Lemma <name>" <file>` to relocate.

## Files in this skill

- **`reference.md`** — core style guide §1-§37 (~3270 lines). Read
  this for general rules:
  - **§1-§21**: Core conventions (line length, naming, proof style,
    HB instances, deprecation, visibility, analysis-specific naming,
    changelog, common review rejections).
  - **§22-§32**: Concision & idiomatic ssreflect (maintainer feedback,
    case analysis, rewriting, forward-step, Notation vs. Definition).
  - **§33**: PR Citation Index (with `[topic ≠ rule]` caveats).
  - **§34-§37**: Cross-cutting idioms (Bigops, HB Factories,
    Choice/Decidability, Search Discipline).
- **`domains.md`** — thin **dispatcher** that routes a question to
  one of the per-library files under `domains/`. Read first when the
  question is about a specific mathcomp library area.
- **`domains/<N>_<topic>.md`** — one file per library area
  (~330-460 lines each). Read **only** the file matching the
  question — not the whole `domains/` directory:
  - `38_matrix.md` (matrix, `mxE`, `\det`, blocks)
  - `39_polynomial.md` (`{poly R}`, `coefE`, `hornerE`, `derivE`)
  - `40_finset.md` (`{set T}`, `inE`, cardinality)
  - `41_int_rat.md` (`int`, `rat`, modular arithmetic)
  - `42_derive.md` (`is_derive`, `'D[_]`, differentiable)
  - `43_measure.md` (`measurable_fun`, Lebesgue integral)
  - `44_topology.md` (filter, nbhs, cvg, `near`)
  - `45_algebra_tactics.md` (`ring`/`field`/`lra`/`nra`/`zify`)
  - `46_tuple_perm_binomial.md` (`n.-tuple`, `'S_n`, `'C(n,m)`)
  - `47_finfun.md` (`{ffun T -> R}`)
- **`templates.md`** — catalog of canonical proof skeletons keyed by
  the **shape of the goal** (`\forall x \near F, P x`, `measurable_fun
  D f`, `is_derive ...`, `apply/ffunP`, `HB.instance Definition _ :=
  ...`, ring-identity, etc.). Read this when you know the goal shape
  but not how to start. 20 templates, each with strategy + skeleton
  + real-code example.
- **`phrasebook.md`** — natural-language **intent → idiom** index. Read
  when you know *what you want to do in English* (e.g. "introduce and
  rewrite", "decide an order comparison", "rewrite under a bigop") but
  not the ssreflect chord. The intent-first complement to `templates.md`
  (goal-shape-first) and `reference.md` (rule-first); also disambiguates
  ssreflect vs vanilla `rewrite`/`case:`/`apply:`.
- **`proof-development.md`** — the `Admitted`/`admit`-filling loop:
  inspect the goal first, `Search` before guessing, test candidates
  with the non-advancing `rocq_step_multi` battery, commit the winner
  via `rocq_check` + extract `proof_tactics`, then re-verify axiom
  hygiene with `rocq_assumptions`. Read when a proof has an open
  obligation or a stuck subgoal. Guidance, not an auto-prover.
- **`errors.md`** — Rocq/`coqc` **error message → cause → mathcomp
  fix** lookup (infer-placeholder/canonical/HB, unification, rewrite
  `not a subterm`, illegal application, scope/notation, HB
  anomaly/universe). Read when the build prints something and you need
  the concrete ssreflect action. Seeded from §35.10.

**When to consult which file**:
| Question type | File |
|---------------|------|
| "How do I name this lemma?" | `reference.md` (§10, §37) |
| "What's the right `apply` form?" | `reference.md` (§22-§29) |
| "How do I declare an HB instance?" | `reference.md` (§15, §35) |
| **"How do I start a proof of `<goal shape>`?"** | **`templates.md`** |
| **"How do I *say* `<intent in English>` in ssreflect?"** | **`phrasebook.md`** |
| **"How do I fill an `Admitted.` / unstick a subgoal?"** | **`proof-development.md`** |
| **"`coqc` printed an error — what's the fix?"** | **`errors.md`** |
| "How do I open a `\matrix_(i,j)` term?" | `domains/38_matrix.md` |
| "How do I prove `\det` of a permutation matrix?" | `domains/38_matrix.md` + `domains/46_tuple_perm_binomial.md` |
| "How do I prove `measurable_fun setT _`?" | `templates.md` §3 + `domains/43_measure.md` |
| "What's the canonical form for an integral rewrite?" | `templates.md` §5 + `domains/43_measure.md` |
| "How does `is_derive` typeclass resolution work?" | `templates.md` §4 + `domains/42_derive.md` |
| "Should I use `ring` / `field` / `lra` / `lia`?" | `domains/45_algebra_tactics.md` |
| "How do I prove tuple equality / permutation parity?" | `templates.md` §6/§14 + `domains/46_tuple_perm_binomial.md` |
| "How do I open `[ffun x => ...]`?" | `domains/47_finfun.md` |
| "How do I prove `\forall x \near F, P x`?" | `templates.md` §1 |
- **`playbook.md`** — concrete cleanup patterns that have been validated
  to work (and the audit recommendations that turn out unsound). Use
  when fixing a codebase against the guide.
- **`LAST_VERIFIED.md`** — date stamps for the cite-heavy sections,
  recording which Rocq/mathcomp version each was verified against.
  When a `file:line` citation seems stale, this tells you how old
  the verification is and what to grep for.
- **`scripts/audit-quick.sh`** — mechanical single-file audit catching
  high-yield style violations (line length, fully-qualified module
  names, scope delimiters, useless `have ->`, `[the X of T]`, `@` on
  user lemmas, name-then-consume patterns, 2-subgoal bullets, `_is_`
  on equational lemmas, tactic spacing). Run with:
  `${CLAUDE_SKILL_DIR}/scripts/audit-quick.sh theories/*.v`

## How to use this skill

1. **For new code**: skim the Quick Reference below; consult
   `reference.md` § for any specific rule the user asks about.
2. **For review / cleanup**: launch the audit workflow described in
   `playbook.md` § "Multi-agent audit", then apply the validated
   cross-cutting fixes (also in `playbook.md`).
3. **For live proof debugging**: invoke the rocq-mcp tools
   (`mcp__rocq-mcp__rocq_check`, `mcp__rocq-mcp__rocq_compile_file`,
   `mcp__rocq-mcp__rocq_query`, `mcp__rocq-mcp__rocq_step_multi`,
   `mcp__rocq-mcp__rocq_assumptions`, etc.) — see "rocq-mcp integration"
   below.

## Quick Reference: Top 25 Rules

| # | Rule | reference.md § |
|---|------|----------------|
|  1 | Lines must be <= 80 chars | 1 |
|  2 | `From HB Require Import structures.` is the very first line | 3 |
|  3 | Always `Local Open Scope`, never plain `Open Scope` | 6 |
|  4 | Goal-closing tactic lines must start with `by` (or be `exact:`) | 26 |
|  5 | Use bullets `-` `+` `*` and 2-space indent for branches | 8, 27.8 |
|  6 | No `Focus`, no `{` `}` -- use indentation and bullets | 8 |
|  7 | Lemma names: `mainSymbol_suffixes`, head symbol first | 10 |
|  8 | Hypothesis names must be meaningful (never `H`, `H'`) | 14 |
|  9 | `move=>` / `apply:` / `apply/` -- no space before the operator | 9 |
| 10 | `rewrite /def` -- space before unfold | 9 |
| 11 | Drop useless arguments to `exact:` / `apply:` | 22.2 |
| 12 | Drop useless scope delimiters (`%R`, `%E`) inside an open scope | 22.3 |
| 13 | Drop useless type constraints like `[the measurableType _ of T]` | 24.1 |
| 14 | Drop the explicit display (`measure_display`) when inferable | 24.4 |
| 15 | Drop `@` unless disambiguating | 25 |
| 16 | Replace `move=> H; rewrite H` with `move=> ->` | 27.1 |
| 17 | Replace `move=> halpha U hU; exact: hU` with `move=> halpha U; exact` | 27.4 |
| 18 | Replace useless lines with `by [].` | 22.1 |
| 19 | No fully-qualified `order.Order.X`, `boolp.X`, `filter.X` -- import | 23 |
| 20 | Auxiliary results: `Local`, `Let`, or `Fact`; main results: bare | 18 |
| 21 | `Arguments` re-declared after `End` when needed (and confirmed needed) | 16 |
| 22 | Document new definitions in the `(**md ... *)` header block | 4 |
| 23 | Add a `CHANGELOG_UNRELEASED.md` entry for every public API change | 20 |
| 24 | Generalize aggressively -- `topologicalType` over `R : realType` etc. | 21 |
| 25 | `HB.instance Definition _ := MixinName.Build T proof.` pattern | 15 |

## Reviewer Checklist (run before sending a PR)

**Structural**
- [ ] All lines <= 80 chars (`awk 'length > 80' file.v`)
- [ ] Imports follow the canonical order (HB → mathcomp base → analysis → project)
- [ ] `(**md ... *)` header documents every public definition
- [ ] `Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.`
- [ ] All `Open Scope` are `Local Open Scope`
- [ ] No fully-qualified module names in source body (`order.Order.X`, `boolp.X`, `filter.X`)

**Naming**
- [ ] Lemma names follow `mainSymbol_suffixes`
- [ ] Suffixes match the standard table (reference.md § 11)
- [ ] No generic hypothesis names (`H`, `H'`); use `_` for unused
- [ ] `_neq0` vs `_nonempty` chosen by exact statement form

**Proof scripts**
- [ ] Goal-closing lines start with `by` or `exact:`
- [ ] No `Focus` or `{}` braces
- [ ] No bullets when only 2 subgoals (use 2-space indent + `last first`)
- [ ] Tactic spacing: `move=>`, `apply:`, `apply/` (no space); `rewrite /def` (space)
- [ ] No numerical occurrence selectors

**Concision (high-yield reviewer flags)**
- [ ] No useless args to `exact:` / `apply:` (try without)
- [ ] No useless scope delimiters inside an open scope
- [ ] No `[the X of T]` over already-canonical HB instances
- [ ] No `@` unless disambiguating
- [ ] No display arg (`measure_display`) passed explicitly when inferable
- [ ] No hypothesis named just to be consumed once -- use `->`, `<-`, `?`, `_`
- [ ] No bookkeeping line that could be `by [].` or `done.`
- [ ] No `have -> : E by [].` followed by `by [].` (rewrite was redundant)

**HB and metadata**
- [ ] HB instance pattern: `HB.instance Definition _ := MixinName.Build T proof.`
- [ ] `Arguments` after `End` only when verified that inside-section
      declarations don't already do the right thing (see playbook.md
      §"Moving section-local `Arguments` declarations post-`End`")
- [ ] Auxiliary lemmas use `Local`/`Let`/`Fact`; main results bare
- [ ] Operators have spaces: `n * m`, not `n*m` (§9)

## rocq-mcp integration (live proof inspection)

The [rocq-mcp](https://github.com/LLM4Rocq/rocq-mcp) MCP server
exposes Rocq's interactive engine as tools. When working on a proof,
prefer these to running `coqc`/`make` repeatedly.

### Setup (one-time)

Install rocq-mcp in your environment (Python 3.11+, `coqc` on PATH).
The standard flow is:

```sh
git clone https://github.com/LLM4Rocq/rocq-mcp
cd rocq-mcp
uv pip install -e .
# Optional, for the interactive tools (rocq_check, rocq_step_multi):
# install pet via coq-lsp
```

Register the server in `~/.claude.json` or your project `.mcp.json`:

```json
{
  "mcpServers": {
    "rocq-mcp": {
      "command": "rocq-mcp",
      "env": { "ROCQ_WORKSPACE": "/path/to/your/rocq/project" }
    }
  }
}
```

After restart, the tools below become available as deferred MCP
tools.

### Tool table

All 11 tools (short name; prefix `mcp__rocq-mcp__`). The `Req`
column lists the **required** params:

| Tool | Use when | Req |
|------|----------|-----|
| `rocq_start` | Open a held session; returns `state_id`+goals | (see below) |
| `rocq_compile` | coqc a finished source *string* | `source` |
| `rocq_compile_file` | coqc a `.v` file on disk; surface errors | `file` |
| `rocq_check` | Commit commands; advances `state_id` | `body`, `from_state` |
| `rocq_query` | `Search`/`About`/`Print`/`Check`/`Locate` | `command` |
| `rocq_step_multi` | Try tactics on ONE state; no advance | `tactics`, `from_state` |
| `rocq_assumptions` | `Print Assumptions` for a name | `name`, `file` |
| `rocq_notations` | How notations in a statement resolve | `statement` |
| `rocq_toc` | Outline (defs/lemmas/sections) of a file | `file` |
| `rocq_verify` | Sandbox-verify a finished proof | `proof`+`problem_*` |
| `rocq_diag` | pet/session health, memory, recent errors | (none) |

`rocq_start` needs **one** start mode: `theorem`+`file`,
`file`+`line`+`character` (position), or `preamble` (imports only).
`rocq_query` also accepts optional `from_state` / `file` / `preamble`
for context. `tactics` is capped at 20 entries.

`from_state` is **required** (no implicit "current state") for both
`rocq_check` and `rocq_step_multi` — always thread the `state_id`
returned by `rocq_start` / a prior `rocq_check` / a state-capture on a
failed `rocq_compile_file`. Call `rocq_diag` after any response that
carries `pet_restarted: True`.

### Warm-import iteration (preamble mode)

For scratch iteration, do **not** repeatedly `coqc /tmp/foo.v` — every
coqc call reloads all imports (seconds on `all_ssreflect` / analysis).
Instead warm the imports once:

```
rocq_start preamble="From mathcomp Require Import all_ssreflect ssralg."
```

The import set is content-hashed, so the returned `state_id` stays
warm across iterations even when you change the lemma body. Then drive
the proof with `rocq_check` / `rocq_step_multi` against that `state_id`.

Tip: if you do anchor on a real file (theorem/position mode) under
`/tmp`, keep the file **name** stable across edits (e.g. `/tmp/probe.v`)
— Fleche caches per file path, so rotating probe names defeats the
warmth.

Position mode (`file`+`line`+`character`) is 0-indexed and rounds
*forward* to a sentence boundary: a cursor anywhere in a sentence
(including its period) yields the state **after** it; a cursor in the
whitespace before a sentence's first character yields the state
**before** it. To inspect goals before a tactic, point at the
whitespace just before its first character.

### Canonical loop (goal-state-first)

Inspect the goal state **before** editing a tactic. The loop:

1. **Inspect**: `rocq_start` (theorem/position/preamble) → read the
   returned goals. Capture the `state_id`.
2. **Search**: `rocq_query command="Search ..." from_state=<state_id>`
   to find a lemma. With `from_state`, `Search`/`Print`/`About`/
   `Locate` see the **live** hypotheses and open scopes mid-proof. Keep
   queries focused (cross-ref reference.md §37 search discipline).
3. **Try the battery**: `rocq_step_multi from_state=<state_id>
   tactics=[...]` to find a winning tactic *without advancing state*.
   Each result entry carries `success`, `goals`, `proof_finished`.
   Cap at 20 tactics, keyed to goal shape (see battery below).
4. **Commit**: re-run the winner via `rocq_check from_state=<state_id>
   body="<tactic>."` — this advances to a **new** `state_id`. Repeat
   from step 2 on the new state.
5. **Extract**: when a `rocq_check` returns `proof_finished: True`, it
   also returns `proof_tactics` (ordered root→current tactic list) and
   `proof_hint` (how to assemble the `.v`). Paste `proof_tactics` into
   the file. If the chain is broken (an ancestor `state_id` was
   evicted), the response omits these and carries
   `proof_tactics_status` instead — restart and re-walk.
6. **Re-verify**: after the file compiles, `rocq_assumptions
   name=<lemma> file=<path>` to confirm no stray axioms (cross-ref
   reference.md §36 — the boolp `funext`/`propext`/`cid` trio (the
   axioms `Print Assumptions` actually reports) is expected in
   analysis proofs; anything else is a red flag). Use
   `rocq_verify` for a sandboxed admit-free check of a candidate.

### `rocq_step_multi` battery (try-the-battery pattern)

`rocq_step_multi` runs a caller-supplied battery of tactics and reports
which close (or progress) the goal *without committing any*. Pick a
subset keyed to the goal shape; lia/lra/ring/field need the matching
`Require Import` warmed into the session first:

```
# general close-out
tactics=["by [].", "done.", "exact: H.", "reflexivity.",
         "assumption.", "trivial."]
# arithmetic over int/nat/rat (zify first to normalise, then)
tactics=["lia.", "nia."]      # cross-ref domains/45_algebra_tactics.md
# ring / field identities
tactics=["ring.", "field.", "nra.", "lra."]
# structure exploration
tactics=["case: n.", "elim: n.", "move=> *."]
```

Keep the list <= 20 entries. After a winner is found, **commit it with
`rocq_check`** — `rocq_step_multi` never advances the session state.

### Example tool calls

Look up a lemma (`Search`/`About`/`Print`/`Check` go through
`command`); add `from_state` to query the live proof context:
```
rocq_query command="Search le_trans"
rocq_query command="Search _ (_ + _)." from_state=42
```

Compile a file and see errors (on an in-proof error with coq-lsp
available, the response carries a reusable `state_id` + goals at the
error position, plus a structured `errors` list):
```
rocq_compile_file file="theories/my_proof.v"
```

Try tactics against a live state, then commit the winner:
```
rocq_step_multi from_state=42 \
  tactics=["rewrite /foo.", "apply: lem1.", "exact: hX."]
rocq_check from_state=42 body="exact: hX."
```

Verify a finished proof in a sandbox. `problem_statement` must be
the **complete file content** of the original problem (with
`Admitted`/`Abort`); `proof` must be the **complete file content**
of the candidate, including imports. `problem_name` is the lemma
identifier:
```
rocq_verify problem_name="foo" \
            problem_statement="From mathcomp Require Import all_ssreflect.\nLemma foo : 1 + 1 = 2.\nProof. Admitted." \
            proof="From mathcomp Require Import all_ssreflect.\nLemma foo : 1 + 1 = 2.\nProof. by []. Qed."
```

### Fallback

If rocq-mcp is not configured, fall back to the project's `make`
target and `Search` queries inside an editor / IDE. The skill is
still useful without the MCP integration — the style guide and
playbook don't depend on it.

## Multi-agent audit workflow

When the user wants a thorough style audit of a mathcomp Rocq
codebase, launch parallel audit agents — one per file or one per
file-group — each instructed to produce a structured punch list
keyed to `reference.md` section numbers. See `playbook.md`
§ "Multi-agent audit" for the prompt template and consolidation
steps.

## When the audit recommends something risky

Some style "improvements" turn out unsound when applied. Common
false positives are documented in `playbook.md` § "Audit
recommendations that don't pan out":
- Stripping `@` from HB Builder calls (`@isFoo.Build R X Y f hf`)
- Inlining `mfun_Sub (mem_set h)` chains
- Moving section-local `Arguments` declarations post-`End`
- Inlining wrappers that anchor type inference

Always test per-site when applying these. If the build breaks,
revert and skip — the audit is an LLM-generated checklist, not
ground truth.

## Commands & agents (bundled plugin)

This skill ships as a Claude Code plugin (`.claude-plugin/plugin.json`):

- `/mathcomp-review [file.v ...] | --scope=changed|project` —
  read-only style review: build status (`rocq_compile_file`), the
  mechanical scanner, this Reviewer Checklist, and axiom hygiene
  (`rocq_assumptions`), emitting `[§N.X] file:LINE — desc — fix`
  findings. Never edits .v files.
- `mathcomp-style-auditor` subagent — read-only per-file auditor
  (no Edit/Write). The command fans it out one-per-file; same-file
  parallel dispatch is safe because no auditor ever writes.

## Citation freshness

`scripts/check-citations.sh` validates every `file.v:line` citation in
`reference.md` / `domains/*.md` against an installed mathcomp tree
(name-missing → error, line-drift → warn + suggested fix; degrades
gracefully to a no-op when mathcomp is absent). A weekly CI job
(`.github/workflows/citations.yml`) runs it against the pinned stack;
`markdown-lint.yml` self-lints the guide's own code fences on every PR.

Other CLI helpers under `scripts/` (all degrade gracefully when
rocq/coq is absent):
- `search-mathcomp.sh` — run §37 `Search`/`About`/`Print HB` queries
  from the shell (or print the query to paste into `rocq_query`).
- `print-assumptions-check.sh --all <file.v>` — axiom hygiene without
  rocq-mcp; flags any axiom beyond the boolp trio and exits non-zero.
- `parse-coqc-errors.py` — pipe `coqc` output through it for
  structured (JSON) error triage, classified the same way as
  `errors.md`.

A bundled `PostToolUse` hook (`hooks/hooks.json`) runs `audit-quick.sh`
on each edited `.v` file and surfaces findings as advisory context —
read-only, never blocking.

## What this skill is NOT

- Not a tutorial on math-comp itself (see the
  [mathcomp book](https://math-comp.github.io/mcb/))
- Not a substitute for the official `CONTRIBUTING.md` files
