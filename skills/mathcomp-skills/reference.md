# MathComp & MathComp-Analysis Coding Guidelines

> Compiled from the official CONTRIBUTING.md files of
> [math-comp/math-comp](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md)
> and [math-comp/analysis](https://github.com/math-comp/analysis/blob/master/CONTRIBUTING.md),
> the [MathComp documentation wiki](https://github.com/math-comp/math-comp/wiki/How-to-document),
> PR review patterns from both repositories, and community discussions on
> [Zulip](https://rocq-prover.zulipchat.com/).

This document is intended to be given to a reviewer agent to enforce
mathcomp/mathcomp-analysis conventions on Rocq formalization code.

---

## Table of Contents

1. [Line Length and Formatting](#1-line-length-and-formatting)
2. [File Structure](#2-file-structure)
3. [Import Organization](#3-import-organization)
4. [File Header Documentation](#4-file-header-documentation)
5. [Post-Header Setup](#5-post-header-setup)
6. [Scope Declarations](#6-scope-declarations)
7. [Section Organization](#7-section-organization)
8. [Proof Style](#8-proof-style)
9. [Tactic Spacing](#9-tactic-spacing)
10. [Lemma Naming Conventions](#10-lemma-naming-conventions)
11. [Complete Abbreviation Table](#11-complete-abbreviation-table)
12. [Special Naming Conventions](#12-special-naming-conventions)
13. [Definition Naming Conventions](#13-definition-naming-conventions)
14. [Variable and Hypothesis Naming](#14-variable-and-hypothesis-naming)
15. [HB Instance Patterns](#15-hb-instance-patterns)
16. [Arguments and Implicit Types](#16-arguments-and-implicit-types)
17. [Deprecation Protocol](#17-deprecation-protocol)
18. [Local vs Global Visibility](#18-local-vs-global-visibility)
19. [Analysis-Specific Conventions](#19-analysis-specific-conventions)
20. [Changelog Conventions](#20-changelog-conventions)
21. [Common Review Rejections](#21-common-review-rejections)

**Concision and idiomatic style (sections distilled from
mathcomp-analysis maintainer reviews):**

22. [Concision and Triviality (Maintainer Feedback)](#22-concision-and-triviality-maintainer-feedback)
23. [Avoiding Fully-Qualified Identifiers](#23-avoiding-fully-qualified-identifiers)
24. [Type Constraint Hygiene](#24-type-constraint-hygiene)
25. [The `@` Discipline](#25-the--discipline)
26. [Closing Tactics and Terminators](#26-closing-tactics-and-terminators)
27. [Book-Keeping Idioms in Proof Scripts](#27-book-keeping-idioms-in-proof-scripts)

**Idiomatic ssreflect tactics (mined from upstream PR reviews):**

28. [Idiomatic Case Analysis](#28-idiomatic-case-analysis)
29. [Rewriting Idioms](#29-rewriting-idioms)
30. [Forward-Step and Symmetry Idioms](#30-forward-step-and-symmetry-idioms)
31. [Maximal Implicits and `Arguments` Discipline](#31-maximal-implicits-and-arguments-discipline)
32. [Notation vs. Definition](#32-notation-vs-definition)
33. [PR Citation Index](#33-pr-citation-index)
34. [Bigop Idioms](#34-bigop-idioms)
35. [HB Factories and Multi-Step Inheritance](#35-hb-factories-and-multi-step-inheritance)
36. [Choice and Decidability](#36-choice-and-decidability)
37. [Search Discipline](#37-search-discipline)

**Domain-specific idioms (mathcomp library areas) — see `domains/<N>_*.md`:**

38. Matrix Idioms — *in `domains/38_matrix.md`*
39. Polynomial Idioms — *in `domains/39_polynomial.md`*
40. Finset Idioms — *in `domains/40_finset.md`*
41. Integer, Rational, and Modular Idioms — *in `domains/41_int_rat.md`*
42. Derivative and `is_derive` Idioms — *in `domains/42_derive.md`*
43. Measure and Lebesgue Integral Idioms — *in `domains/43_measure.md`*
44. Topology and Filter Idioms — *in `domains/44_topology.md`*
45. Algebra Tactics — *in `domains/45_algebra_tactics.md`*
46. Tuple, Permutation, and Binomial Idioms — *in `domains/46_tuple_perm_binomial.md`*
47. Finite Functions (`{ffun T -> R}`) Idioms — *in `domains/47_finfun.md`*

---

## 0. Quick Reference: Top 25 Rules

A condensed cheat sheet of the rules most likely to surface in
mathcomp-analysis review. Each item links to the full rule below.

| # | Rule | Section |
|---|------|---------|
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
| 21 | `Arguments` re-declared after `End` when needed | 16 |
| 22 | Document new definitions in the `(**md ... *)` header block | 4 |
| 23 | Add a `CHANGELOG_UNRELEASED.md` entry for every public API change | 20 |
| 24 | Generalize aggressively -- `topologicalType` over `R : realType` etc. | 21 |
| 25 | `HB.instance Definition _ := MixinName.Build T proof.` pattern | 15 |

---

## 1. Line Length and Formatting

**Hard rule: A line should have no more than 80 characters.**

This is the single most frequently enforced rule in PR reviews (enforced
by upstream reviewers). If a line is longer than
80 characters:

1. Cut it **semantically** (at a natural break point).
2. If no semantic cut is possible, cut over several lines for
   readability.
3. Consider using `Implicit Types` to shorten repeated type
   annotations (PR #1825).

Additional formatting rules:
- No tabs -- spaces only.
- 2-space indentation for most constructs.
- 4-space indentation for continuation lines (parameters that overflow
  from a definition/lemma statement).
- All comment boxes are exactly 80 characters wide.

---

## 2. File Structure

Every file follows this order:

```
1. Copyright/license line
2. Imports (From HB, From mathcomp, From project)
3. (**md ... *) documentation header block
4. Post-header setup (Set/Unset, Import, Local Open Scope)
5. Reserved Notation (if any)
6. Sections containing definitions, lemmas, proofs
7. Arguments declarations (after End of sections if needed)
8. Notation/coercion exports
```

---

## 3. Import Organization

Imports follow a strict ordering:

```coq
(* 1. HB always first *)
From HB Require Import structures.

(* 2. MathComp base libraries *)
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint.

(* 3. MathComp analysis libraries, in dependency order *)
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.

(* 4. Project-local imports *)
From MyProject Require Import my_module other_module.
```

Rules:
- **`From HB Require Import structures.`** is always the very first
  import line.
- Group related modules on the same line with spaces.
- Approximately 4-7 import lines total.
- Use `From mathcomp Require Import` (never path-qualified like
  `mathcomp.classical`). Reviewers consistently reject this: "Please
  use the namespace `mathcomp` rather than the too specific
  `mathcomp.classical`."
- Consolidate where possible: `all_algebra` subsumes multiple
  packages; prefer `all_ssreflect` when appropriate.
- Suppress warnings when needed:
  `#[warning="-warn-library-file-internal-analysis"]`

---

## 4. File Header Documentation

Every file must have a markdown documentation block immediately after
imports. The format is:

```coq
(**md**************************************************************************)
(* # File Title                                                               *)
(*                                                                            *)
(* Description paragraph explaining the file's purpose.                       *)
(*                                                                            *)
(* Reference: bibliographic entry if applicable                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   definition == prose explanation of the definition                         *)
(*     notation == prose explanation, scope info nearby                        *)
(*   structType == name, with "The HB class is Xyz."                          *)
(*     shortcut := pseudo-code explanation                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)
```

Rules:
- The opening line is `(**md` followed by `*` characters to fill 80
  columns.
- The closing line is `(***...***)` also exactly 80 columns.
- All content lines are `(*` padded with spaces to 78 chars then `*)`.
- Main heading: `# Title`. Sub-headings: `## Sub-heading`.
- Notation/definition tables are wrapped in triple-backtick code
  blocks.
- Each entry uses `==` to separate notation from description, or `:=`
  for code-style explanations.
- Entries are right-aligned at the `==` delimiter with consistent
  column alignment.
- **Every new definition must be documented in the header**
  (PR #821).
- **Lemmas are NOT documented by default** -- to encourage users to
  read the full documentation. Exception: particularly important
  theorems.
- Only sentences end with a period; definition explanations do not.

Section markers within the file:
```coq
(** * Level 1 section name *)
(** ** Level 2 section name *)
```

Notes and todos:
- Use `TODO:` with date and author. Prefer GitHub issues.
- Use `NB:` with date and author for important notes.

---

## 5. Post-Header Setup

Immediately after the documentation block, every file has:

```coq
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
```

Variations:
- Some files add `Import numFieldTopology.Exports.` or
  `numFieldNormedType.Exports.`
- Analysis files may add: `Unset SsrOldRewriteGoalsOrder.`
  (with comment: "remove the line when requiring MathComp >= 2.6")
- The four `Set/Unset` lines are always present in that exact order.

---

## 6. Scope Declarations

**Always use `Local Open Scope`** -- never open scopes globally.

```coq
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
```

Scopes may also be opened locally within sections when only needed
there.

### 6.1 `Bind Scope` propagation

When defining a new structure type, declare its `Bind Scope` so the
right scope opens automatically when arguments of that type appear.
The rule of thumb (math-comp PR #1046) is:

> A structure should inherit the `Bind Scope` declaration from its
> carrier.

Once `Bind Scope ring_scope with someRingType` is declared, callsite
expressions of `someRingType` automatically use `ring_scope` -- so
explicit `%R` delimiters become unnecessary downstream.

### 6.2 Scope ordering inside a file

Be consistent: when a notation is introduced in two scopes (e.g.,
`ereal_scope` and `ereal_dual_scope`), use the same ordering across
the file. Reviewers (analysis PR #514) flag inversions of
the established order.

### 6.3 Notation precedence

Tweak `Bind Scope` and notation precedences with care: small changes
can break parse trees in distant files (analysis PR
#514). Always run the full test suite after a notation/scope change.

---

## 7. Section Organization

```coq
Section section_name.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

Local Notation "'N_ p [ f ]" := (Lnorm mu p f).

(* definitions and lemmas *)

End section_name.
```

Rules:
- `Context` is the modern form for declaring section variables. Its
  binders carry explicitness markers (`(x : T)` explicit,
  `{x : T}` implicit, `[x : T]` non-maximally-inserted implicit),
  and **those markers are preserved at section discharge** — so
  every lemma proved in the section inherits the same binder shape
  for `x`. This is why mathcomp-analysis writes
  `Context d {T : measurableType d} {R : realType}.` — `d` stays
  explicit, `T` and `R` are inferred from the measurable/real
  structure.
- `Variable` (singular) and `Variables` (plural) are the historical
  forms; they always discharge as **explicit** arguments. They
  remain extremely common in mathcomp source for backward
  compatibility, and are still appropriate when you want explicit
  arguments and do not need to mix binder shapes in one declaration.
- `Hypothesis` / `Hypotheses` are conventionally used for
  `Prop`-typed assumptions; semantically equivalent to
  `Variable` / `Variables`.
- Note: mathcomp has **very few typeclasses** (it relies on canonical
  structures and HB instead), so `Context` here is *not* about
  typeclass resolution — it is about preserving binder explicitness.
- `Implicit Types` inside sections for conventional type bindings.
- `Local Notation` for section-local shorthands.
- `Local Open Scope` within sections when the scope is only needed
  there.

---

## 8. Proof Style

### General Guidelines

- **Structure proofs in blocks** (forward steps) to limit the scope
  of errors. See "An introduction to small scale reflection in Coq"
  (the SSReflect tutorial), p.103.
- Lines end with a period `.` and only have `;` inside them.
- **Lines that close a goal must start with a terminator** (`by` or
  `exact`). Use an editor that highlights these in red.
- Do not chain too many optional rewrites. Idiom:
  `rewrite conditional_rule ?simplify_side_condition // next_rule.`
- **Do not use `Focus` or `{}`** -- use indentation and terminators.
- Avoid numerical occurrence selectors (`{1 3}`, `{-2}`) -- use
  context patterns, `set`, or `rewrite /` instead
  (Issue #436).

### Indentation in Proof Scripts

Two subgoals:
```coq
tactic.
  tactic. (* first subgoal, indented 2 spaces *)
tactic.   (* second subgoal, not indented *)
```
Use `last first` to bring the smallest/less meaningful goal first
and keep the main flow unindented.

Three or more subgoals -- use bullets:
```coq
tactic.
- tactic.
  + tactic.
    * tactic.
    * tactic.
  + tactic.
- tactic.
- tactic.
```

If one goal is the main flow, remove its bullet and unindent:
```coq
tactic.
- tactic. (* secondary subgoal 1 *)
- tactic. (* secondary subgoal 2 *)
tactic. (* main flow, unindented *)
```

Bullet hierarchy: `-` (level 1), `+` (level 2), `*` (level 3).

### Proof Forms

- One-line proofs: `Proof. by rewrite foo bar. Qed.`
- Multi-line proofs: `Proof.` on its own line, `Qed.` on its own
  line.
- Heavy use of SSReflect tactic chains with `//`, `/=`, `=>`.
- `exact:` preferred over `apply:` when the term directly solves the
  goal.

---

## 9. Tactic Spacing

**No space** between tactic keyword and operator:
```coq
move=> x.       (* correct *)
move => x.      (* WRONG *)
move: x.        (* correct *)
apply/andP.     (* correct *)
apply: lemma.   (* correct *)
```

**Space** between `rewrite` and an unfold:
```coq
rewrite /definition.   (* correct *)
rewrite/definition.    (* WRONG *)
```

**Operators surrounded by spaces** in terms:
```coq
n * m       (* correct *)
n*m         (* WRONG *)
```

---

## 10. Lemma Naming Conventions

### Name Structure

Names follow one of these patterns:

```
(condition_)?mainSymbol_suffixes
mainSymbol_suffixes(_condition)?
naryPredicate_mainSymbol+
mainSymbol_unaryPredicate
```

Where:
- **mainSymbol** is the most meaningful part -- generally the head
  symbol of the RHS of an equation or the head symbol of a theorem.
  It is usually either a main symbol of the theory (`opp`, `add`,
  `mul`, etc.) or a canonical operation (`linear`, `raddf`, `rmorph`,
  `rpred`, etc.).
- **condition** is used when the lemma applies under a hypothesis.
- **suffixes** refine the shape and other symbols. Can be a symbol
  name (`add`, `mul`), a short predicate name (`inj`, `id`), or an
  abbreviation from the table below.

### Underscore Rule

There is an underscore before **suffixes** when they start with a
one-letter lowercase identifier or a lowercase semantic word
(`eq0`, `gt0`, `ge0`, `neq0`). No underscore before capital-letter
chains (`AC`, `CA`, `LR`), digits, or unary suffix capitals.
Exceptions exist for short names (e.g., `lern1`).

Examples:
- `addr_eq0` -- underscore before `eq0` (lowercase semantic word)
- `addr_ge0` -- underscore before `ge0`
- `addrA`, `addrAC`, `addrCA` -- no underscore before capital chains
- `addr0` -- no underscore before `0` (digit)
- `mulNr` -- no underscore before `N` (capital)

### Head Symbol Goes First

The main symbol appears first in the name. For an equational lemma
`LHS = RHS`, reviewer practice is **"head of the LHS"**, not the
literal "head of the RHS" wording in math-comp's CONTRIBUTING.md.
See §37.2 for the discrepancy and PR #1000's worked example
(`powR_Lnorm` was preferred over `Lnorm_powR_K` because the LHS
head is `powR`).

### Unary Predicate Convention

For lemmas about a unary predicate applied to a main symbol:
`mainSymbol_unaryPredicate` (not `unaryPredicate_mainSymbol`).
Example: `g_monotone_monotone` not `monotone_g_monotone`.

### Avoid Overly Generic Names

Names should be specific enough to be discoverable. Reviewers
(PR #1624) reject this: `conjugate` is "too generic" -- should be
`hoelder_conjugate` with local notation.

---

## 11. Complete Abbreviation Table

### Boolean/Logical Abbreviations

| Suffix | Meaning | Example |
|--------|---------|---------|
| `A` | Associativity | `andbA : associative andb` |
| `AC` | Right commutativity | |
| `ACA` | Self-interchange | `orbACA` |
| `b` | Boolean argument | `andbb : idempotent andb` |
| `C` | Commutativity | `andbC : commutative andb` |
| `C` | (alt.) Complement | `predC` |
| `C` | (alt.) Constant | |
| `CA` | Left commutativity | |
| `D` | Predicate/set difference | `predD` |
| `E` | Elimination/equation | `negbFE : ~~ b = false -> b` |
| `F`/`f` | Boolean false | `andbF : b && false = false` |
| `F` | (alt.) Finite type | |
| `I` | Injectivity | `addbI : right_injective addb` |
| `I` | (alt.) Intersection | `predI` |
| `K` | Cancellation | `esymK` |
| `N`/`n` | Boolean negation | `andbN` |
| `P` | Characteristic property / reflect | `andP : reflect (a /\ b) (a && b)` |
| `T`/`t` | Boolean truth | `andbT : right_id true andb` |
| `T` | (alt.) Total set | |
| `U` | Union | `predU` |
| `W` | Weakening | `in1W` |

### Arithmetic Abbreviations

| Suffix | Meaning | Example |
|--------|---------|---------|
| `0` | Zero / empty set | `addr0 : x + 0 = x` |
| `1` | One / identity | `mulr1 : x * 1 = x` |
| `D` | Addition | `linearD : f (u + v) = f u + f v` |
| `B` | Subtraction | `opprB : - (x - y) = y - x` |
| `M` | Multiplication | `invfM : (x * y)^-1 = x^-1 * y^-1` |
| `Mn` | Ring-nat multiplication | `raddfMn` |
| `N` | Ring negation | `mulNr : (- x) * y = - (x * y)` |
| `V` | Multiplicative inverse | `mulVr : x^-1 * x = 1` |
| `X` | Exponentiation | `rmorphXn : f (x ^+ n) = f x ^+ n` |
| `Xn` | Nat exponentiation | |
| `Xz` | Int exponentiation | |
| `Z` | Module scaling | `linearZ : f (a *: v) = s *: f v` |
| `S` | Successor (nat) | `addSn : n.+1 + m = (n + m).+1` |

### Position/Side Abbreviations

| Suffix | Meaning | Example |
|--------|---------|---------|
| `l` | Left of operation | `andb_orl`, `ltr_norml` |
| `r` | Right of operation | `orb_andr`, `ler_normr` |
| `L` | Left of relation | `ltn_subrL` |
| `R` | Right of relation | `ltn_subrR` |
| `LR` | Move op from left to right | `leq_subLR` |
| `RL` | Move op from right to left | `ltn_subRL` |

### Argument Type Abbreviations

| Suffix | Meaning | Example |
|--------|---------|---------|
| `g` | Group argument | |
| `n` | Natural number argument | |
| `r` | Ring argument | |
| `z` | Int argument | |

### Numeric Condition Prefixes (from ssrnum)

| Prefix | Meaning | Example |
|--------|---------|---------|
| `p` | Positive (> 0) | `ltr_pM2l` |
| `n` | Negative (< 0) | |
| `w` | Weak (non-strict) monotony | `ler_wpM2r` |
| `wp` | Non-negative | |
| `wn` | Non-positive | |

---

## 12. Special Naming Conventions

### Membership (`\in`) predicates

- Prefix `in_`: lemmas that unfold specific predicates, propagating
  `\in`. Part of `inE` multirule. Examples: `in_cons`, `in_set0`.
- Prefix `mem_`: other membership lemmas. Examples: `mem_head`,
  `mem_map`.

### Morphism prefixes in algebra

- `raddf_` -- additive function properties (`raddfD`)
- `rmorph_` -- ring morphism properties (`rmorphM`)
- `linear` -- linear map properties (`linearD`, `linearZ`)
- `rpred` -- predicate closedness (`rpredD`, `rpredM`)

### `{homo ...}` and `{mono ...}` lemmas

Statements should NOT be named after `homo` or `mono`. Use the head
of the unfolded statement (for `homo`) or the head of the LHS of the
equality (for `mono`):
```coq
Lemma le_contract : {mono contract : x y / (x <= y)%O}.
(* NOT: mono_contract *)
```

Priority rules:
- When `{mono ...}` subsumes `{homo ...}`: mono gets the short name;
  homo gets suffix `W`.
- When `{mono ...}` is subdomain-restricted: homo gets the short
  name; mono gets suffix `in`.

### Important: D, B, M, X as secondary operations

These suffixes abbreviate **secondary** operations in equational
lemma names. They are NOT used to abbreviate the main operation of
relational lemmas.

Example: `mulnDl` (D abbreviates + in a `*` lemma) but
`leq_add2l` (not `leq_D2l`).

---

## 13. Definition Naming Conventions

| Category | Convention | Example |
|----------|-----------|---------|
| Structure types | lowerCamelCase + `Type` | `unitRingType` |
| HB structures | UpperCamelCase | `UnitRing` |
| Mixins (bottom) | `is`/`has` + UpperCamelCase | `hasChoice`, `isNmodule` |
| Mixins (extend) | `A_C_isB` or `A_C_hasB` | `Nmodule_isZmodule`, `Zmodule_isPzRing` |
| Coq modules | UpperCamelCase | `NumDomain` |
| Definitions | `snake_case` | `hoelder_conjugate`, `normal_pdf` |
| Types (custom) | PascalCase | `LfunType`, `LspaceType` |

Abbreviations in type names:
- Z-module => `zmod`/`Zmod`
- L-module => `lmod`/`Lmod`
- L-algebra => `lalg`/`Lalg`
- Partial order => `porder`/`POrder`

---

## 14. Variable and Hypothesis Naming

| Type | Conventional Names |
|------|-------------------|
| Natural numbers/integers | `m`, `n`, `p`, `d` |
| Ring elements | `x`, `y`, `z`, `u`, `v`, `w` |
| Polynomials | `p`, `q`, `r` (lowercase) |
| Matrices | `A`, `B`, ..., `M`, `N` |
| Polymorphic variables | `x` |
| Induction hypotheses | `IH` or `ih` prefix (e.g., `IHn`) |

**Hypotheses must have meaningful names.** Never use `H`, `H'`, `H''`
(these collide with subgroup variable conventions).

Pattern: hypothesis `n > 0` should be named `n_gt0`.

Scope rules:
- Variables that do not survive the line: can use `?`.
- Very short scope (~1-5 lines): short name OK.
- Longer scope (>5 lines): must have a meaningful name.

---

## 15. HB Instance Patterns

### Standard Instance Declaration

```coq
HB.instance Definition _ := hasDecEq.Build T proof.
```

or with explicit arguments:

```coq
HB.instance Definition _ := @hasDecEq.Build T eq_op proof.
```

### Section + HB.instance Pattern (recommended)

For morphisms and structured instances, the recommended pattern is:

```coq
Section foo_instance.
Variables (X Y : someType).
Let f := fun x => ...
Let hf : some_property f := ...
HB.instance Definition _ := SomeMixin.Build ... f hf.
Definition foo : someBundledType := f.
End foo_instance.
```

This avoids `HB.pack` and gives better control over types.

### Common Forms

1. **Builder**: `MixinName.Build args...`
2. **Transfer**: `[Structure of Type by <:]`
3. **On**: `Structure.on term`
4. **Copy/Alias**: `Structure.copy T expr`

### HB.lock for Computation Control

```coq
HB.lock Definition foo := ...
Canonical locked_foo := Unlockable foo.unlock.
Arguments foo ...
```

Used to prevent unfolding during type-checking.

### HB Mixin and Structure Naming

- `HB.mixin Record isFoo ...` -- `is` prefix, PascalCase
- `HB.structure Definition Foo ...` -- PascalCase, no prefix
- `#[short(type=fooType)]` for short type name

---

## 16. Arguments and Implicit Types

### `Arguments` Declarations

```coq
Arguments foo {d T R} mu p f.
Arguments bar {_ _ _ _ _} _.
```

- `Arguments` appears immediately after a definition or after `End`
  of a section (when section-local `Arguments` settings are lost).
- Implicit arguments use `{}`.
- Named arguments for meaningful positions; `_` for positional.
- **`Arguments` is section-local in Rocq**: when a section closes,
  `Arguments` settings are lost. Post-`End` re-declarations are
  NECESSARY, not duplicates.

### `Implicit Types`

Always declared inside sections:

```coq
Implicit Types (f g : R -> R) (a b : R).
Implicit Types (p : \bar R) (f : T -> \bar R).
Implicit Type n : nat.
```

Use parenthesized groups to mix different types on one line. Helps
keep lemma statements short (< 80 chars).

---

## 17. Deprecation Protocol

### For Renaming

```coq
Definition foo_new := ...
#[deprecated(since="analysis X.Y.Z", note="Use foo_new instead.")]
Notation foo_old := foo_new (only parsing).
```

### For Scheduled Deletion

```coq
(* Rename the lemma first *)
Lemma __deprecated__lem := ...
#[deprecated(since="analysis X.Y.Z", note="Use other_lemma instead.")]
Notation lem := __deprecated__lem (only parsing).
```

Rules:
- Must be at **top-level** (not inside a section).
- `(only parsing)` is **mandatory** so Coq doesn't print back the
  deprecated name.
- Warnings must be kept for **at least one release**, goal is
  **at least two years**.
- **Exception**: internal definitions marked as `Fact` or `Local`
  do not require deprecation unless CI breakage is observed.
- Internal identifiers should use `_subdef`/`_subproof` suffixes
  (blacklisted by `Search`).

---

## 18. Local vs Global Visibility

- **`Local Definition`** and **`Local Lemma`** for auxiliary
  results, showcase/exercise definitions, and anything that should
  not leak outside the file.
- **`Fact`** (not `Lemma`) for internal lemmas used only for
  declaring instances. `Fact` indicates internal status.
- Main results of a file should NOT be marked `Local` (PR #1015:
  "this looks like the main result of this PR, it's
  strange to see it tagged local").
- Use `Let` inside sections for section-local bindings.

---

## 19. Analysis-Specific Conventions

### Convergence Naming

| Statement form | Preferred? | Lemma string |
|---------------|-----------|-------------|
| `F --> x` | YES (preferred) | `cvg` |
| `lim F` | Only when no other expression for limit | `lim` |
| `cvg F` | When limit unknown | `is_cvg` |

### `near` Tactics vs Filter Lemmas

- When proof doesn't need to change epsilon: use `filterS`,
  `filterS2`, `filterS3` lemma combinators.
- When epsilon-delta reasoning is needed: use `near` tactics.

### Properties of Functions

- **Composites** use single-letter suffix: `cvgM`, `continuousM`,
  `deriveX`, `measurable_funX`
- **Applied functions** use multi-letter prefix: `mul_continuous`,
  `exp_derive`, `exp_measurable_fun`

### Set Constructions

- `_ !=set0` => suffix `nonempty`
- `_ != set0` => suffix `neq0`

### Landau Notations

Four shapes:
1. `f =o_F e` (binary functional)
2. `f = g +o_F e` (ternary functional)
3. `f x =o_(x \near F) (e x)` (binary pointwise)
4. `f x = g x +o_(x \near F) (e x)` (ternary pointwise)

---

## 20. Changelog Conventions

Structure of `CHANGELOG_UNRELEASED.md`:

```markdown
### Added
- in `filename.v`:
  + new definition `name`
  + new lemma `name1`, `name2`

### Changed
### Renamed
### Generalized
### Deprecated
### Removed
### Infrastructure
### Misc
```

Rules:
- Entries grouped by file with `in 'filename.v':`.
- Items prefixed with `+`.
- Code elements in backticks.
- Every user-visible change needs a changelog entry.
- Distinguish between renamed and newly-created lemmas.

---

## 21. Common Review Rejections

The following are the most frequent reasons PRs are sent back for
revision, in approximate order of frequency:

1. **Line too long** (> 80 chars) -- immediate correction requested.
2. **Wrong lemma name** -- does not follow `mainSymbol_suffix`
   convention.
3. **Missing header documentation** for new definitions.
4. **Missing changelog entry** for public API changes.
5. **Overly strong preconditions** -- reviewers push to weaken type
   constraints ("the precondition can be weakened to...").
6. **Redundant lemmas** -- reviewers check if subsumed by existing
   lemma.
7. **Unnecessary `Local`** on main results, or missing `Local` on
   auxiliary results.
8. **Generalization requests** -- "This could generalize to
   `topologicalType`" is recurring.
9. **Unfactored intermediate results** -- useful intermediate lemmas
   buried in long proofs should be factored out (PR #984).
10. **Typos in comments/documentation**.
11. **Wrong tactic spacing** -- space before `=>` after tactic
    keyword.
12. **`Focus`/`{}` usage** instead of proper indentation.
13. **Setoid/Morphisms imports in main files** -- should be in
    separate compatibility files (PR #1230).
14. **Useless type constraints** in lemma statements (Section 24).
15. **Useless scope delimiters** like `%R` already provided by an
    open scope (Section 6).
16. **`@` without good reason** (Section 25).
17. **Useless arguments to `exact:`** -- e.g., `exact: foo a b` when
    `exact: foo` suffices (Section 22).
18. **Fully-qualified identifiers** because the right file was not
    imported (Section 23).
19. **Useless lines** that could be `by [].` (Section 22).
20. **Hypothesis named only to be consumed once** -- prefer `move=> ->`
    (Section 27).
21. **`Internal` in a lemma name** (analysis PR #469:
    "Never use a lemma called `Internal`"). Use `_subdef`/`_subproof`
    suffixes for hidden auxiliaries instead.
22. **Implicational lemma where an equation would do** -- reviewers
    push for `P = Q` (Section 32.4) over `P -> Q` whenever both
    directions hold.
23. **One-direction lemma when its dual is missing** -- if you add
    a left-sided variant, add the right-sided one (analysis PRs
    #514, #780, #535).
24. **Manual case analysis when a `Variant`/`leqP`-style lemma
    exists** (analysis PR #410; Section 28).
25. **`Definition` for a thin wrapper that should be `Notation`**
    (Section 32; analysis PRs #311, #1244).
26. **`is_` prefix on a packaged operator** (analysis
    PR #223). Reserve `is_`/`has_` for predicates / structure
    factories.
27. **`apply: lem; exact: x`** when `exact: lem x` suffices, OR vice
    versa: `by exact: ...` when `exact: ...` is already a closer
    (math-comp PR #41: never both `by` and `exact:`).
28. **File over ~3000 lines** -- split by topic (analysis
    PR #1544).
29. **Lemma in the wrong file** -- reviewers (analysis
    PR #334) flag misplaced lemmas: e.g., a `topology` lemma must
    live in `topology.v`.
30. **Spurious newlines / trailing whitespace / double spaces**
    (math-comp PRs #944, #965, #511).

---

## 22. Concision and Triviality (Maintainer Feedback)

This section captures specific guidance distilled from
mathcomp-analysis maintainer review feedback. The single overarching
principle is: **delete anything the elaborator can do for you, and
stop one tactic earlier than feels safe.**

### 22.1 Replace useless lines with `by [].`

When an entire line of bookkeeping does nothing the trivial tactic
cannot do, just write `by [].`.

```coq
(* WRONG -- useless rewriting that `done` already handles *)
by move: hr1; rewrite /= /preorder.Order.le /=.

(* RIGHT *)
by [].
```

```coq
(* WRONG -- the rewritten goal is already definitionally equal *)
have -> : (fun p : R * X =>
             ((f : W -> X -> Y) \o alpha) p.1 p.2) \o beta =
          (fun r => ((f : W -> X -> Y) (alpha r))
             ((g : W -> X) (alpha r))) by [].
by [].

(* RIGHT *)
by [].
```

**Rule of thumb**: If a `have -> : E by [].` is followed by `by [].`,
the rewriting was redundant -- both sides are definitionally equal,
and `done` would have closed the goal directly. Try `by [].` first; if
it works, delete the rewrite.

**Diagnostic technique**: After every multi-tactic line that "feels
heavy", try replacing it with `by [].` (or `done.`). If the proof
still goes through, keep the simpler version.

### 22.2 Drop useless arguments to `exact:`, `apply:`, etc.

`exact:` and `apply:` perform unification. Often the lemma's
arguments are recovered automatically from the goal. Pass arguments
only when needed to disambiguate.

```coq
(* WRONG -- extra arguments are inferable from the goal *)
exact: measurableT_comp measurable_fst halpha.

(* RIGHT *)
exact: measurableT_comp.
```

```coq
(* WRONG *)
apply: ler_trans hxy hyz.

(* RIGHT (when the chain matches the goal) *)
apply: ler_trans.
```

When in doubt, strip arguments one at a time until the tactic fails.

### 22.3 Drop useless scope delimiters

Once the relevant scope is open (locally or in the section), `%R`,
`%N`, `%E`, `%nat`, `%classic` etc. are noise.

```coq
Local Open Scope ring_scope.

(* WRONG *)
Lemma foo (x : R) : (x + 0)%R = x.

(* RIGHT *)
Lemma foo (x : R) : x + 0 = x.
```

A scope delimiter is needed only when **switching** scope locally,
e.g., writing an `\bar R` expression inside a `ring_scope` block:

```coq
(* OK -- explicit because we are in ring_scope *)
Lemma foo : (1 + 1)%E = 2%:E.
```

### 22.4 Avoid useless type declarations

Many mathcomp-analysis structures carry **display** parameters
(`measure_display`, `Order.disp_t`, `latticeType disp`) that are
inferred from the surrounding context. Pass them explicitly only when
inference fails.

```coq
(* WRONG -- the display is inferable *)
Lemma foo (T : measurableType default_measure_display)
          (R : realType) ... .

(* RIGHT *)
Lemma foo d (T : measurableType d) (R : realType) ... .

(* OFTEN BETTER -- if the section already has Context for d, T, R *)
Section foo_section.
Context d {T : measurableType d} {R : realType}.
Lemma foo ... .
```

When `d` is otherwise unused, write `_ {T : measurableType _}` to let
unification fill it.

### 22.5 The minimal-tactic mindset

For every tactic line, ask:

1. Is there an argument I can drop? (Section 22.2)
2. Is there a scope delimiter I can drop? (Section 22.3)
3. Is there a type annotation I can drop? (Sections 22.4, 24)
4. Is there a `@` I can drop? (Section 25)
5. Is there a hypothesis name I can replace with `?` or `->`?
   (Section 27)
6. Could the whole line be `by [].`? (Section 22.1)

If you cannot answer "no" to all six, the line is not yet minimal.

---

## 23. Avoiding Fully-Qualified Identifiers

Fully-qualified module paths in source (`order.Order.TotalTheory.ltNge`,
`boolp.asbool`, `filter.cvg_within`) are a smell: they almost always
mean the right `Import` is missing, so the user-facing notation or
short name is not in scope.

### 23.1 The diagnostic

Search the file for any identifier of the form `lowercase_module.X`
or `lowercase_module.UpperCamel.Y`. Each such occurrence indicates a
missing `Import`.

```coq
(* WRONG *)
exact: order.Order.TotalTheory.ltNge.

(* RIGHT -- after `Import Order.TotalTheory.` *)
exact: ltNge.
```

```coq
(* WRONG -- boolp not Imported *)
have := boolp.asbool_eq.

(* RIGHT *)
have := asbool_eq.
```

### 23.2 Common imports needed in analysis files

| If you reference... | Add at top of file or section |
|---------------------|------------------------------|
| `Order.TotalTheory.X` (lt/le on totalOrder) -- canonical short alias is `TTheory` | `Import Order.TTheory.` |
| `Order.POrderTheory.X` | `Import Order.POrderTheory.` |
| `boolp.asbool`, `asboolP`, `propeqP` | `Import boolp.` (the file is `mathcomp/classical/boolp.v`) |
| `--->` (cvg notation), `\near`, `nbhs` filter notations | Ensure `topology`/`filter` are imported, *and* the right `Exports` |
| `numFieldTopology` lemmas | `Import numFieldTopology.Exports.` |
| `numFieldNormedType` lemmas | `Import numFieldNormedType.Exports.` |
| `GRing.Theory` (`addrA`, etc.) | `Import GRing.Theory.` |
| `Num.Theory` (`ler_*`) | `Import Num.Theory.` |
| `Num.Def` (`Posz`, `normr`) | `Import Num.Def.` |
| `archimedean.Num.Theory.Znat_def` etc. | `Import archimedean.Num.Theory.` |
| `lebesgue_integral.Set` | `Import lebesgue_integral.` |

The standard preamble for an analysis file is:

```coq
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
```

`Order.TTheory` is the canonical short alias for the bundled order
theory; spelling it `Order.TotalTheory` (or worse,
`order.Order.TotalTheory.X` in source) is wrong. If you need a
restricted theory module, prefer `Order.POrderTheory`,
`Order.LatticeTheory`, etc.

### 23.3 The `From mathcomp Require Import` form

**Always** use `From mathcomp Require Import X.` (capital `From`),
**never** `Require Import mathcomp.X.Y.`. The unqualified `From` form
respects build-system path conventions and is the project-wide
standard (see `lemma-overloading` issue #22 for an example of the
fix being applied).

### 23.4 The convergence-notation gotcha

`F --> x`, `lim F`, and `\forall x \near F, P x` are notations defined
inside specific module Exports. If they look unrecognized, you almost
always need one of:

```coq
Import topology.
Import filter.   (* in newer mathcomp-analysis where filter.v split off *)
```

When a maintainer comments "convergence notation not available", that
is the fix.

### 23.5 Why short names matter

- They are what readers searching by `Search` will find.
- Long paths break when the module is reorganized upstream.
- The bundled `Import X.Theory.` form is the project-wide convention;
  using bare module paths breaks consistency.

---

## 24. Type Constraint Hygiene

Mathcomp uses canonical structures and HB to infer types. Explicit
annotations should be used **only** when inference fails or
disambiguation is required, never as a "safety belt".

### 24.1 Don't constrain product/sum types

```coq
(* WRONG -- the product structure is canonical *)
Lemma foo (M1 M2 : measurableType _)
          (f : [the measurableType _ of (M1 * M2)%type] -> R) ...

(* RIGHT *)
Lemma foo (M1 M2 : measurableType _) (f : M1 * M2 -> R) ...
```

`M1 * M2` already resolves to a `measurableType` via the canonical
product instance. Adding `[the measurableType _ of ...]` is noise.

### 24.2 Don't re-state the type of an already-typed name

```coq
(* WRONG *)
move=> (x : R) (h : 0 <= x).

(* RIGHT *)
move=> x h.
```

The hypothesis `h : 0 <= x` has its type fixed by the goal;
restating it is redundant.

### 24.3 Avoid `: T` on lambda parameters when inferable

```coq
(* WRONG *)
fun (p : R * X) => f p.1 p.2.

(* RIGHT (when the surrounding context fixes the type) *)
fun p => f p.1 p.2.
```

### 24.4 Use displays as wildcards

```coq
(* WRONG *)
Variable T : measurableType default_measure_display.

(* RIGHT *)
Variable d : measure_display.
Variable T : measurableType d.

(* OR -- if d is never referenced again *)
Variable T : measurableType _.
```

Naming `d` is preferred when other variables share it (you want the
displays to unify); `_` is fine for one-off uses.

### 24.5 Heuristic for keeping a constraint

Keep an explicit type annotation only if **at least one** holds:

- Removing it produces an "unable to unify" error.
- It documents an intended-but-otherwise-ambiguous interpretation
  (e.g., `0 :> R` to disambiguate `0`).
- It is part of a `Variable` / `Implicit Types` declaration meant to
  be read by humans.

Otherwise, delete it.

---

## 25. The `@` Discipline

`@lemma` disables implicit-argument resolution and forces every
argument to be supplied positionally. It is sometimes necessary, but
mathcomp reviewers reject it whenever the elaborator could have done
the work.

### 25.1 When `@` is wrong

If every explicit argument you pass is one the elaborator would have
inferred anyway, drop the `@`:

```coq
(* WRONG -- all the arguments are inferable from the goal *)
exact: @measurableT_comp _ _ _ _ _ measurable_fst halpha.

(* RIGHT *)
exact: measurableT_comp.
```

### 25.2 When `@` is justified

`@` is acceptable (sometimes necessary) only when:

1. **Disambiguation**: the elaborator cannot pick between two
   instances and would otherwise complain.
2. **Positional access** to an argument that is otherwise implicit and
   has no name-based syntax: e.g., `@addrA R x y z` to refer to the
   ring `R` explicitly.
3. **Constructing a term** (not in tactics) where you want to be
   explicit for readability of a definitional equation.

Even in these cases, prefer named arguments: `lemma_name (R := myRing)`
rather than `@lemma_name myRing _ _ _`.

### 25.3 The rewrite-style alternative

Instead of `rewrite (@foo _ x _)`, prefer `rewrite (foo (a := x))` or
`rewrite [in X in _ = X]foo`. The pattern-based form is more
maintenance-friendly.

### 25.4 Cleanup pattern

Whenever you find yourself writing `@`, before committing, try once
without it. If the proof still goes through, the `@` was unnecessary.

---

## 26. Closing Tactics and Terminators

Every line that closes a goal must visually mark itself as a
terminator. The convention is:

- **`by` prefix** for any tactic line that closes a goal.
- **`exact:` / `exact`** as a self-contained terminator.
- **`apply:`** alone never closes a goal -- if it does, it should
  have been `exact:`.

### 26.1 Wrong vs right

```coq
(* WRONG -- this line closes the goal but doesn't start with `by` *)
rewrite addrA addrC.

(* RIGHT *)
by rewrite addrA addrC.
```

```coq
(* WRONG *)
apply: lemma_name.

(* RIGHT (when this closes the goal) *)
exact: lemma_name.
```

### 26.2 The `exact:` vs `apply:` rule

| Situation | Use |
|-----------|-----|
| Term solves the goal directly | `exact: term` |
| Term reduces the goal to subgoals | `apply: term` |
| Term solves the goal but creates side conditions discharged by `done` | `exact: term` (if `done` discharges them) or `by apply: term` |

Mathcomp culture: a reader scanning the proof should be able to spot
goal-closing lines just by looking at left margins. `by` and `exact:`
serve that visual cue.

### 26.3 Don't close a goal without a terminator

Even a one-liner like:

```coq
Proof. rewrite foo. Qed.
```

is rejected; write:

```coq
Proof. by rewrite foo. Qed.
```

### 26.4 The `//` and `//=` shortcuts

Inside a chain, `//` discharges trivial subgoals (= `by []`), and
`//=` does the same plus simplification:

```coq
by rewrite foo // bar //= baz.
```

This obviates writing trailing `; by [].` calls.

---

## 27. Book-Keeping Idioms in Proof Scripts

The single biggest source of "extra book-keeping" in proofs is
introducing names for hypotheses that are used only once. Prefer
SSReflect's intro-pattern combinators.

### 27.1 Rewrite during introduction with `->` and `<-`

```coq
(* WRONG -- name introduced just to rewrite once *)
move=> H; rewrite H.

(* RIGHT *)
move=> ->.
```

```coq
(* WRONG *)
move=> Heq; rewrite -Heq.

(* RIGHT *)
move=> <-.
```

### 27.2 Discard a hypothesis with `_`

```coq
(* WRONG *)
move=> Hunused x; exact: foo x.

(* RIGHT *)
move=> _ x; exact: foo x.
```

### 27.3 Apply immediately with `/lem`

```coq
(* WRONG *)
move=> H; apply/eqP in H.

(* RIGHT *)
move=> /eqP H.   (* reflect-style introduction *)
```

```coq
(* WRONG *)
move=> H; case: H => H1 H2.

(* RIGHT *)
move=> [H1 H2].
```

### 27.4 Don't name a final hypothesis you immediately consume

```coq
(* WRONG *)
move=> halpha U hU; exact: hU.

(* RIGHT *)
move=> halpha U; exact.
```

`exact.` (no argument) uses the top of the stack. Equivalently:

```coq
move=> halpha U; apply.
```

### 27.5 Combine introduction with destructuring

| Pattern | Effect |
|---------|--------|
| `move=> [a b]` | Destruct a pair/conjunction |
| `move=> [a | b]` | Destruct a sum/disjunction |
| `move=> [a [b c]]` | Nested destruct |
| `move=> [\| a]` | Match nat (zero \| succ a) |
| `move=> //` | Introduce and discharge if trivial |
| `move=> ?` | Introduce with an auto-generated name |
| `move=> *` | Introduce all remaining variables |

### 27.6 Forward chaining with `have`

When you must name an intermediate fact, prefer `have` with an
intro-pattern that consumes it inline rather than naming and reusing:

```coq
(* WRONG *)
have H : 0 <= x by exact: ge0_x.
rewrite (le_trans H _).

(* RIGHT (when H is used once) *)
rewrite (le_trans (ge0_x _) _).
```

Use `have` with a name only when the fact is reused multiple times.

**Anonymous `have ?` for `//`-dischargeable side conditions.** When a
fact's only role is to be picked up by `//` / `assumption` in later
`rewrite` chains, give it the anonymous introduction pattern `?`. This
front-loads positivity / non-zeroness at the top of a proof so the
body's `rewrite lemma//` chains shrink to one line each:

```coq
(* WRONG -- named, then never referenced by name; the name is noise *)
have sum_pos : 0 < sigma0 ^+ 2 + sigma ^+ 2 by apply: addr_gt0.
have sqsum_neq0 : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0.
  rewrite sqrtr_eq0 -ltNge; apply: addr_gt0; rewrite exprn_even_gt0 //=.

(* RIGHT -- anonymous; the second `have` reuses the first via assumption *)
have ? : 0 < sigma0 ^+ 2 + sigma ^+ 2 by apply: addr_gt0.
have ? : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0
  by rewrite sqrtr_eq0 -ltNge.
```

**Parser caveat.** `have ? : T.` opens a sub-proof that must close in
a *single* indented `by …` line. Multi-line sub-proofs (two or more
indented tactics — typical when a bulleted goal split is needed) fail
to parse under the anonymous form; use a named `have` instead. Keep
this in mind when promoting an existing named `have` to `have ?`: if
the sub-proof spans multiple lines, leave the name.

```coq
(* OK -- single-line sub-proof *)
have ? : 0 < stddev_post sigma0 sigma
  by rewrite /stddev_post sqrtr_gt0 divr_gt0// mulr_gt0.

(* OK -- inline `by` *)
have ? : 0 < sigma0 ^+ 2 by rewrite exprn_even_gt0.

(* NOT OK with `?` -- two-line sub-proof; name it instead *)
have Kpos : 0 < K.
  rewrite /K normal_pdfE //; apply: mulr_gt0.
    by rewrite normal_peak_gt0.
  by rewrite /normal_fun expR_gt0.
```

**Importing a top-level lemma into the assumption pool** with
`have ? := lemma args.`:

```coq
have ? := stddev_post_neq0 _ _ sigma0_neq0 sigma_neq0.
rewrite !normal_pdfE //   (* finds `stddev_post sigma0 sigma != 0` *)
```

This is the canonical way to surface a top-level fact for `//`
discharge without manually re-deriving it.

### 27.7 The `=> ->` pattern after equality lemmas

When a lemma yields an equality, chain `apply` and `rewrite` via
`/lemma` and `->`:

```coq
(* WRONG *)
move=> /eq_foo Heq; rewrite Heq.

(* RIGHT *)
move=> /eq_foo ->.
```

### 27.8 Indentation and bullets recap

Restating Section 8 in the language of the maintainer feedback:

- After a tactic that opens **two** subgoals, indent the first by 2
  spaces and leave the second un-indented:
  ```coq
  case: x => [a | b c].
    by rewrite foo.
  by rewrite bar baz.
  ```
- After a tactic that opens **three or more** subgoals, use bullets
  `-` / `+` / `*` strictly nested.
- Use `last first` (or `first last`) to push a small subgoal up so the
  main flow stays at the outer indent level.
- Never mix bullet styles at the same level.

**No bullets when only 2 subgoals are generated** -- two-space
indentation suffices (analysis PR #410).

---

## 28. Idiomatic Case Analysis

Mathcomp culture prefers reflection-style case analysis through
**dedicated lemmas** (`leP`, `ltgtP`, `eqVneq`, `altP`, etc.) rather
than ad-hoc `destruct` / `case` on raw inductive data. The dedicated
lemmas leave the **goal in equational form** so they can be chained.

### 28.1 The standard family

| Lemma / view | Use case |
|--------------|----------|
| `eqP` | turn `a = b` proofs into `a == b` (decidable equality) |
| `eqVneq x y` | branch on `x = y` vs `x != y`, no boolean residual |
| `altP P` | branch on `P` vs `~~ P`, with reflect-style residual |
| `leP m n` | branch on `m <= n` vs `n < m` (nat) |
| `ltP m n` | branch on `m < n` vs `n <= m` |
| `ltgtP x y` | three-way: `x < y` / `x = y` / `x > y` |
| `posnumP x` | get a `{posnum R}` from `0 < x` |
| `real_leP` | `leP` analogue for real domains |

```coq
(* WRONG -- manual case analysis *)
case: (eqVneq x y) => Hxy.
  rewrite Hxy ...
case: (eqVneq x y) => Hxy.
  by ...

(* RIGHT -- chained with intro patterns *)
case: eqVneq => [-> | xy_neq].
  by ...
```

```coq
(* RIGHT -- three-way comparison in one step (analysis PR #817) *)
have [x0 | | ->] := ltgtP x 0.
- (* x < 0 *) ...
- (* x > 0 *) ...
(* x = 0 -- main flow *)
```

### 28.2 Encode case structure with `Variant`

When you find yourself writing the same ad-hoc case split repeatedly,
extract it to a `Variant` and a specification lemma in the style of
`eqVneq` / `leqP` (analysis PR #410):

```coq
Variant compare_int (m n : int) : bool -> bool -> bool -> Set :=
  | CompareIntLt of m < n : compare_int m n true false false
  | CompareIntGt of m > n : compare_int m n false true false
  | CompareIntEq of m = n : compare_int m n false false true.

Lemma compareIntP m n : compare_int m n (m < n) (m > n) (m == n).
Proof. ... Qed.
```

Then `case: compareIntP` does the case analysis declaratively.

**`Variant` vs `Inductive`**: use `Variant` when the type is purely
case-analysis machinery (no recursion, no induction principle
needed). Note: by default Rocq still generates `_rec`/`_ind`/`_rect`
schemes for `Variant`; mathcomp suppresses them globally via
`Unset Elimination Schemes` in its preamble, so within mathcomp
`Variant` is the right intent-signalling choice. Outside mathcomp
the schemes are still emitted unless you opt out.

### 28.3 Disjunction in intro patterns

Don't `case` after `move=>`; combine:

```coq
(* WRONG *)
move=> H; case: H => [Ha | Hb].

(* RIGHT *)
move=> [Ha | Hb].
```

For "split" goals (a conjunction-shaped target):

```coq
(* WRONG *)
split.
  by ...
by ...

(* RIGHT, for a binary split *)
split=> [|]; by [|].

(* RIGHT, with intro patterns inside *)
apply/seteqP; split=> [x [[Ax|Bx] Cx] | x [[Ax Cx]|[Bx Cx]]].
- by left.
- by right.
- by split=> //; left.
- by split=> //; right.
```
(analysis PR #1222)

---

## 29. Rewriting Idioms

### 29.1 `under` for under-binder rewriting

Rewriting under a binder (e.g., inside `\sum_(i < n) f i`) is the
classic motivation for `under`:

```coq
(* WRONG *)
apply: eq_bigr => i _; rewrite addrC -raddfN.

(* RIGHT *)
under eq_bigr => i _ do rewrite addrC -raddfN.
```
(math-comp PR #965)

`under` accepts a `do tac` clause to apply a tactic to each subgoal it
creates, leaving the main goal in compact form.

### 29.2 Localized rewrites with `[in RHS]`, `[LHS]`, `[in X in _]`

When a rewrite would otherwise apply at multiple positions:

```coq
(* WRONG -- relies on default selection *)
rewrite big_nat_cond.

(* RIGHT -- pin location *)
rewrite [in RHS]big_nat_cond.
rewrite [LHS]sum_integral_limn.
rewrite [in X in _ + X]addrA.
```
(analysis PR #1674: explicit patterns also signal intent
and were measured ~0.4s faster than default selection.)

### 29.3 `!` for repeated, `?` for optional

| Form | Meaning |
|------|---------|
| `rewrite L` | rewrite once; fails if no match |
| `rewrite ?L` | rewrite if applicable; never fails |
| `rewrite !L` | rewrite as many times as possible; fails if zero |
| `rewrite 2!L` | rewrite exactly twice |
| `rewrite -L` | rewrite right-to-left |
| `rewrite L1 L2 // L3` | discharge intermediate trivial subgoals |

A canonical idiom: `rewrite cond ?simpl_side //; next_rule.`

### 29.4 Avoid using `inE` right-to-left

```coq
(* WRONG -- behavior is unpredictable *)
rewrite -inE.

(* RIGHT -- inE is a multi-rule; use a specific in_X lemma *)
rewrite -in_set ...
```
(analysis PR #410: "`inE` should never be used with `-`
(right to left), this is not supposed to be predictable.")

### 29.5 Prefer `rewrite predeqE` to set extension by hand

For `setX = setY` goals, try `by rewrite predeqE.` (analysis
PR #162) before unfolding manually. Similarly:

- `apply/seteqP; split=> ...` for set equality with explicit witnesses
- `apply/funext=> x; ...` for function extensionality (or
  `exact: funext` if no x is needed)

### 29.6 Don't eta-expand to defeat `simpl`

```coq
(* WRONG -- adds simpl overhead *)
rewrite [pred y | leT x y]xxx.

(* RIGHT *)
rewrite (leT x).
```

### 29.7 `congr` for syntactic-skeleton rewriting

When the LHS and RHS share a common head and the goal reduces to
proving subterm equalities, prefer `congr` over manual rewriting:

```coq
(* Goal: f x y = f x' y' *)
congr (f _ _).
(* Now two subgoals: x = x', y = y' *)
```

`congr (f _)` strips one argument; `congr (g (h _))` strips through
nested constructors. Within a `\sum`/`\prod`/`\big` body, use
`under eq_bigr do congr (...)` to push the same skeleton inside the
binder.

Pair `congr` with `case:` discrimination when the head is a
constructor: `congr Some.`, `congr S.`, `congr (.+1).`
(math-comp PR #328)

---

## 30. Forward-Step and Symmetry Idioms

### 30.1 `wlog` for symmetry breaking

When two cases of a proof are symmetric, `wlog` reduces them to one:

```coq
(* WRONG -- both directions written out *)
case: (leP x y) => xy.
  ...
...

(* RIGHT *)
wlog: x y / x <= y => [hyp_sym | xy].
  by case: (leP x y) => xy; [exact: hyp_sym | apply: hyp_sym].
...
```

The `=> [hyp_sym | xy]` form names the symmetry hypothesis on the
first branch and the remaining case-assumption on the second.

A heavier idiom (analysis PR #817):

```coq
wlog: x y z / 0 < x => [h | x0].
  have [x0 | | ->] := ltgtP x 0; [ | exact: h | by rewrite !mul0e].
  by apply: oppe_inj; rewrite -!mulNe h ?oppe_gt0.
```

### 30.2 `gen have` for in-proof lemma extraction

When a fact will be used several times in the proof, factor it
without leaving the proof:

```coq
gen have lem, _ : x y H / P x y.
  (* prove P x y under hypothesis H *)
(* now `lem` is available in the rest of the proof *)
```

Use `gen have` instead of duplicating proof bodies.

### 30.3 The `near` skeleton

For epsilon-delta-style filter proofs:

```coq
rewrite openE => x /=; rewrite -ball_normE /interior => xeps.
near=> z.
  ...
by near: z; apply: cvg_dist; rewrite // subr_gt0.
Grab Existential Variables. all: end_near.
```
(analysis PR #283)

The `Grab Existential Variables. all: end_near.` line at the end is
mandatory for closing leftover existentials introduced by `near`.

When epsilon does NOT need to shrink, prefer **filter combinators**
(`filterS`, `filterS2`, `filterS3`) over `near=>`.

### 30.4 The `Posnum` idiom

To go from `0 < e` to a `{posnum R}` you can use as a positive number:

```coq
move=> _ /posnumP[e].
```

After this, `e` has type `{posnum R}` and you can apply lemmas that
expect a positive bundled value.

### 30.5 `nbhs_ballP` / `nbhs_normP` views

When you have a goal `nbhs x A` for a metric / normed space:

```coq
apply/nbhs_ballP => /= eps eps_gt0.
(* or *)
apply/nbhs_normP => /= eps eps_gt0.
```

Both unpack the filter to an explicit ball / norm condition.

### 30.6 Replace `u_ --> +oo` unfoldings with the bundled form

If you find yourself manually expanding "for all M, eventually
$u_n > M$", that's the **definition** of `u_ --> +oo`. Use the
bundled statement and the corresponding `cvg_*` lemmas instead
(analysis PR #422).

---

## 31. Maximal Implicits and `Arguments` Discipline

### 31.1 Maximal implicits

A trailing implicit argument that should be filled even when the
function is partially applied must be declared with **braces** (not
square brackets). Square brackets denote *non-maximal* implicits and
trigger a warning when applied to trailing positions.

```coq
(* WRONG -- triggers "trailing implicit so must be maximal" *)
Arguments foo [T n] _.

(* RIGHT -- braces force the trailing implicit to be maximal *)
Arguments foo {T n} _.
```

Reviewers (math-comp PR #447) consistently
push for the brace form on trailing implicits to silence the warning
and make the function partial-application-friendly.

### 31.2 Don't pass `(f := ...)` if the variable name might change

```coq
(* FRAGILE *)
apply: lemma (f := fun x => g x).

(* PREFER -- positional or pattern-based *)
apply: (lemma _ (fun x => g x)).
```
(math-comp PR #1383: keyed application breaks if the
upstream lemma renames `f`.)

### 31.3 Make a lemma argument explicit to avoid `@` at use sites

If callers consistently need to write `@lem _ _ x` to fix one
argument, the upstream lemma should be redeclared with that argument
**explicit** (math-comp PR #860):

```coq
(* If users always write `@telescope_op _ _ f`, change the lemma to: *)
Lemma telescope_op (f : ...) ... : ... .
Arguments telescope_op f.
```

Then callers write `telescope_op f` cleanly.

### 31.4 Repeat `Arguments` after `End`

`Arguments` declarations made inside a section are **not preserved**
when the section closes. After `End Section.`, re-declare them at
top level if they should persist.

### 31.5 `Arguments lemma : simpl never` for opaque computation

When a definition should not unfold under `simpl` (typical for `Hb.lock`
locked definitions or computation-heavy terms):

```coq
Arguments my_def : simpl never.
```

---

## 32. Notation vs. Definition

Reviewers prefer `Notation` over `Definition` for **thin wrappers**
that exist only to give a shorter syntax (analysis PRs
#311, #1244):

```coq
(* SOMETIMES WRONG -- forces unfolding step at call sites *)
Definition foo (x : R) := bar x x.

(* OFTEN BETTER *)
Notation foo x := (bar x x).
```

The notation:
- Doesn't add a new identifier the unification engine must match.
- Is unfolded by display, so the user reads the original term.
- Doesn't require a separate `Arguments` declaration.

**When to keep `Definition`** instead:

- The term is computationally non-trivial and benefits from being
  abstracted in proofs (you can `rewrite /foo` to unfold).
- You need to attach typeclass / canonical structure instances to
  `foo` directly.
- The term has free variables you want to bind once (e.g., a
  measurable function with a measurability proof packaged in HB).

### 32.1 Drop the `is_` prefix on packaged operators

Predicates start with `is_` / `has_` / boolean-valued lemmas end with
`P`. Packaged **operators** do not (analysis PR #223):

```coq
(* WRONG -- not a predicate *)
Definition is_normal_pdf := fun x => ...

(* RIGHT *)
Definition normal_pdf := fun x => ...
```

### 32.2 Prefer `set U` over `pred U` in user-facing API

When defining a topology, measure space, or similar at the user
level, prefer `set U -> Prop` (or `set U -> bool` if decidable) over
`pred U`. Theory-level uses can stay in `pred U` (analysis
PR #311).

### 32.3 Provide notation aliases on rename

When renaming a public definition, leave a `Notation` alias for one
release (analysis PR #223):

```coq
Definition new_name := ...
Notation old_name := new_name (only parsing).
```

This is gentler than the `#[deprecated]` form when you want to keep
display output unchanged but still let old code parse.

### 32.4 Equations are better than implications

A lemma `P -> Q` is a one-shot tool; a lemma `P = Q` (or `P <-> Q`)
is reusable as a rewrite rule (analysis PR #1649):

```coq
(* WEAKER *)
Lemma foo_pos v : v > 0 -> norm v > 0.

(* STRONGER, prefer when both directions hold *)
Lemma foo_norm_neq0 v : (norm v > 0) = (v != 0).
```
(math-comp PR #1333)

When the equivalence holds, rephrase. Prefer **bidirectional**
statements; reviewers consistently push for this generalization.

---


## 33. PR Citation Index

A non-exhaustive index of upstream PR comments cited in this guide,
for cases where readers want to follow the original review thread.

**Caveat**: PR-to-rule attributions are approximate. A reviewer's
remark in PR #N often crystallises a community norm that predates
the PR and is enforced across many threads. Treat each row as
"a PR where this rule was discussed", not "the PR that introduced
this rule". Some rows have known discrepancies between PR topic
(what the PR was *about*) and the rule cited (what the *thread*
touched on); these are flagged with `[topic ≠ rule]` below.

### math-comp/math-comp

| PR | Topic |
|----|-------|
| #41 | One-line proofs start with `by`; no redundant trailing `exact:` |
| #270 | `@` only when grammatically necessary (e.g., notation disambiguation) |
| #292, #253, #447 | Maximal implicits for trailing implicits |
| #328 | Don't eta-expand to wrap `simpl` |
| #351 | Prefer `x != y` over `~ (x = y)` on `eqType`; `case: eqVneq` |
| #399 | `F` suffix on lemmas returning boolean false |
| #406 | Missing `Canonical` / `Coercion` in `Exports`; `pack` correctness |
| #408 | View chains in `[..|..]` patterns |
| #517 | `_l` / `_r` suffixes for left/right distributivity |
| #535 | "Maybe we want them all" -- add full dual family |
| #565 | Drop `by` when closer is `apply`/`exact` |
| #582 | View chains: `move/eq_map_mx->` |
| #593 | `case: leP`, `real_leP`; `{in D, forall t}` |
| #601 | Lemma names too short; "3 lines, not 6" |
| #624 | `count_subseqP` naming |
| #632 | `/andP[Px Ps]` directly when no intermediate name needed |
| #682 | Reformulate to most-general bigop form |
| #779 | One-line proofs open with `by` |
| #817 (math-comp) | Spacing around `=>` |
| #860 | Make argument explicit in lemma to avoid `@` at use sites |
| #944 | Indentation; readable hypothesis names |
| #965 | `under eq_bigr => i _ do rewrite ...`; spurious newlines |
| #1046 | `Arguments`/`Notation` separation; `(@Quotient.quot I) : type_scope` |
| #1196 | Section names need topic markers |
| #1198 | Drop `(_ )%N`/`(_ )%g` when scope is open |
| #1216 | Compaction by `rewrite … // …` |
| #1217 | `sorted_cat_cons` -- verbose but informative |
| #1318 | Unary predicates as suffix |
| #1383 | Avoid `(f := ...)`; concrete proof compaction |
| #1535 | Reformatting to 80 chars |
| #1933 | `move=> /(congr1 val); rewrite ...` chain |

### math-comp/analysis

| PR | Topic |
|----|-------|
| #21 | Generic mixins over global canonical structures |
| #124 | `by` immediately after `Proof.`; informative names |
| #128 | CI hygiene |
| #135 | `inE/=` (no space) |
| #136 | `exact: asboolP` to replace multi-step |
| #162 | Try `by rewrite predeqE.` first |
| #206 | Avoid duplicate orderings |
| #223 | No `is_` for packaged operators; `homo`/`mono` naming |
| #268, #284 | Identify and remove redundant lines/definitions |
| #280 | `_nonempty` vs `_neq0` |
| #283 | `near=>` skeleton with `Grab Existential Variables. all: end_near.` `[topic ≠ rule]` (PR is about closed balls; the skeleton is a community norm) |
| #311 | `Notation` over `Definition`; document; prefer `set U` |
| #313 | `le_ball` not `ball_ler` |
| #320 | `propext` rewrite in intro pattern |
| #334 | Locate lemmas in correct file |
| #350 | `\is a fin_num` predicate notation |
| #391 | Line overflow |
| #403 | `_subdef` is hidden in `Search` |
| #410 | No bullets for 2 subgoals; `inE` not right-to-left; `Variant` for case structure |
| #422 | Use bundled `--> +oo` |
| #469 | "Never use a lemma called `Internal`" |
| #511 | Move helper lemmas; spurious newlines |
| #514 | Scope ordering consistency; add dual lemmas |
| #532 | Drop `seq` for most general type |
| #535 | Keep `Proof.` even for one-liners |
| #558 | Split lines at `;` to fit 80 chars |
| #690 | `Proof. by []. Qed.` for trivial proofs |
| #712 | `*_idem` / `*_id` family naming |
| #780 | Add dual lemmas (`dual_adde`) |
| #786 | Aliases break forgetful inheritance |
| #815 | Indentation of multi-line statements |
| #817 (analysis) | shorter `muleA` proof using `wlog`/`ltgtP` (worked example, not the PR's main topic) |
| #821 | Document new definitions; deprecation aliases on rename |
| #823, #891 | Mandatory CHANGELOG entries |
| #1125 | Module organization (`Scale`) |
| #1222 | One-line set equalities; deprecation aliases |
| #1244 | Don't restate; import the namespace |
| #1351 | `Local Definition` / `Local Lemma` for non-exported `[topic ≠ rule]` (PR is about π-irrationality; the discipline is community-wide) |
| #1383 (analysis) | Concrete proof compactions |
| #1385 | `cvgr_` prefix when specialised to reals |
| #1544 | File length cap; in-file duplication |
| #1558 | Suffix conventions after `P` |
| #1563 | `by` forbidden in `core` HintDb |
| #1565 | Match local style of neighboring proofs |
| #1649 | Lemmas should be bidirectional / equational when possible |
| #1674 | `[in RHS]` / `[LHS]` rewrite patterns; `apply/foo/bar` chains |
| #1678 | Composition through views (`exact/funext/fct_prodE`) |
| #1679 | `sqrtK` (cancel-suffix) over `sqrK` |
| #1683 | Forward-style hypothesis introduction |
| #1825 | Drop unnecessary parentheses in boolean expressions |
| #1827 | `k \in S` over `in_set S k` |

This index is not exhaustive; treat it as a starting point for
deeper searches in the upstream review history.

---

## 34. Bigop Idioms

The `bigop` library (`mathcomp/boot/bigop.v`, ~2800 lines) is the
single most-rewritten file in any mathcomp proof. Reviewers
consistently flag two regressions: (1) rolling manual recursion
over a `seq` when a `big_*` lemma applies, and (2) using
`apply: eq_bigr` followed by per-`i` tactics instead of a one-line
`under eq_bigr do ...`. This section codifies the canonical idioms.

### 34.1 Reading the notation

The general form is `\big[op/idx]_<range> <body>`, where `op` is the
binary operator, `idx` is the identity (returned for an empty
range), and `<range>` is one of:

| Range | Meaning |
|-------|---------|
| `(i <- s)` | `i` ranges over the `seq` `s` |
| `(m <= i < n)` | `i` ranges over `iota m (n - m)`, i.e. `m, ..., n - 1` |
| `(i < n)` | `i : 'I_n` (ordinal); the canonical "for-loop" form |
| `(i : T)` | `i` ranges over `index_enum T` (`T` is a `finType`) |
| `i` or `(i)` | same, type inferred from context |
| `(i in A)` | `i` ranges over the `finType`, restricted to `i \in A` |
| `(i <- s \| P i)` | filter `s` by `P` (any range can take a `\| P i` tail) |

The standard aliases unfold to `\big`:

```coq
\sum_(...) F  ==  \big[+%R/0]_(...) F   (* in ring scope *)
\prod_(...) F ==  \big[*%R/1]_(...) F
\bigcup_(...) F, \bigcap_(...) F        (* over set / group lattices *)
\meet_(...) F, \join_(...) F            (* on lattices *)
```

Use `\sum`, `\prod`, etc., **not** `\big[+%R/0]_...` directly --
reviewers reject the latter as opaque. Reach for `\big[op/idx]` only
when `op` is genuinely non-standard (e.g. iterated function
composition, custom monoid).

`BIG_F` and `BIG_P` are pattern abbreviations that select the body
and predicate inside a `\big`; useful with `[in X in BIG_F]` etc.

The head constant of every `\big` notation is the **locked**
`bigop`. Underneath sits the transparent `reducebig`, defined as
`foldr (applybig \o body) idx r` (bigop.v line 585). You almost
never `unlock` it -- the lemma family below covers every reasonable
manipulation.

### 34.2 The core lemma family

Spot-checked against `mathcomp/boot/bigop.v` (paths in this guide
assume `rocq-9.1`; the file moved from `ssreflect/` to `boot/` in
mathcomp 2.x but the contents are stable).

| Lemma | What it does |
|-------|--------------|
| `eq_bigr` (l. 929) | `(forall i, P i -> F1 i = F2 i) -> \big...F1 = \big...F2` -- rewrite the **body** under the binder |
| `eq_bigl` (l. 918) | `P1 =1 P2 -> \big_(\| P1) = \big_(\| P2)` -- rewrite the **predicate** |
| `eq_big` (l. 933) | both at once |
| `bigID a` (l. 2041) | split the predicate: `\big_(\| P) = \big_(\| P && a) * \big_(\| P && ~~ a)` |
| `partition_big p Q` (l. 2064) | partition by `p : I -> J` into a J-indexed double sum |
| `big_cat` (l. 1817) | `\big_(i <- r1 ++ r2) = \big_(_ <- r1) * \big_(_ <- r2)` |
| `big_split` (l. 2036) | `\big_(F1 i * F2 i) = \big F1 * \big F2` (abelian monoid) |
| `big_seq` (l. 1020) | adds the `i \in r` side condition (for `eqType`) |
| `big_seq_cond` (l. 1013) | same but preserving an existing `P` |
| `big_mkcond` (l. 1786) | turn `\big_(\| P) F` into `\big_ (if P then F else 1)` |
| `big_mkord` (l. 1092) | nat-iota range to ordinal range |
| `bigD1 j` (l. 1389) | extract one element: `P j -> \big_(\| P) F = F j * \big_(\| P && (i != j))` |
| `bigD1_seq j` (l. 1398) | same on a `uniq` `seq` |
| `big_ord_recl` (l. 1202) | `\big_(i < n.+1) = F ord0 * \big_(i < n) F (lift i)` |
| `big_ord_recr` (l. 1941) | symmetric: peel from the right |
| `big_nat_recl` (l. 1087) | analogue for `(m <= i < n.+1)` ranges |
| `big_const_seq` (l. 1258) | `\big_(_ <- r \| P) x = iter (count P r) (op x) idx` |
| `big_const` (l. 1262) | finType: `\big_(i in A) x = iter #\|A\| (op x) idx` |
| `reindex h` (l. 1446) | bijective change of variable |
| `reindex_inj h` (l. 1455) | injection on the whole finType |
| `big_morph f f_op f_id` (l. 792) | push `f` inside: `f (\big_(F i)) = \big_(f (F i))` |
| `big_pred0 P_false` (l. 977) | empty predicate -> `idx` |
| `big_seq1` (l. 1778) | singleton seq: `\big_(j <- [:: i]) F = F i` |
| `big_cons`, `big_nil` (l. 943-946) | seq-recursion lemmas (rarely needed by hand) |
| `exchange_big` (l. 2135) | swap two independent bigops |
| `pair_big`, `pair_big_dep` (l. 2113-2118) | nested bigop into a single bigop on pairs |

For ring distributivity over `\sum` (`mathcomp/algebra/ssralg.v`):

```coq
mulr_suml : (\sum_(i <- r | P i) F i) * x = \sum_(i <- r | P i) F i * x
mulr_sumr : x * (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x * F i
big_distrl, big_distrr   (* monoid-level analogues *)
sumrN     : \sum_(...) - F i = - \sum_(...) F i
sumrB     : \sum_(...) (F1 i - F2 i) = \sum F1 - \sum F2
raddf_sum : f additive -> f (\sum_(i <- r | P i) F i) = \sum_(...) f (F i)
rmorph_sum, rmorph_prod  (* ring morphism *)
```

Prefer the **named morphism lemma** (`raddf_sum`, `rmorph_sum`,
`rmorph_prod`, `mulr_sumr`, ...) over a raw `big_morph` invocation
when one exists; reviewers consistently flag this (math-comp PR #682,
"reformulate to most general bigop form": pick the right alias).

### 34.3 The `under eq_bigr` discipline

§29.1 introduced `under`; here is the full bigop story.

```coq
(* WRONG -- per-i tactic, breaks the bigop into a goal-tower *)
apply: eq_bigr => i Pi.
rewrite addrC -raddfN.
...

(* RIGHT *)
under eq_bigr => i Pi do rewrite addrC -raddfN.
```
(math-comp PR #965)

The `do tac` clause hands `tac` to each generated subgoal and leaves
the main goal in compact `\sum_...` form. Without `do`, `under
eq_bigr` opens a sub-proof terminated by `over`:

```coq
under eq_bigr => i Pi.
  rewrite addrC -raddfN.
  by [].   (* or just `over.` *)
```

Localize when there are several bigops:

```coq
(* rewrite only inside the LHS *)
under [LHS]eq_bigr do rewrite mulrC.

(* rewrite only inside the right summand of an outer + *)
under [in X in _ + X]eq_bigr do rewrite mulrC.
```

Same machinery for `eq_bigl` (predicate side), `eq_big` (both),
`eq_big_seq`, and `eq_bigr` chained with `eq_bigl`:

```coq
under eq_big => [i | i Pi].
  by rewrite andbT.        (* predicate-side rewrite *)
by rewrite mulrC.           (* body-side rewrite *)
```

Note: bigop.v line 1166 itself uses `under [LHS]eq_bigr do
rewrite ...` -- it is the canonical idiom even inside the library.

### 34.4 Distributing operations: prefer named lemmas

```coq
(* WRONG -- raw big_morph, fiddly term-mode args *)
rewrite (big_morph f rmorphM rmorph1).

(* RIGHT -- use the alias *)
rewrite rmorph_prod.
```

A cheat-sheet for "push `f` inside the bigop":

| `f` | Distribution lemma |
|-----|--------------------|
| additive | `raddf_sum` |
| ring morphism, on `\sum` | `rmorph_sum` |
| ring morphism, on `\prod` | `rmorph_prod` |
| left-multiply by `x` | `mulr_suml` |
| right-multiply by `x` | `mulr_sumr` |
| outer pair-product | `big_distrlr`, `big_distr_big` |
| arbitrary morphism | `big_morph` (or `big_endo` if same monoid) |

For mathcomp-analysis: `nneseries_split`, `ge0_sume_distrr` and the
`\sum_<oo` family follow the same naming -- the head symbol of the
distributed expression goes first.

### 34.5 Empty / singleton / split idioms

```coq
(* Empty range: result is idx *)
rewrite big_pred0.       (* goal: P =1 xpred0 *)
rewrite big_pred0_eq.    (* literal `false` predicate *)
rewrite big_nil.         (* range is [::] *)
rewrite big_ord0.        (* range is 'I_0 *)
rewrite big_geq.         (* m <= i < n with n <= m *)

(* Singleton: result is F i *)
rewrite big_seq1.
rewrite big_pred1.       (* P =1 pred1 i, finType *)
rewrite big_ord1.        (* 'I_1 *)
rewrite big_nat1.        (* n <= i < n.+1 *)

(* Peel one element on a finType *)
rewrite (bigD1 j) //=.       (* requires P j *)
rewrite (bigD1_seq j) //=.   (* uniq r, j \in r *)
```

A common reviewer-flagged anti-pattern: using `case: r => [|x s]`
to do induction over the seq, when `big_cons`, `big_nil`, or even
better `big_seq` + `bigD1_seq` apply.

### 34.6 Order of summation: Fubini-style

```coq
(* swap two independent bigops *)
rewrite exchange_big /=.

(* dependent variant *)
rewrite (exchange_big_dep xQ).

(* nested -> single bigop on pairs *)
rewrite -pair_big.       (* or pair_big_dep for dependent inner range *)

(* single -> nested by partition *)
rewrite (partition_big p Q) /=.
```

`exchange_big` lives in the `Abelian` section of bigop.v, so it
needs an abelian monoid for the operator. Both inner predicates
must be independent of the outer index; use `exchange_big_dep` when
`Q i j` actually depends on `i`.

For `\sum_<oo` (ereal series) in mathcomp-analysis, the analogous
swap goes by `nneseriesC` and friends -- search for `nneseries`
before reaching for hand-rolled limit swaps.

### 34.7 Naming conventions for bigop lemmas

This rolls back into §10. Two patterns dominate:

1. **Operation-prefixed lemmas** about `\big`:
   `big_<modifier>` -- `big_cat`, `big_split`, `big_seq`,
   `big_mkord`, `big_ord_recl`. Read as "a fact **about** `\big`,
   parameterized by a structural modifier."

2. **Variant-suffixed pairs** for conditional vs. unconditional:
   `big_seq` (no `P`) vs. `big_seq_cond` (preserves `P`),
   `big_mkcond` vs. `big_mkcondr` / `big_mkcondl` (which side gets
   merged), `pair_big` vs. `pair_big_dep`. The `_cond` suffix means
   "stays under an existing predicate"; `_dep` means "the inner
   range / predicate may depend on the outer index"; `_l` / `_r`
   indicate side (math-comp PR #517).

When you introduce a new bigop lemma, follow this scheme. A lemma
named `sum_<X>` is **about a particular expression** that happens to
start with `\sum`; a lemma named `big_<X>` is **about `\big`
itself**. Reviewers will rename across the boundary (math-comp
PR #1000-style feedback).

### 34.8 Common style mistakes flagged in review

A consolidated checklist; see §34.3 and §34.4 for explanations.

```coq
(* WRONG -- rolling foldr by hand *)
elim: r => [|x s IHs] /=; first by rewrite big_nil.
rewrite big_cons; case: ifP => Px; rewrite IHs ?addrA.
(* RIGHT -- a higher-level lemma applies *)
by rewrite (big_morph _ ...) // big_split.

(* WRONG: apply: eq_bigr => i Pi; rewrite ... *)
(* RIGHT: under eq_bigr do rewrite ...        *)  (* PR #965 *)

(* WRONG: \big[+%R/0]_(i < n) f i              *)
(* RIGHT: \sum_(i < n) f i                     *)

(* WRONG: rewrite (big_morph f raddfD raddf0). *)
(* RIGHT: rewrite raddf_sum.                   *)

(* WRONG: rewrite (eq_bigl _ _                 *)
(*           (fun i => orbN (a i))).           *)
(* RIGHT: rewrite (bigID a).                   *)
```

When the predicate gets ugly under a `bigID` or `partition_big`,
clean it with `under eq_bigl do rewrite ...` rather than rebuilding
the bigop term.

### 34.9 Quick decision flow

```
Goal involves \sum / \prod / \big.

  Body needs rewriting under the binder?
    -> under eq_bigr [=> i Pi] do rewrite ...

  Predicate needs rewriting?
    -> under eq_bigl => i do rewrite ...   (or eq_big for both)

  Need to split the range by a property?
    -> rewrite (bigID a)             (binary split)
    -> rewrite (partition_big p Q)   (J-indexed partition)

  Need to peel one element?
    -> rewrite (bigD1 j) //=    (finType, j satisfies P)
    -> rewrite big_ord_recl     (i < n.+1, peel from the left)
    -> rewrite big_ord_recr     (peel from the right)

  Two nested bigops, swap order?
    -> rewrite exchange_big

  Pull a function out?
    -> rewrite raddf_sum / rmorph_sum / mulr_suml / mulr_sumr / ...
       (named alias FIRST; big_morph only as a last resort)

  Reduce to seq concat / map / filter?
    -> big_cat, big_map, big_filter, big_filter_cond
```

Sources: `mathcomp/boot/bigop.v` (file header lines 7-100; lemma
sites cited in 34.2 above); `mathcomp/algebra/ssralg.v` (`mulr_suml`
l. 1076, `mulr_sumr` l. 1080, `rmorph_sum` l. 2324, `rmorph_prod`
l. 2338); math-comp PR #965 (`under` discipline); PR #682
("reformulate to the most general bigop form"); PR #517
(`_l` / `_r` suffixes); MathComp Book chapter 6 ("Big
Operators"). The named-distribution-lemma rule was re-stated in
math-comp/analysis review threads on PRs #1230 and #1340.

---

## 35. HB Factories and Multi-Step Inheritance

§15 covered the surface (`HB.mixin`, `HB.structure`, `HB.instance`,
`HB.lock`). This section covers the next layer: factories, builder
blocks, multiple parents, forgetful inheritance, and the HB
debugging commands. Examples are taken from `mathcomp/boot/nmodule.v`
and `mathcomp/algebra/ssralg.v`.

### 35.1 Factories: what and why

A **mixin** packs operations and axioms; a **factory** is an
alternative interface that HB elaborates into one or more mixins via
a *builders* block. Use a factory when the natural user-facing
packaging differs from the canonical mixin chain.

Typical reasons to introduce a factory:

1. The user provides redundant data (e.g. both `add` and `opp`)
   when the mixin chain would refactor it across two mixins.
2. The user provides data more general than what a mixin expects
   (e.g. `field_axiom` on `ComUnitRing` is repackaged into the
   `UnitRing_isField` mixin plus `ComUnitRing_isIntegral`).
3. The conversion involves non-trivial proof obligations the user
   should not be forced to redo.

Example: declaring a Z-module starting from "raw" data --- the
factory `isZmodule V` lets users build a `zmodType` straight from
`zero`, `opp`, `add` and the four laws, even though the underlying
hierarchy splits these across `isNmodule` (semigroup-with-zero) and
`Nmodule_isZmodule` (the inverse axiom). From `mathcomp/boot/nmodule.v`:

```coq
HB.factory Record isZmodule V of Choice V := {
  zero : V;
  opp  : V -> V;
  add  : V -> V -> V;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add
}.

HB.builders Context V of isZmodule V.
HB.instance Definition _ := isNmodule.Build V addrA addrC add0r.
HB.instance Definition _ := Nmodule_isZmodule.Build V opp addNr.
HB.end.
```

Conventions to notice:

- Factory name is **PascalCase, no `is`/`has` prefix when chained
  from a parent** (e.g. `Zmodule_isPzRing`, `Nmodule_isZmodule`,
  `ComUnitRing_isField`). The leading parent name records the `of`
  context; the trailing capitalised noun records the new structure.
- A factory built from `Choice` only (no algebraic prerequisite)
  uses the bare `is` prefix: `isZmodule`, `isPzRing`, `isPzSemiRing`.
- The `of <Parent> V` clause is the prerequisite *context*, not a
  parent in the structure graph; it tells HB what is already
  assumed when unfolding the builders.

### 35.2 The `HB.builders ... HB.end` block

`HB.builders Context V of FactoryName V.` opens a section in which
`V` is a generic carrier already equipped with everything the
factory provides plus its `of`-context. Inside, you:

- prove auxiliary lemmas (`Lemma`, `Fact`) needed by the downstream
  mixin builders, and
- emit one `HB.instance Definition _ := <Mixin>.Build ...` line per
  mixin you are deriving.

`HB.end` closes the block; HB then registers the factory together
with the mixins it produces. Example with intermediate proofs ---
`Zmodule_isPzRing` derives `Nmodule_isPzSemiRing` after first
proving the missing `mul0r` and `mulr0`:

```coq
HB.builders Context R of Zmodule_isPzRing R.
  Local Notation "1" := one.
  Local Notation "x * y" := (mul x y).
  Lemma mul0r : @left_zero R R 0 mul.
  Proof.
    by move=> x; apply: (addIr (1 * x));
       rewrite -mulrDl !add0r mul1r.
  Qed.
  Lemma mulr0 : @right_zero R R 0 mul.
  Proof.
    by move=> x; apply: (addIr (x * 1));
       rewrite -mulrDr !add0r mulr1.
  Qed.
  HB.instance Definition _ := Nmodule_isPzSemiRing.Build R
    mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.
HB.end.
```

Style points:

- Indent the body two spaces (matches `Section`/`Module` style).
- Local notations (`Local Notation "1" := one.`) inside the block
  are common and harmless --- they vanish at `HB.end`.
- Builder lemmas are *not* exported; they are anonymous proof
  obligations consumed by the elaborator.
- Several `HB.instance Definition _ := ...` lines in sequence are
  fine; HB chains them and discharges the original factory at
  `HB.end`.

### 35.3 Type annotation on builder instances

When the builder produces a mixin whose name overlaps with a
deprecated alias or another builder, give the instance an explicit
type:

```coq
HB.instance Definition _ : ComNzRing_hasMulInverse R :=
  ComNzRing_hasMulInverse.Build R mulVf intro_unit inv_out.
HB.instance Definition _ : ComUnitRing_isField R :=
  ComUnitRing_isField.Build R (fun x x_neq_0 => x_neq_0).
```

(from `ssralg.v`, builders for `ComNzRing_isField`). The annotation
forces HB to register the instance under the intended mixin and
makes the builder readable: a reviewer can scan the LHS to learn
which mixins this factory produces.

### 35.4 Multiple inheritance and diamonds

A structure with multiple parents lists them after `of` separated
by `&`. Example: `Zmodule` inherits from `Nmodule` and from a
`hasOpp`/`BaseAddUMagma` chain that also depends on `Choice`,
giving a diamond rooted at `Choice`:

```coq
#[short(type="zmodType")]
HB.structure Definition Zmodule :=
  {V of BaseZmoduleNmodule_isZmodule V & BaseZmodule V & Nmodule V}.
```

HB resolves the `Choice` diamond automatically. You only need to
intervene when:

1. A new mixin is introduced *after* parents are declared. Use
   `HB.saturate` to retroactively recompute joins (see §35.7).
2. A user-defined alias hides a parent instance --- see §35.5.

Joins should be added **at the leaf level**: declare the new
combined structure together with its mixin in one place, not by
amending parents. From `ssralg.v`:

```coq
#[short(type="pzRingType")]
HB.structure Definition PzRing := { R of PzSemiRing R & Zmodule R }.
```

### 35.5 Forgetful inheritance: aliases vs modules

The deepest gotcha. Forgetful inheritance is HB's principle that a
structure transparently provides every parent's interface. A bare
`Definition T := <expr>.` over a typed term **breaks** that
transparency: HB cannot see through the alias, so canonical
instances declared on the right-hand side do not transfer to `T`.

Reviewer rule (math-comp/analysis PR #786):

> *"This breaks forgetful inheritance. Please provide an alias of Q
> or encapsulate in a module."*

The two safe encapsulations:

```coq
(* OK: Notation alias --- transparent to HB *)
Notation quotient_topology X := (quot_of X) (only parsing).

(* OK: Module wrapper --- HB declares fresh canonical instances
   on the wrapped type *)
Module QuotientTopology.
Section def.
Variable X : topologicalType.
Definition type := quot_of X.
HB.instance Definition _ := Topological.copy type (quot_of X).
End def.
End QuotientTopology.

(* WRONG: bare Definition hides the canonical instances on
   quot_of *)
Definition quotient_topology (X : topologicalType) := quot_of X.
```

Rule of thumb: **never wrap a typed expression in a plain
`Definition` if downstream code expects HB instances on the
result.** Use `Notation`, a `Module` with `HB.instance`, or
`Structure.copy` (e.g. `Topological.copy`, `Zmodule.copy`).

### 35.6 The `#[short(type=...)]` and `#[short(pred=...)]` attributes

The `short` attribute attaches a one-word alias to a long structure
name. Convention (per `mathcomp/boot/nmodule.v`, `ssralg.v`):

```coq
#[short(type="nmodType")]   (* type alias for Nmodule.sort *)
HB.structure Definition Nmodule := {V of isNmodule V & Choice V}.

#[short(type="zmodType")]
HB.structure Definition Zmodule := {V of ... }.

#[short(type="fieldType")]
HB.structure Definition Field :=
  { R of IntegralDomain R & UnitRing_isField R }.
```

- `type=` produces `<name>Type` (lowercase camelCase + `Type`):
  `nmodType`, `zmodType`, `fieldType`, `pzRingType`. This is the
  alias users actually write.
- `pred=` produces a predicate alias (used for sub-structures and
  closure predicates, e.g. `addrPred`, `subringPred`).
- The attribute also opens a `Module <Foo>Exports` block where
  `Bind Scope ring_scope with Foo.sort.` is conventional, followed
  by `HB.export FooExports.` to push it into the user namespace.

### 35.7 HB inheritance graph: debugging commands

| Command | When to use |
|---------|-------------|
| `HB.about <name>.` | Show the mixins/structures attached to a name and the file where each instance was declared. Equivalent to `About` but HB-aware. |
| `HB.howto <T> <Struct>.` | "How do I make `T` a `<Struct>Type`?" Prints sequences of factories that close the gap. Indispensable when stuck. |
| `HB.graph "out.dot".` | Dump the structure hierarchy to Graphviz. Inspect with `xdot` to find missing joins. |
| `HB.locate <name>.` | Show the file and line where any HB-synthesized constant was generated --- mixin builders, projections, exports. |
| `HB.saturate.` | Recompute every join in the current hierarchy. Required after declaring a new mixin or structure that should automatically combine with previously-declared structures. Use sparingly --- it is slow. |
| `#[verbose] HB.instance ...` | Make HB print what it is elaborating. Use `#[log]` or `#[log(raw)]` to print the equivalent Coq commands. |

`HB.saturate` is mainly needed when a parent structure is enriched
*after* its descendants have been declared (e.g. dual-order
instances feeding back into lattice structures). Search for
"`(* TODO: HB.saturate *)`" in `ssralg.v`, `vector.v`, `poly.v` for
real examples.

### 35.8 `HB.lock` revisited

`HB.lock` wraps a definition behind an opaque symbol plus an
unfolding equation, preventing it from unfolding during canonical
instance / unification. The `Unlockable` boilerplate is mandatory
to keep `unlock` rewrites available:

```coq
HB.lock Definition mxrank (F : fieldType) m n (A : 'M_(m, n)) :=
  ...
Canonical mxrank_unlockable := Unlockable mxrank.unlock.
```
(`mathcomp/algebra/mxalgebra.v`)

Lock when:

- The body is a complex match/recursive function whose unfolding
  derails canonical structure inference.
- The definition is a "tag" used to drive resolution and should
  remain rigid (locked predicates, locked operators in instance
  search).

**Anti-pattern**: locking everything. A locked `Definition`
prevents `simpl`, `cbn` and definitional equality from working. Use
`HB.lock` only where computation behaviour matters for inference,
not as a stylistic default.

### 35.9 Naming convention recap

| Construct | Pattern | Example |
|-----------|---------|---------|
| Mixin | `is`/`has` prefix, PascalCase, optionally `<Parent>_is<Child>` | `isNmodule`, `hasOpp`, `Nmodule_isPzSemiRing`, `PzRing_hasCommutativeMul` |
| Factory | PascalCase, often `<Parent>_is<Child>` | `Nmodule_isZmodule`, `Zmodule_isPzRing`, `ComUnitRing_isField`, `isZmodule` |
| Structure | PascalCase, no prefix | `Nmodule`, `Zmodule`, `PzRing`, `Field` |
| Type alias | lowercase camelCase + `Type` | `nmodType`, `zmodType`, `fieldType`, `pzRingType` |
| Predicate alias | lowercase + `Pred` | `addrPred`, `subringPred`, `keyedPred` |
| Exports module | `<Struct>Exports` | `NmoduleExports`, `FieldExports` |

`is`/`has` distinguishes propositional content (`isFoo`) from
operational content (`hasFoo`) at the mixin level. Both appear in
mathcomp; `hasOpp` is the canonical example of `has` (it provides
an operation, no axiom).

### 35.10 Common errors and what they mean

| Error message | Likely cause | Fix |
|---------------|--------------|-----|
| `Could not unify "Foo X" and "Bar Y"` inside `HB.instance` | Missing parent instance for the carrier | Provide it before the `HB.instance` line, or use the right factory whose `of` context matches what is already declared |
| `ambiguous canonical projection` | Diamond not resolved at the join | Add an explicit `HB.instance Definition _ : <CombinedMixin> ... := ...` after declaring both parents |
| `Argument number N is a trailing implicit so must be maximal` | An `Arguments` declaration leaves a final implicit non-maximal | Re-declare with `{X}` (curly) for the trailing arg, e.g. `Arguments foo {T} x : rename.`. See §16, §31 |
| `abbreviation "Foo.Build" is not applied enough` | A factory or mixin's `Build` constructor needs more positional arguments than supplied | Inspect with `HB.about Foo` or `Print Foo.Build`; the `of`-context arguments must be provided explicitly when invoked from outside a builders block |
| Reviewer flag: "this breaks forgetful inheritance" | A `Definition` aliased an HB-equipped type | Replace by `Notation` or wrap in a `Module` (§35.5, analysis PR #786) |
| Reviewer flag: missing `Canonical` / `Coercion` | Legacy code re-exports an HB structure but forgot the canonical declaration | Add `Canonical` next to the structure export (math-comp PR #406) |

### 35.11 Common pitfalls

- **Adding redundant factories.** math-comp PR #1586:
  introduce a factory only when no existing chain expresses the
  same packaging. `HB.howto` already finds non-trivial chains; if
  it succeeds, the factory is redundant.
- **Over-using `@` in `Build` calls.** Prefer
  `Mixin.Build T h1 h2 h3` over
  `@Mixin.Build T arg1 arg2 ... h1 h2 h3` --- HB infers the
  `of`-context positions. Use `@` only when one of the inferred
  positions truly is ambiguous (math-comp PRs #41, #270).
- **Forgetting to declare `Canonical` / `Coercion` in legacy
  exports.** When porting non-HB code, the equivalent of HB's
  automatic export is a manual `Canonical` next to the structure
  (math-comp PR #406).
- **Putting reusable lemmas inside `HB.builders`.** A builders
  block is anonymous; lemmas proved there are not callable from
  outside. If a lemma has independent value, factor it out *before*
  `HB.builders` and call it from inside.
- **Locking everything.** `HB.lock` is for inference control, not
  for general "I want this to be opaque". Use it sparingly (§35.8).
- **Bare `Definition` aliases over typed expressions.** Always use
  `Notation`, `Module`, or `<Struct>.copy` (analysis
  PR #786, §35.5).
- **Declaring a join after the fact and forgetting `HB.saturate`.**
  Symptoms: a structure is "missing" an instance even though all
  the mixins are present. Run `HB.howto` to confirm, then add an
  explicit join or call `HB.saturate`.

### 35.12 Sources

- [HB README](https://github.com/math-comp/hierarchy-builder/blob/master/README.md)
- [HB Changelog](https://github.com/math-comp/hierarchy-builder/blob/master/Changelog.md)
- [HB FSCD2020 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol167-fscd2020/LIPIcs.FSCD.2020.34/LIPIcs.FSCD.2020.34.pdf)
- math-comp source files referenced above:
  `mathcomp/boot/nmodule.v` (`isZmodule`, `Nmodule_isZmodule`),
  `mathcomp/algebra/ssralg.v` (`Zmodule_isPzRing`,
  `ComUnitRing_isField`, `ComNzRing_isField`),
  `mathcomp/algebra/mxalgebra.v` (`HB.lock` patterns),
  `mathcomp/order/order.v` (`HB.saturate` usage)
- [analysis PR #786 --- forgetful inheritance / aliases](https://github.com/math-comp/analysis/pull/786)
- [math-comp PR #406 --- missing `Canonical`/`Coercion`](https://github.com/math-comp/math-comp/pull/406)
- [math-comp PR #1586 --- redundant factories](https://github.com/math-comp/math-comp/pull/1586)
- [Rocq Zulip #Hierarchy-Builder](https://rocq-prover.zulipchat.com/#narrow/channel/237977-Hierarchy-Builder)

---

## 36. Choice and Decidability

Mathcomp layers logical content as a chain of type structures. Each
layer adds machinery downstream lemmas require; the cardinal
principle is **ask for the weakest level the lemma actually uses**.
mathcomp-analysis adds a small axiom set in
`mathcomp/classical/boolp.v` to bridge classical reasoning with
boolean reflection.

### 36.1 The hierarchy in one diagram

```text
        Type  (bare types, only Leibniz =)
          |
          v   + decidable equality (eq_op : T -> T -> bool, eqP)
       eqType  == Equality.type           (mathcomp/boot/eqtype.v)
          |
          v   + xchoose : informative choice
     choiceType == Choice.type            (mathcomp/boot/choice.v)
          |
          v   + pickle / unpickle pair (bijection with subset of nat)
     countType == Countable.type          (mathcomp/boot/choice.v)
          |
          v   + finite enumeration `enum T : seq T`
      finType  == Finite.type             (mathcomp/boot/fintype.v)

     subType / subEqType / subChoice / subFinite : sub-structure
     transport along a predicate `P : pred T`.
```

The HB declarations (`mathcomp/boot/eqtype.v`, `choice.v`,
`fintype.v`) chain the factories so `x : finType` automatically
exposes `x : choiceType`, `eqType`, ...:

```coq
HB.structure Definition Equality  := { T of hasDecEq T }.
HB.structure Definition Choice    := { T of hasChoice T & hasDecEq T }.
HB.structure Definition Countable := { T of Choice T & Choice_isCountable T }.
HB.structure Definition Finite    := { T of isFinite T & Countable T }.
```

What each level grants:

| Level        | Key API                            | Typical use         |
|--------------|------------------------------------|---------------------|
| `eqType`     | `==`, `!=`, `eqP`, `eqVneq`        | branch on equality  |
| `choiceType` | `xchoose`, `xchooseP`              | pick a witness      |
| `countType`  | `pickle`, `unpickle`, `pickleK`    | enumerate / encode  |
| `finType`    | `enum T`, `\sum_(x:T)`, `#|T|`     | finite reasoning    |
| `subType P`  | `\val`, `Sub`, `valK`              | `{x : T | P x}`     |

### 36.2 Choosing the right level

Bumping the level "to be safe" closes off generic uses.

```coq
(* WRONG -- finType is overkill for a comparison lemma *)
Lemma foo_eq (T : finType) (x y : T) : (x == y) = (y == x).

(* RIGHT *)
Lemma foo_eq (T : eqType) (x y : T) : (x == y) = (y == x).
Proof. by rewrite eq_sym. Qed.
```

Heuristics:

- `eqType` -- only `==` / `!=` / `eqVneq` are used.
- `choiceType` -- extracting a witness via `xchoose` from `exists x, P x`.
- `countType` -- enumerating the carrier or coding into `nat`.
- `finType` -- finiteness is **mathematically essential** (`#|T|`,
  bigop over the whole type). Convenience does not count.

For analysis: most measure-theoretic / topological types do not need
this hierarchy at all. `pointedType`, `topologicalType` etc. bring
their own typeclasses; do not add `eqType` unless a lemma in the
proof body asks for it.

### 36.3 `reflect` and the decidable-equality bridge

`eq_op` gives boolean equality on `eqType`; `eqP : reflect (x = y)
(x == y)` is the bridging reflection. Live in `bool` and rewrite to
`Prop` only at the boundary.

Standard view chains (see also §27.7, §28.1):

```coq
move=> /eqP ->.                  (* bool -> Leibniz, rewrite *)
apply/eqP.                       (* Leibniz -> bool *)
case: eqVneq => [-> | xy_neq].   (* branch on equality *)
have [<-|xy_neq] := eqVneq x y.  (* same, named branch *)
```

Fall back to Leibniz `=` only when the type is not an `eqType`, or
in top-level `_ = _` lemma statements (the user calls `apply/eqP` on
the `==` side).

### 36.4 Classical extensions: `boolp` and `asbool`

mathcomp-analysis lives one axiom layer above mathcomp.
`mathcomp/classical/boolp.v` declares **exactly three** axioms:

```coq
Axiom functional_extensionality_dep : ...        (* funext *)
Axiom propositional_extensionality  : ...        (* propext *)
Axiom constructive_indefinite_description : ...  (* cid *)
```

Excluded middle, `pselect`, `boolp.classic`, `lem` are **derived**
from these via Diaconescu (`Theorem EM` in `boolp.v`).
`Print Assumptions` on an analysis proof should list these three and
nothing else (modulo `Eqdep.Eq_rect_eq.eq_rect_eq` shims).

The classical projection from `Prop` to `bool`:

```coq
Definition asbool (P : Prop) := if pselect P then true else false.
Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolP  (P : Prop) : reflect P `[< P >].
Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[< P >]).
Lemma asbool_or  {P Q} : `[< P \/ Q >] = `[< P >] || `[< Q >].
Lemma asbool_and {P Q} : `[< P /\ Q >] = `[< P >] && `[< Q >].
```

Use `asbool` when an arbitrary `Prop` must enter a boolean-shaped API
(`pred T`, a `bool`-valued recursor). Avoid it when the property is
constructively decidable, when you only case-analyze (use `pselect`,
§36.5), or when `Prop` only appears because of a stray `is_true`.

CHANGELOG note: any new `Axiom` beyond the `boolp` set must be
flagged in `CHANGELOG_UNRELEASED.md` under `### Infrastructure`.
Reviewers block PRs that silently add
axioms.

### 36.5 `pselect` and `cid`

```coq
Lemma pselect (P : Prop) : { P } + { ~ P }.
Notation cid := constructive_indefinite_description.
Lemma cid2 (A : Type) (P Q : A -> Prop) :
  (exists2 x : A, P x & Q x) -> { x : A | P x & Q x }.
```

`pselect` is the classical informative case-split; `cid` / `cid2`
extract a witness from `exists`. Idiomatic invocations:

```coq
have [hP | hnP] := pselect P.    (* RIGHT -- named branches *)
case: (pselect P) => [hP | hnP]. (* RIGHT -- inline *)
destruct (pselect P) as [...].   (* WRONG -- not SSReflect style *)
```

Witness extraction:

```coq
Definition pick_x (eP : exists x : T, P x) : T := projT1 (cid eP).
Lemma pick_xP eP : P (pick_x eP). Proof. exact: projT2 (cid eP). Qed.
```

`projT1 (cid _)` is the standard pattern; do not unfold it.

### 36.6 `{posnum R}`, `{nonneg R}`: bundled positivity

Defined in `mathcomp/reals/signed.v`. When a lemma needs `0 < x` (or
`0 <= x`), prefer the bundled form:

```coq
(* WRONG -- two separate arguments *)
Lemma foo (R : realType) (x : R) (xpos : 0 < x) : ... .

(* RIGHT -- bundled, composes with `_%:pos`, `_%:num` *)
Lemma foo (R : realType) (x : {posnum R}) : ... .
```

Convert a hypothesis at proof time with `posnumP` (dual: `nonnegP`):

```coq
Lemma bar (R : realType) (x : R) : 0 < x -> P x.
Proof. by case/posnumP=> {}x; ...  (* x : {posnum R} now *) Qed.
```

Bundling wins (analysis PRs #21, #786) because
`(x%:num + y%:num)%:pos` is auto-inferred positive, side conditions
ride along the type, and forgetful-inheritance aliasing is avoided.

### 36.7 `Decidable` predicates: `bool` vs `{P}+{~P}` vs `Prop`

| Form              | When to use                                      |
|-------------------|--------------------------------------------------|
| `b : bool`        | decidable, you compute with it                   |
| `{P} + {~P}`      | informative case-split at term level             |
| `P : Prop`+`pselect` | genuinely classical; case-analyze only       |
| `` `[< P >] `` : bool  | hand a bool to a `pred T` API from a `Prop` |

Rule of thumb: do not parametrize a lemma over `decidable P` if you
can give a stronger `pred T` argument and use `eqP`/`asboolP` once.

### 36.8 Common style mistakes

Repeatedly flagged in upstream review:

1. **`finType` when `eqType` suffices** (math-comp PR #351).
2. **Re-proving `xchoose`-style lemmas** or rolling a custom choice
   when an HB instance already exists.
3. **Mixing `=` and `==`** on an `eqType` (PR #351). Prefer
   `case: eqVneq` over `case: (x =P y)` plus manual rewriting.
4. **Using `Coq.Logic.Classical_Prop`** / `Classical_Pred_Type` /
   `ClassicalDescription`: always go through `boolp.classic`,
   `boolp.pselect`, `boolp.lem`. Mixing breaks `Print Assumptions`.
5. **New axioms not declared** in `CHANGELOG_UNRELEASED.md ###
   Infrastructure`. Reviewers block.
6. **`asbool` chains where reflection suffices**:
   `apply/asboolP; apply/asboolP` is a smell.
7. **Fully-qualified `boolp.asbool`** -- add `Import boolp.` (§23,
   PR #1244).
8. **`rewrite /xchoose`** -- `xchoose` is locked behind `xchooseP`.

### 36.9 `eqP` view chain idioms (cross-ref §27.7, §28)

```coq
move=> /eqP ->.            (* rewrite-by-equation *)
move=> /eqP <-.            (* right-to-left *)
apply/eqP/some_other_view. (* compose views *)
case: eqP => [-> | hne].   (* branch + rewrite equal case *)
move/eqP in H.             (* turn H : x == y into x = y *)
rewrite (eqP H).           (* same, in goal *)
```

### 36.10 Search and discoverability

```coq
Search (?x == ?y) "sym".  (* eq_sym, eqP *)
Search {posnum _}.        (* posnum-bundled lemmas *)
Search (reflect _ _).     (* available reflect bridges *)
Search "xchoose".         (* witness introduction *)
Search "pselect".         (* classical case-split *)
```

### 36.11 Common pitfalls

- **`Print Assumptions` should list at most** the three `boolp`
  axioms (`functional_extensionality_dep`,
  `propositional_extensionality`,
  `constructive_indefinite_description`). Anything else
  (`Classical_Prop.classic`, the stdlib `proof_irrelevance` --
  *not* `boolp.Prop_irrelevance`, which is derived) is a regression.
- **`gen_eqMixin` / `gen_choiceMixin`** in `boolp.v` build
  `eqType` / `choiceType` from `cid`; they bake classical axioms
  into the structure. Prefer constructive `hasDecEq.Build` /
  `Choice_isCountable.Build` whenever the carrier admits one.
- **`{classic T}` / `{eclassic T}`** (boolp.v) wrap a bare `Type`
  with a classical `eqType` / `choiceType` via `gen_eqMixin`. Use
  at definition time; never at use sites.
- **HB factory vs mixin**: use `isCountable.Build` (factory, chains
  Choice + Equality) to declare a fresh `countType`, not
  `Choice_isCountable.Build` (mixin) directly.
- **`subType` carriers** of a `choiceType T` are `choiceType`
  automatically: `HB.instance Definition _ := [Choice of S by <:].`
  Do not re-prove choice.
- **Avoid `Coq.Init.Logic.Decidable`**: `Decidable.decidable P` is
  `P \/ ~ P`, *not* informative. Use mathcomp's `{P}+{~P}` or `bool`.

---

## 37. Search Discipline

A lemma is only as useful as it is findable. Mathcomp culture treats
`Search` as the primary library-navigation tool: every statement is
named, ordered, and notated so that future searchers can rediscover
it from any salient symbol. This section consolidates the rules
implicit in the upstream review threads cited in §10, §12, §17, §32.

### 37.1 The `Search` commands every contributor uses

| Form | Purpose |
|------|---------|
| `Search "_eq0".` | by name substring |
| `Search (?x + ?y) (?x = ?y).` | by term pattern (multiple constraints conjunctive) |
| `Search inside Order.TotalTheory.` | within a module |
| `Search outside ssrnat.` | excluding a module |
| `Search -is_true _ (?x <= ?y).` | exclude a head/wrapper |
| `Search "_le" (?x + _).` then `Search "_lt" (?x + _).` | (Rocq's `Search` does not support disjunction of name patterns; run two queries) |

Lemmas are filtered by the `Search Blacklist` table (Rocq vernacular).
mathcomp pre-populates it; e.g. `mathcomp/classical/functions.v` opens
with:

```coq
Add Search Blacklist "__canonical__".
Add Search Blacklist "__functions_".
Add Search Blacklist "_factory_".
Add Search Blacklist "_mixin_".
```

The convention extends to user-written helpers via the `_subdef` and
`_subproof` suffixes (analysis PR #403): everything
suffixed that way is considered HB- or auto-generated boilerplate
and is filtered out of search results.

### 37.2 The head-symbol rule (LHS for equations)

The mathcomp CONTRIBUTING.md says the main symbol is "generally the
head symbol of the right-hand side of an equation or the head symbol
of a theorem". In practice, for a *rewrite-oriented* equation
`LHS = RHS`, reviewers consistently ask for the head of the **LHS**,
because that is what users have in their goal when they reach for
`rewrite`.

Example (analysis PR #1000, "Minkowski"):

```coq
(* LHS is `'N_r%:E[f] `^ r`, head symbol is powR *)
Lemma powR_Lnorm f r : r != 0%R ->
  'N_r%:E[f] `^ r = \int[mu]_x (`| f x | `^ r)%:E.
```

The original draft was `Lnorm_powR_K`. A reviewer's note:

> "At least, `powR_Lnorm` would be better (head symbol goes first)."

Note this differs from §10's literal wording ("head of the RHS").
The operative rule, as practiced, is:

- **Equational rewrite lemmas** (the typical case): name after the
  head of the LHS — the user finds it from the term they want to
  rewrite.
- **Equational definitional unfolds** (`fooE : foo a b = ...`): the
  name still leads with the symbol the user starts from (`foo`).
- **Theorem lemmas without a clear LHS**: name after the main
  symbol of the conclusion.

### 37.3 Make every salient symbol searchable

A lemma about `f \o g` involving both `f` and `g` should be
findable from either. Two techniques:

1. **Compound names** mention every salient symbol:
   `cat_take_drop : take n s ++ drop n s = s` is reachable via
   `Search cat`, `Search take`, and `Search drop`.

2. **`mainSymbol_unaryPredicate`** (§12) for property lemmas:
   `g_monotone_monotone`, not `monotone_g_monotone`. The head
   `g` is what `Search g` matches.

`Search` matches name *substrings*, so `Search "_take_drop"` and
`Search "cat_"` both surface `cat_take_drop`. Reviewers reject
names that hide the head behind a wrapper.

### 37.4 Hide internals with `_subdef` / `_subproof`

Internal helpers should be tagged so they don't pollute the global
result list:

```coq
(* Good: the helper is invisible to Search; the user-facing alias is. *)
Definition mule_subdef : \bar R -> \bar R -> \bar R := ...
Definition mule := nosimpl mule_subdef.

Fact addq_subproof q1 q2 : ratK (addq_subdef q1 q2) = ...

(* Bad: leaks an HB-internal helper into Search. *)
Lemma Internal_addrA : ...
```

Three distinct tools, same goal:

- Name the helper `*_subdef` or `*_subproof` — it falls under the
  default mathcomp Search blacklist.
- Use `Fact` rather than `Lemma` for instance-only auxiliaries
  (§18); reviewers understand `Fact` as "do not cite this".
- Never expose a name containing `Internal` (analysis
  PR #469: *"Never use a lemma called `Internal`"*). The pattern
  leaks an HB-internal name and breaks the abstraction.

### 37.5 Side-condition placement

`Search` matches against the *whole* type of a lemma, including
preconditions, but the discoverability heuristic is:

```coq
(* Good: searchable head appears in the conclusion. *)
Lemma divnK m n : (n %| m)%N -> n * (m %/ n) = m.

(* Less good: precondition buries the salient symbol. *)
Lemma divnK_alt m n : n * (m %/ n) = m -> (n %| m)%N.
```

Order preconditions so the head symbol the user is searching for
appears in the conclusion (or as the *last* informative argument).
A user with goal `n * (m %/ n)` searches for that pattern; the
divisibility precondition is then surfaced as side information.

### 37.6 `reflect` over `iff` for booleans

A `reflect (P x) b` statement is searchable on **both** sides:
`Search b` and `Search P` will both find it. An `<->`
statement loses the boolean side from term-pattern searches.

```coq
(* Searchable as andP via both `&&` and `/\`. *)
Lemma andP : reflect (a /\ b) (a && b).

(* Same content, but `Search (_ && _)` will not match this `iff`. *)
Lemma andP_iff : a /\ b <-> a && b = true.
```

When both forms exist, mathcomp prefers the `reflect` form and
suffix `P` (§11).

### 37.7 `{in D, ...}`, `{homo ...}`, `{mono ...}`

These notations are *abbreviations* that expand to quantified
statements; the wrapping symbol (`prop_in1`, `homomorphism_2`,
`monomorphism_2`) is what `Search` actually sees on the lemma's
type.

```coq
Lemma le_contract : {mono contract : x y / (x <= y)%O}.
(* Search "_mono_" finds it; Search "<=%O" finds it via the body. *)

Lemma ler_inD x : {in D, forall y, x + y <= ub}.
(* Search prop_in1 finds the family; Search "_inD" finds this lemma. *)
```

Two consequences:

- `Search {homo _ : _ _ / _}` and `Search {mono _ : _ _ / _}` work.
- The relation `R` and the domain `D` remain searchable through
  the unfolded body — do *not* hide them behind a one-shot
  abbreviation.

Names should follow §12: the head of the unfolded statement (for
`homo`) or of the LHS of the equality (for `mono`); never name a
lemma `mono_*` or `homo_*`.

### 37.8 Typeclass / HB method projections

HB-generated names follow `Module.method`, found via
`Search inside Module`. Always add a short user-facing alias so
the canonical name is searchable in flat form:

```coq
(* HB exposes AddRing.add; users want bare `add`. *)
Notation add := AddRing.add.
```

`Hint Mode` constrains typeclass resolution so unification does not
loop on flexible heads. Example from `mathcomp/classical/filter.v`:

```coq
Global Hint Mode Filter - ! : typeclass_instances.
Global Hint Mode ProperFilter - ! : typeclass_instances.
```

`!` requires a head constructor on that argument before resolution
fires; use `Hint Mode` whenever instance lookup would otherwise loop.

### 37.9 `Hint Resolve` discipline

`Hint Resolve lem : core` adds `lem` to the `core` HintDb, used by
`done` and `by`. Two strict rules (analysis PR #1563):

- **Never use `by` inside hints registered to `core`.** ssreflect's
  `exact` calls the same machinery as `by []` and `done`, which
  in turn re-enters `core` — *"`by` is strictly forbidden in `core`
  HintDb (causes loops)"*. Use `solve` if you need a closer.
- **Prefer a dedicated HintDb** over `core` for deep automation;
  reserve `core` for one-step facts (`Hint Resolve lerr : core`).

### 37.10 Common `Search`-hostile mistakes reviewers flag

| Mistake | Fix | Source |
|---------|-----|--------|
| Generic name (`conjugate`) | Domain-prefix it (`hoelder_conjugate`) | analysis PR #1624 |
| Head buried (`Lnorm_powR_K`) | Lead with the LHS head (`powR_Lnorm`) | analysis PR #1000 |
| Internal helper exposed (`Internal_*`) | Rename to `*_subdef` / `*_subproof` | analysis PRs #469, #403 |
| `iff` where `reflect` would do | Use `reflect _ _` form, suffix `P` | §11, §32 |
| Naked `Module.x` user-side | Add `Notation x := Module.x.` | §23 |
| `by` in a `core` `Hint Resolve` | `solve` or use a non-`core` db | analysis PR #1563 |
| Missing dual / sided lemma | Add the symmetric variant | analysis PRs #514, #535, #780 |

### 37.11 Search recipe (cheat sheet)

When *looking for* a lemma about `f a + g a`:

```coq
(* 1. Pattern over the whole expression. *)
Search (?h (?u + ?v)).

(* 2. Expected suffix (additivity / morphism). *)
Search "_addD" "_D".

(* 3. Specialise to the head. *)
Search raddfD.

(* 4. Restrict to the relevant module. *)
Search (_ + _) inside GRing.Theory.

(* 5. Strip wrappers that match too much. *)
Search (_ + _) -is_true -reflect.
```

When *writing* a lemma so it ANSWERS such searches:

1. Lead with the head of the LHS (§37.2).
2. Mention every salient secondary symbol in the suffix list
   (§37.3, §11 abbreviation table).
3. Wrap quantifications in `{in D, ...}` / `{homo ...}` /
   `{mono ...}` rather than ad-hoc `forall` so the framework
   notation is searchable (§37.7).
4. Provide a `Notation` alias for any HB-namespaced primitive
   the user is meant to invoke (§37.8).
5. Tag any helper not meant for citation as `_subdef` /
   `_subproof` (§37.4).
6. Add the dual lemma in the same commit (§21, item 23).

If you cannot recover your own lemma with one `Search` invocation
two weeks after writing it, the name is wrong.

---

---

## Reviewer Checklist

When reviewing Rocq code against mathcomp-analysis conventions, check:

**Structural**
- [ ] All lines <= 80 characters
- [ ] File starts with copyright line, then imports in correct order
- [ ] `(**md ... *)` header documents all new definitions
- [ ] `Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.` present
- [ ] All `Open Scope` are `Local Open Scope`
- [ ] Sections use `Context`/`Variable`/`Implicit Types` appropriately
- [ ] No fully-qualified module names (`order.Order.X`, `boolp.X`,
  `filter.X`) in source -- add the relevant `Import` (Section 23)

**Naming**
- [ ] Lemma names follow `mainSymbol_suffixes` convention
- [ ] Abbreviation suffixes match the standard table
- [ ] Hypotheses have meaningful names (not `H`, `H'`)
- [ ] No overly generic names (be specific and discoverable)
- [ ] For analysis: convergence uses `cvg`/`lim`/`is_cvg` correctly
- [ ] For analysis: composite vs applied function naming correct

**Proof scripts**
- [ ] Proof lines closing goals start with `by` or `exact:`
  (Section 26)
- [ ] No `Focus` or `{}` in proofs
- [ ] Tactic spacing: `move=>`, `apply/`, `apply:` (no space);
  `rewrite /def` (space)
- [ ] No numerical occurrence selectors in proofs
- [ ] Bullets use `-`, `+`, `*` hierarchy
- [ ] Indentation: 2 spaces for branches, `last first` to keep main
  flow at outer level (Section 27.8)

**Concision (maintainer feedback)**
- [ ] No useless arguments to `exact:` / `apply:` (Section 22.2)
- [ ] No useless scope delimiters (`%R`, `%E`) inside an open scope
  (Section 22.3)
- [ ] No useless type annotations like `[the X of T]` when `T`
  resolves canonically (Section 24.1)
- [ ] No `@` unless disambiguation requires it (Section 25)
- [ ] No `measure_display` or other display arguments passed
  explicitly when inferable (Section 24.4)
- [ ] No hypothesis named just to be consumed once -- use `->`, `<-`,
  `?`, `_` (Section 27)
- [ ] No bookkeeping line that could be `by [].` or `done.`
  (Section 22.1)
- [ ] No `have -> : E by [].` followed by `by [].` -- the rewrite was
  redundant (Section 22.1)

**HB and metadata**
- [ ] `HB.instance Definition _ := ...` pattern used correctly
- [ ] `Arguments` re-declared after section `End` when needed
- [ ] Auxiliary lemmas use `Local`/`Let`/`Fact`; main results do not
- [ ] Operators have spaces: `n * m` not `n*m`

---

## Upstream review focus areas

For context on what upstream review tends to enforce:

- Naming conventions, changelog, code organization, deprecation,
  header documentation
- Architecture, naming, redundancy elimination, type hierarchy
  design, HB patterns
- Style (spacing, imports), deprecation mechanics, changelog accuracy
- Line length, proof simplification, section organization
- Mathematical generalization, factoring intermediate results,
  documentation quality

---

## Sources

- [math-comp/math-comp CONTRIBUTING.md](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md)
- [math-comp/analysis CONTRIBUTING.md](https://github.com/math-comp/analysis/blob/master/CONTRIBUTING.md)
- [MathComp Wiki: How to Document](https://github.com/math-comp/math-comp/wiki/How-to-document)
- [Mathematical Components Book](https://math-comp.github.io/mcb/)
- PR review comments from math-comp/analysis (PRs #677, #754, #817,
  #821, #942, #969, #971, #984, #1000, #1008, #1015, #1108, #1222,
  #1230, #1289, #1340, #1351, #1366, #1368, #1435, #1624, #1679,
  #1825, #1827)
- PR review comments from math-comp/math-comp (PRs #1398, #1505,
  #1547, #1551, #1552, #1557, #1563)
- [Zulip: math-comp users](https://rocq-prover.zulipchat.com/#narrow/channel/237664-math-comp-users)
- [Zulip: math-comp analysis](https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis)
- [Zulip: Hierarchy Builder](https://rocq-prover.zulipchat.com/#narrow/channel/237977-Hierarchy-Builder)
- [GitHub Issue #436: Numerical occurrence selectors](https://github.com/math-comp/math-comp/issues/436)
- [GitHub Issue #508: mem_imset/mem_map naming](https://github.com/math-comp/math-comp/issues/508)
- [GitHub Issue #1093: leq_subr naming](https://github.com/math-comp/math-comp/issues/1093)
- [Hierarchy Builder README](https://github.com/math-comp/hierarchy-builder/blob/master/README.md)
- [HB FSCD2020 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol167-fscd2020/LIPIcs.FSCD.2020.34/LIPIcs.FSCD.2020.34.pdf)
- [SSReflect proof language reference](https://rocq-prover.org/doc/master/refman/proof-engine/ssreflect-proof-language.html)
- [analysis CHANGELOG](https://github.com/math-comp/analysis/blob/master/CHANGELOG.md)
- [math-comp CHANGELOG](https://github.com/math-comp/math-comp/blob/master/CHANGELOG.md)
- Section 33 above lists the specific PR reviews used to construct
  Sections 22-32.
- [GitHub Issue #1370: rpred discoverability](https://github.com/math-comp/math-comp/issues/1370)
