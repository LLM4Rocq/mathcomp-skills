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
49. nat and seq Idioms (ssrnat, seq) — *in `domains/49_nat_seq.md`*

**Migration (book / mathcomp 1.x → 2.5):**

48. [Coming from the MathComp Book](#48-coming-from-the-mathcomp-book-mathcomp-1x--coq-8--mathcomp-25--hb--rocq-9)

Cross-reference rule: `(§N)` with N ≤ 37 or N = 48 lives in this file;
38-47 and 49 live in `domains/<N>_*.md`.

---

## 0. Quick Reference: Top 25 Rules

A condensed cheat sheet of the rules most likely to surface in
mathcomp-analysis review. Each item links to the full rule below.

| # | Rule | Section |
|---|------|---------|
|  1 | Lines must be <= 80 chars | 1 |
|  2 | `From HB Require Import structures.` first, then `From mathcomp Require Import all_boot …` (not deprecated `all_ssreflect`) | 3 |
|  3 | Always `Local Open Scope`, never plain `Open Scope` | 6 |
|  4 | Goal-closing tactic lines must start with `by` (or be `exact:`) -- bullets do not check closure under mathcomp | 26, 26.5 |
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

(* 2. MathComp base libraries (mathcomp >= 2.5; see the table below) *)
From mathcomp Require Import all_boot all_order.
From mathcomp Require Import ssralg ssrnum ssrint.   (* or all_algebra *)

(* 3. MathComp analysis libraries, in dependency order *)
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.

(* 4. Project-local imports *)
(* From MyProject Require Import my_module other_module. *)
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
  packages.
- **`all_ssreflect` is deprecated since mathcomp 2.5.0.** It is now a
  shim for `all_boot` + `preorder` + `order`, so a mechanical swap to
  `all_boot` alone can lose order lemmas and notations. Write
  `all_boot all_order`.
- When editing an upstream file, keep its local import style.
- Suppress warnings when needed:
  `#[warning="-warn-library-file-internal-analysis"]`

### Which Umbrella Line?

| Situation | Import | Why |
|---|---|---|
| New code, mathcomp ≥ 2.5 | `all_boot` (+ `all_order` if order/preorder lemmas or notations are used) | `boot/` holds the former `ssreflect/` files |
| Upstream **analysis ≥ 1.16** PR, or a project that must build on mathcomp 2.4 **and** already depends on analysis ≥ 1.16 | follow upstream: `all_ssreflect_compat` | shipped by mathcomp-classical 1.16 (`classical/all_ssreflect_compat.v`); its header says to switch to `all_boot`/`all_order` when requiring MC ≥ 2.5.0; absent from core and from analysis ≤ 1.15 |
| File that must build on mathcomp 2.4 **without** analysis | `all_ssreflect` | 2.4 has no `all_boot`; on 2.5 it prints `[deprecated-library-file-since-mathcomp-2.5.0]` (`errors.md` §9) |

```coq
(* WRONG: all_ssreflect -> all_boot alone drops order/preorder *)
From mathcomp Require Import all_boot.
Fail Import Order.TTheory.        (* order.v is not loaded *)

(* RIGHT *)
From mathcomp Require Import all_order.
Import Order.TTheory.
Check le_trans.
```

### Umbrella Files by Tier

The book's tiers (MCB Introduction) are `all_ssreflect`, `all_fingroup`,
`all_algebra`, `all_solvable`, `all_field`, `all_character`. Installed
umbrellas (mathcomp 2.5 + analysis):

| Umbrella | Main contents |
|---|---|
| `all_boot` | all of `boot/`: `ssreflect ssrbool ssrfun eqtype ssrnat seq choice monoid nmodule path div fintype fingraph tuple finfun bigop prime finset binomial generic_quotient ssrAC` |
| `all_order` | `order` (which re-exports `preorder`), both in `order/` |
| `all_algebra` | `ssralg ssrnum ssrint rat intdiv poly polydiv matrix mxalgebra mxpoly vector zmodp interval fraction …`; not `interval_inference` (import it explicitly) |
| `all_fingroup` | `fingroup perm morphism quotient action automorphism gproduct presentation` |
| `all_solvable` | `cyclic abelian nilpotent pgroup sylow hall frobenius commutator …` |
| `all_field` | `fieldext galois separable finfield closed_field cyclotomic algC …` |
| `all_real_closed` | `polyrcf qe_rcf realalg complex …` |
| `all_classical`, `all_reals`, `all_analysis` | analysis layers (`boolp classical_sets functions …`; `reals constructive_ereal …`; `topology normedtype sequences measure lebesgue_integral …`) |

- There is **no `all_character` in core**: character theory is the
  separate mathcomp-character package.
- The book's `ssreflect/` files moved to `boot/` (`boot/ssrnat.v`,
  `boot/seq.v`, …); `ssreflect/` now holds only the deprecated
  `all_ssreflect.v`. Grep and cite `boot/`.
- Deprecation warning row: `errors.md` §9. Book → 2.5 name map: §48.

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
(*   definition == prose explanation of the definition                        *)
(*     notation == prose explanation, scope info nearby                       *)
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

Immediately after the documentation block, every file has **three
flags**, then an `Import` line whose content depends on the tier:

```coq
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* algebra-level files additionally: *)
(* From mathcomp Require Import all_order all_algebra. *)
(* Import Order.TTheory GRing.Theory Num.Def Num.Theory. *)
```

The three flags are always present, in that order. They are unchanged
in 2.5: the library's theory files set them (e.g.
`boot/ssrnat.v:112`; 190 installed files).

**What the flags do**

| Flag | Effect |
|---|---|
| `Set Implicit Arguments` | In every `Definition`/`Lemma`/`Record` you declare, parameters inferable from later arguments or the type become implicit; pass them with `@f` or `f (x := _)` (§25) |
| `Unset Strict Implicit` | Also makes *non-strict* parameters implicit: those inferable only through a position that reduction could erase (`n` in `'I_(n + 1)`) |
| `Unset Printing Implicit Defensive` | Goals no longer show non-strict implicits defensively (`h2 (n:=2) x` prints `h2 x`), so they read like the library and the book |

Without the first two flags your definitions keep explicit parameters,
callers must write `foo _ x`, and the `@`/`Arguments` reasoning of
§16, §25 and §31 no longer matches upstream.

```coq
From mathcomp Require Import all_boot.

Set Implicit Arguments.          (* inferable parameters become implicit *)
Definition h1 (n : nat) (x : 'I_(n + 1)) := val x.
About h1.                        (* Arguments h1 n x: n is non-strict *)
Unset Strict Implicit.           (* non-strict ones become implicit too *)
Definition h2 (n : nat) (x : 'I_(n + 1)) := val x.
About h2.                        (* Arguments h2 [n] x *)
Check forall x : 'I_(2 + 1), h2 x = 0.   (* prints h2 (n:=2) x = 0 *)
Unset Printing Implicit Defensive.
Check forall x : 'I_(2 + 1), h2 x = 0.   (* prints h2 x = 0 *)
```

**The `Import` line follows the tier.** Each module must be loaded
first; a boot-only file has no `Import` line.

| Loaded | Add to the `Import` line |
|---|---|
| `all_boot` only | nothing |
| `all_order` / `order` | `Order.TTheory` |
| `ssralg` | `GRing.Theory` |
| `ssrnum` | `Num.Def Num.Theory` |

```coq
From mathcomp Require Import all_boot.
Fail Import GRing.Theory.    (* WRONG in a boot-only file: no ssralg *)

From mathcomp Require Import all_order all_algebra.
Fail Check lerD.             (* loaded, not imported: "not found" *)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Check lerD.                  (* RIGHT *)
```

Variations:
- Some analysis files add `Import numFieldTopology.Exports.` or
  `numFieldNormedType.Exports.`
- Requiring any mathcomp file already sets `SsrOldRewriteGoalsOrder`,
  `Asymmetric Patterns` and `Bullet Behavior "None"` globally
  (`boot/ssreflect.v:4-6`); do not add them (§26.5). Exception:
  analysis 1.16 files carry an explicit `Set`/`Unset
  SsrOldRewriteGoalsOrder` porting marker (the new order becomes the
  default with MathComp 2.6). Keep the file's line; when porting,
  switch `Set` to `Unset` and fix the side-goal order (§27.9).

```coq
From mathcomp Require Import all_boot.
(* not yet ported (most analysis 1.16 files): *)
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file,
  then remove the line when requiring MathComp >= 2.6 *)
(* already ported (e.g. realseq.v, experimental_reals/dedekind.v): *)
Unset SsrOldRewriteGoalsOrder.  (* remove this line when requiring
  MathComp >= 2.6 *)
```

**Probe preambles copy the header.** A rocq-mcp
`rocq_start preamble=…` must be a verbatim copy of the target file's
header: imports, the three flags, the `Import` line and every
`Local Open Scope`. Otherwise `Search`/`Check` results, notations and
implicit status differ from the file. Operational version: SKILL.md,
*Warm-import iteration*.

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
- `Context` is the modern form for declaring section variables. It
  mixes binder shapes in one line: `{x : T}` discharges as a
  **maximal** implicit, `[x : T]` as a non-maximal one. A plain
  binder (`d` or `(x : T)`) behaves like `Variable` (next bullet).
  mathcomp-analysis writes `Context d {T : measurableType d}
  {R : realType}.`: `T` and `R` become maximal implicits, and `d`,
  inferable from `T`, becomes `[d]` (e.g. `About ae_le_measureP`
  in `ess_sup_inf.v` prints `Arguments ae_le_measureP [d] ...`).
- `Variable` / `Variables` (and plain `Context` binders) do **not**
  always discharge as explicit arguments. Under the mandatory
  `Set Implicit Arguments` (§5), a variable that can be inferred from
  later arguments discharges as a **non-maximal implicit** `[T]`:
  `hd2 : forall [T : Type], T -> seq T -> seq T -> T` (example below).
  Non-inferable ones (`x0 : T`, `n : nat` in a nat-only statement)
  stay explicit. Use `Context {T}` for a maximal implicit. To force
  an explicit argument, add `Arguments lem : clear implicits.` after
  `End` (§16, §31.4); restating the names alone
  (`Arguments hd2 T x0 s1 s2.`) only asserts them and changes nothing.
  `Variable` remains extremely common in mathcomp sources.
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

### What `End` does to your statements

1. Each definition or lemma is abstracted over exactly the section
   Variables/Hypotheses its **statement or proof body** uses, in
   declaration order. Unused ones are dropped, so arity and argument
   order differ from lemma to lemma (MCB §1.4, §2.3.2).
2. A Hypothesis used only in the proof, even implicitly through
   `by []`, `//` or a hint, becomes a premise of the exported lemma
   (MCB §2.3.2; the rest of item 2 and items 3-4 are not from the
   book). This silently changes the signature and can weaken the lemma. Check
   with `About lem` after `End`. State a lemma-specific assumption in
   the header (`Lemma foo (h : P) : ...`), or restrict the proof with
   `Proof using x y.` / `#[using="x y"]`: `Qed` then fails with
   "The following section variable is used but not declared".
3. Declare types first, data next, hypotheses last.
4. Check arity with `About` / `Print Implicit` (§37.12) before relying
   on it at call sites (errors.md §4).

```coq
From mathcomp Require Import all_boot.
Set Implicit Arguments. Unset Strict Implicit.
Section Sec.
Variables (T : Type) (x0 : T) (n : nat).
Hypothesis n_gt0 : 0 < n.
Definition hd2 s1 s2 := head (head x0 s2) s1.
Definition unusedx (k : nat) := k.+1.  (* uses no section variable *)
Lemma uses_hyp : 0 < n.-1.+1.         (* statement never mentions n_gt0 *)
Proof. by rewrite prednK. Qed.
Lemma no_hyp : n <= n.
Proof using n. by []. Qed.  (* Qed fails if the proof touches n_gt0 *)
End Sec.
About hd2.       (* hd2 : forall [T : Type], T -> seq T -> seq T -> T *)
About unusedx.   (* unusedx : nat -> nat         (T, x0, n all dropped) *)
About uses_hyp.  (* uses_hyp : forall [n : nat], 0 < n -> 0 < n.-1.+1 *)
About no_hyp.    (* no_hyp : forall n : nat, n <= n                   *)
Arguments hd2 : clear implicits.     (* now hd2 : forall T : Type, ... *)
```

### Shape-encoded side conditions

- When positivity matters for **typing** (`'I_n.+1` with `ord0` /
  `ord_max`, rings on `'I_n.+2`, non-empty `'M_n.+1`, `thead` on an
  `n.+1.-tuple`), write `Variable n' : nat. Local Notation n :=
  n'.+1.` instead of `Hypothesis n_gt0 : 0 < n`. The library then
  finds `ord0`, `ord_max` and the canonical instances by unification
  (MCB §8.1).
- When positivity matters only in proofs (a divisor must be
  positive), a named hypothesis `n_gt0` (§14) is fine.
- Pitfall: a `0 < n` hypothesis with `'I_n` makes `ord0` unavailable
  and leads to `Ordinal n_gt0` terms, which carry a proof and do not
  unify across call sites (MCB §8.1).
- Modular arithmetic on `'Z_p` / `'I_p'.+2`: see domains/41 §41.7.

```coq
From mathcomp Require Import all_boot.
Section Pos.
Variable n' : nat.
Local Notation n := n'.+1.
Implicit Types i : 'I_n.
Lemma ord0_le i : (ord0 : 'I_n) <= i.  (* ord0 needs n = _.+1 *)
Proof. by []. Qed.
Check ord_max : 'I_n.
End Pos.

Section Hyp.  (* WRONG shape when the constraint matters for typing *)
Variables (m : nat) (m_gt0 : 0 < m).
Fail Check (ord0 : 'I_m).        (* 'I_m is not 'I_(_.+1) *)
Check Ordinal m_gt0 : 'I_m.      (* proof term in the index: brittle *)
End Hyp.
```

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
  (fail early and locally, §29.3)
- **Do not use `Focus` or focusing braces `{ ... }`** -- use
  indentation and terminators. Clear items `{h}`/`{}h` in intro
  patterns and `rewrite {}h` are fine and encouraged (§27.11).
- Avoid numerical occurrence selectors (`{1 3}`, `{-2}`) -- use
  context patterns, `set`, or `rewrite /` instead
  (Issue #436). Translations: "Replacing numeric occurrence
  selectors" below.

### Granularity: one line per reasoning step

Counterweight to §22: minimality applies to **bookkeeping**, never to
deleting the declarative `have`s that carry the mathematics
(MCB §4.3.1).

1. Outline the paper proof first. Each key intermediate claim becomes
   a `have`/`suff` whose statement reads without running Rocq.
2. One line = one step you would say aloud. Bookkeeping (side
   conditions, reshuffling with short-named lemmas like `addnCA`) may
   be packed densely on that line.
3. Avoid "vertical" scripts (one `rewrite` per line) and "horizontal"
   lines that pack two or more mathematical steps.
4. Name the facts a case split produces on the case line, e.g.
   `case: (leqP m n) => [le_mn|lt_nm]`, not on a later
   `move=>`.
5. Do not insert `have`s whose only job is to reshape a goal for
   `lia`/`ring`: either the tactic closes the paper step as stated
   (§45), or prove that step with rewrites.
6. `have`s at paper-proof milestones double as repair checkpoints: when
   a library change breaks the script, the failure stays between two
   named claims (MCB §4.3.3).

Canonical example (one mathematical step per line; bookkeeping packed
with `?`/`//`):

```coq
From mathcomp Require Import all_boot.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1.
  by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
```

### Replacing numeric occurrence selectors

Keep the ban even when copying the book or older sources. Occurrence
numbers still compile in Rocq 9; the ban is this skill's review
convention, not the book's. Book idioms below: MCB Part III, cheat
sheet (`rewrite {2}lem` is not from the book).

| Book idiom | Allowed form | See |
|---|---|---|
| `elim: n.+1 {-2}n (ltnSn n)` (strong induction) | `elim/ltn_ind: n => n IHn` or `have [k] := ubnP n; elim: k n => // k IHk n` | templates.md §21 |
| `cmd: {-2}x (erefl x)` (remember an equation) | `case E: x` / `move E: x => y` | §27.10 |
| `set n := {2 4}(_ + b)` | `set n := (X in _ = _ + X)`: a context pattern naming the **position** | §30.8, §29.2 |
| `rewrite {3}[in X in f _ X]E` | more specific pattern `[in X in f _ (_ + X)]E`, or `[e in X in p]E` | §29.2 |
| `rewrite {2}lem` | `rewrite [in RHS]lem` / `[LHS]lem` / `[X in _ * X]lem` | §29.2 |

A context pattern selects a **syntactic position**, not the k-th
instance of a term, so it is not a literal equivalent of `{2 4}`:
check what it binds (here `n := 0 + a + b`).

```coq
From mathcomp Require Import all_boot.

(* instead of: set n := {4}(_ + b). *)
(* goal adapted from MCB Part III, cheat sheet (set example) *)
Lemma st a b : (a + b) + (a + b) = (a + b) + (0 + a + b).
Proof. by set n := (X in _ = _ + X). Qed.
```

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

**Qed vs Defined**:

1. `Lemma`/`Fact`/`Theorem` always end with `Qed`. `Defined` on a
   lemma is a review flag: it exposes the proof term to reduction and
   conversion, which causes performance and unfolding surprises.
2. Build **data** as terms, with proof obligations as separate
   Qed-proved `*_subproof` lemmas (§37.4). The data then computes and
   the proofs stay opaque.
3. `Definition foo : T. Proof. … Qed.` makes `foo` opaque: projections
   no longer compute and `by []` fails. This is the data-by-tactics
   anti-pattern.
4. Use `Defined` only when the term itself must reduce (`Acc`-based
   recursion, `eq_rect` transports used in computation, terms evaluated
   by `vm_compute`/reflection). Add a comment saying why.
5. When a definition must stay folded (inference control), lock it
   with `HB.lock` (§15, §35.8), sparingly; never seal it with `Qed`.

```coq
From mathcomp Require Import all_boot.

Record pos := Pos { pval :> nat; _ : 0 < pval }.

(* RIGHT: data is a term, the obligation is a Qed lemma *)
Lemma three_subproof : 0 < 3. Proof. by []. Qed.
Definition three : pos := Pos 3 three_subproof.
Lemma threeE : pval three = 3. Proof. by []. Qed.

(* WRONG: data built by tactics and sealed with Qed is opaque *)
Definition bad : pos. Proof. by exists 3. Qed.
Lemma badE : pval bad = 3. Proof. Fail by []. Abort.
```

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
| `1` | (alt.) Singleton set; `_set1` when `1` would read as unit | `cards1`, `sub1set`, `mulg_set1` |
| `A` | Associativity | `andbA : associative andb` |
| `AC` | Right commutativity | |
| `ACA` | Self-interchange | `orbACA` |
| `b` | Boolean argument | `andbb : idempotent_op andb` |
| `C` | Commutativity | `andbC : commutative andb` |
| `C` | (alt.) Complement | `predC` |
| `C` | (alt.) Constant | |
| `Cr` | Complement on the right | `setUCr : A :\|: ~: A = [set: T]` |
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
| `S` | (alt.) Subset argument / monotony (see §12) | `setUS`, `mulgS` |
| `T`/`t` | Boolean truth | `andbT : right_id true andb` |
| `T` | (alt.) Total set | |
| `U` | Union | `predU` |
| `W` | Weakening | `in1W` |
| `X` | (alt.) Cartesian product | `setX`, `cardsX` |

One letter can carry several meanings (`S`, `X`, `1`, `R`;
MCB §2.5.2). The argument types disambiguate.

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
| `LR`/`RL` | (alt.) Move a function across `=` with its `cancel` | `canLR`, `canRL` (Corelib ssrfun) |

### Argument Type Abbreviations

| Suffix | Meaning | Example |
|--------|---------|---------|
| `g` | Group argument | |
| `n` | Natural number argument | |
| `r` | Ring argument | |
| `z` | Int argument | |
| `nn` | Both operands are the same nat | `leqnn`, `subnn`, `divnn : d %/ d = (0 < d)` (not `= 1`) |
| `xx` / `rr` | Same, order-generic / ring | `lexx`, `ltxx` / `subrr` |

### Group-Theory Abbreviations (fingroup)

Suffixes from the book's naming list (MCB §2.5.2):

| Suffix | Meaning | Example |
|--------|---------|---------|
| `G` | Group argument | `mulGS`, `mulGid` |
| `J` | Conjugation | `groupJ`, `conjJg` |
| `M` | Group multiplication | `groupM` |
| `R` | Commutator | `groupR`, `morphimR` |
| `Y` | Join `<*>` | `conjYg`, `quotientY` |
| `F` | Group functor | `morphimF` |

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

### Standard property predicates (ssrfun)

State an instance of a classical law with the Corelib ssrfun
predicate, not a spelled-out `forall` (MCB §2.3.1): the type stays
short, the name follows §11, and `Search (commutative _)` finds it.

| Predicate | Unfolds to | Suffix | Example |
|-----------|-----------|--------|---------|
| `commutative op` | `op x y = op y x` | `C` | `addnC` |
| `associative op` | `op x (op y z) = op (op x y) z` | `A` | `addnA` |
| `left_commutative op` | `op x (op y z) = op y (op x z)` | `CA` | `addnCA` |
| `right_commutative op` | `op (op x y) z = op (op x z) y` | `AC` | `addnAC` |
| `interchange op1 op2` | `op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t)` | `ACA` | `mulnACA` |
| `left_id e op` / `right_id e op` | `op e x = x` / `op x e = x` | `0`/`1` (position) | `add0n` / `addn0` |
| `left_zero z op` / `right_zero z op` | `op z x = z` / `op x z = z` | `0` (position) | `mul0n` / `muln0` |
| `left_distributive op1 op2` | `op1 (op2 x y) z = op2 (op1 x z) (op1 y z)` | `Dl` | `mulnDl` |
| `right_distributive op1 op2` | `op1 x (op2 y z) = op2 (op1 x y) (op1 x z)` | `Dr` | `mulnDr` |
| `injective f` | `f x = f y -> x = y` | `_inj` | `succn_inj` |
| `left_injective op` / `right_injective op` | injective in one argument | `I` | `addnI` |
| `cancel f g` / `pcancel f g` | `g (f x) = x` / `g (f x) = Some x` | `K` | `addKn` / `pickleK` |
| `involutive f` | `f (f x) = x` | `K` | `setCK`, `negbK` |
| `idempotent_op op` | `op x x = x` | `b` / `nn` | `andbb`, `maxnn` |

`idempotent` is deprecated for `idempotent_op` since mathcomp 2.3.0
(boot/ssrfun.v:39). Morphism laws use `{morph f : x y / ...}`,
`{homo ...}`, `{mono ...}` (§37.7).

```coq
From mathcomp Require Import all_boot.
Definition mx (m n : nat) := maxn m n.
(* WRONG: spelled-out law; Search (commutative _) misses it *)
Lemma mx_comm m n : mx m n = mx n m.  Proof. exact: maxnC. Qed.
(* RIGHT: the ssrfun predicate; short type, suffix from §11 *)
Lemma mxC : commutative mx.     Proof. exact: maxnC. Qed.
Lemma mx0 : right_id 0 mx.      Proof. exact: maxn0. Qed.
Lemma mxnn : idempotent_op mx.  Proof. exact: maxnn. Qed.
Search (commutative mx).        (* finds mxC, not mx_comm *)
Check (mulnDl : left_distributive muln addn).
Check (addKn : forall n, cancel (addn n) (subn^~ n)).
```

### Monotony lemmas and argument prefixes

- Closure under an operation: property + operator suffix (`groupM`).
- Monotony in a subset argument: operator + `S` at the position that
  grows (`mulgS`, `setUS`, `setSI`).
- The prefix is the operation, the rest the property it preserves:
  `quotient_normal : A <| B -> A / H <| B / H`
  (fingroup/quotient.v:474), not `normal_quotient` (MCB §2.5.2).

```coq
From mathcomp Require Import all_boot all_fingroup.
Check groupM.  (* x \in G -> y \in G -> x * y \in G      property + M *)
Check mulgS.   (* B \subset C -> A * B \subset A * C     operator + S *)
Check quotient_normal. (* A <| B -> A / H <| B / H            *)
Check canLR.   (* cancel f g -> x = f y -> g x = y *)
Check canRL.   (* cancel f g -> f x = y -> x = g y *)
Check cardsX.  (* #|setX A1 A2| = #|A1| * #|A2|    X = product *)
```

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

Name a hypothesis after its statement so a reader can rebuild its type
without scrolling (MCB §4.3.1; examples in §3.3, §4.1.1). Common
forms, not mandates:

| Hypothesis | Name |
|------------|------|
| `0 < n` / `1 < x` | `n_gt0` / `x_gt1` |
| `n != 0` / `x != 0` | `n_neq0` / `x_neq0` |
| `m <= n` / `m < n` | `le_mn` (also `mn`) / `lt_mn` |
| `prime p` | `p_pr` (also `pr_p`) |
| `p %\| m` | `p_dv_m` |
| `x = y` | `eq_xy` (also `exy`, `xy`) |
| `x \in A` / `A \subset B` | `Ax` (also `xA`) / `sAB` |
| `P x` (bigop filter) | `Px` |
| `A -> B` | `hAB` |
| `injective f` / `coprime m n` | `f_inj` / `co_mn` |

- Name each branch of a case split by its statement:
  `case: (leqP m n) => [le_mn|lt_nm].`
- After `case: n => [|n]`, reuse `n` (or `n'`) for the predecessor.
- Short names such as `addnCA` mark bookkeeping rewrites; give a
  substantive new lemma a descriptive name (§10).

```coq
From mathcomp Require Import all_boot.
Lemma name_ex p n (p_pr : prime p) (n_gt0 : 0 < n) : 0 < p * n.
Proof. by rewrite muln_gt0 prime_gt0. Qed.
Lemma split_ex m n : minn m n <= maxn m n.
Proof.
case: (leqP m n) => [le_mn|lt_nm].
  exact: le_mn.
exact: ltnW lt_nm.
Qed.
```

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

Here `proof : Equality.axiom eq_op`. For a new datatype, one
`X.copy T (pcan_type fK)` line along an encoding usually replaces the
hand-proved axiom (§36.12).

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
2. **Transfer**: `[Structure of Type by <:]` (§36.13)
3. **On**: `Structure.on term`
4. **Copy/Alias**: `Structure.copy T expr`

### Instance hygiene

- **Name the carrier.** The carrier is the first explicit argument
  of `X.Build` / `X.copy` after the structure's parameters: `'I_p` in
  `GRing.isZmodule.Build 'I_p`, `V` in `GRing.Zmodule_isLmodule.Build
  R V`, the operator in `Monoid.isComLaw.Build nat 0 addn`. Write it as
  users write it (`'I_p`, the alias `M`), never `_` (MCB §8.1). With `_` the carrier is read off the axioms'
  types, so an instance meant for `M := nat` lands on `nat` (HB warns
  `HB.no-new-instance`) and `M` gets nothing.
- **Name every axiom.** One `Lemma`/`Fact` per axiom, usually `Local`
  or `*_subproof` (§18, §37.4), passed to `Build` by name.
  One-line terms such as `(fun x h => h)` or `(fun _ _ => erefl)` are
  fine (`algebra/ssralg.v:4693`); no `ltac:(...)` or multi-step
  proof terms inside `Build`: they hide the axiom from `Search`.
- **Define operations first.** Each data field gets its own
  `Definition` before the instance, so its head is stable for
  rewriting and locking (§35.8).
- **One `Build` per `HB.instance` line**, so `HB.about` locates each
  instance (§35.7).

Model instance, `algebra/zmodp.v:151` (MCB §8.1):
`GRing.isZmodule.Build 'I_p (@Zp_addA _) (@Zp_addC _) Zp_add0z Zp_addNz`.
Worked example with named axioms: §34.10 (MCB §6.7.2, §8.2).

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Definition M := nat.
Lemma M_eqP : Equality.axiom eqn.
Proof. by move=> x y; apply: eqnP. Qed.
(* WRONG: `_` is read off M_eqP's type, i.e. nat. HB warns
   HB.no-new-instance and M gets no instance of its own. *)
HB.instance Definition _ := hasDecEq.Build _ M_eqP.
Check (M : eqType).          (* still passes: unfolds M to nat *)
Fail HB.about M.             (* "uninteresting constant" *)
(* RIGHT: name the carrier. *)
HB.instance Definition _ := hasDecEq.Build M M_eqP.
HB.about M.                  (* eqtype.Equality *)
```

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

`Implicit Type s : seq T.` also covers the variants `s1`, `s2`, `s'`
(MCB §1.4) and `s_1`, both as lemma binders (`Lemma l s1 s' : ...`)
and as statement binders (`forall s2, ...`).

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

Minimality targets bookkeeping. Keep the declarative `have`s that
carry the mathematics (§8 "Granularity").

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

**Conversion-first closing** (MCB §2.2.1, §3.4, §3.6). Convertible statements
share their proofs, so a goal that computes to a trivial one needs no
lemma.

1. **Try `by []` before searching for a lemma.** It closes any goal
   convertible to a trivial one (`isT`, `erefl`, `I`): `0 < n.+1`,
   `n.+1 != 0`, `size [:: a; b] = 2`, `nth x0 (x :: s) 0 = x`,
   `size (x :: s) = (size s).+1`.
2. **Term position.** When a lemma argument holds by computation, pass
   `(isT : 1 < p.+2)` (as upstream does at `boot/prime.v:856`) or
   `(erefl : a = b)`. Do not add a `have` or cite `ltn0Sn` for it.
   `isT` is `is_true_true` (Corelib `ssrbool`); `erefl` works only
   when both sides are convertible.
3. **If `by []` fails**, try `/=` first, then the named lemma.

```coq
From mathcomp Require Import all_boot.

Lemma conv_ex n p : (0 < n.+1) && (p.+1 != 0).
Proof. by []. Qed.

Lemma conv_seq (T : Type) (x0 x : T) (s : seq T) :
  [/\ size [:: x; x] = 2, nth x0 (x :: s) 0 = x
    & size (x :: s) = (size s).+1].
Proof. by []. Qed.

(* term position: pass the computed fact, no have, no ltn0Sn *)
Check prime_gt0 (isT : prime 7) : 0 < 7.
Check (erefl : 2 + 1 = 3).
Fail Check (erefl : \sum_(i < 3) i = 3).   (* locked head *)
```

Where conversion does **not** close the goal:

| Goal shape | Why `by []` / `isT` / `erefl` fail | Fix |
|------------|------------------------------------|-----|
| Bigops (`\sum`, `\prod`, `\big`), `HB.lock`ed definitions | the head is locked | unfold with the bigop lemmas (`big_ord_recr`, `big_ord0`, §34) |
| `x + 0 = x` over an abstract `pzRingType` | the operators are projections of an unknown instance | `addr0`, or `ring` (§45) |
| Large `nat` numerals | `nat` is unary, so evaluation is slow | keep the numbers symbolic, or use a lemma |
| `n + 1 = n.+1`, `n * 0 = 0` | `addn`/`muln` recurse on the first argument, here a variable | `addn1`, `muln0` (§49.4) |

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
7. Is there an `auto`/`intuition` I can replace by a case split or a
   view? (below)

If you cannot answer "no" to all seven, the line is not yet minimal.

**No black-box automation.** A script must fail at the line that
broke, with a local diagnosis (MCB §4.3.2).

- **Do not use** `auto`, `eauto`, `intuition` or `firstorder` as
  closers in mathcomp/analysis code. They are slow, fragile under
  library changes, and fail without saying which step broke. About 30
  legacy uses remain (`ssralg.v`, `ordered_qelim.v`); do not add new
  ones. `tauto` on classical `Prop`/set goals is accepted in analysis
  (`boolp.v`, `classical_sets.v`).
- **Review points, not bans:** `congruence` and `repeat` loops. Keep
  them only when the explicit steps are clearly worse.
- **Allowed automation:** `done` / `by []` (`trivial` + the `core`
  hint db, §37.9); `//` and `//=` in chains (§26.4); the certified
  `ring` / `field` / `lra` / `nra` / `lia` when the carrier fits (§45).
- **Boolean tautologies:** `by case: b`, `by case: a; case: b`, or the
  bool rewrite rules (`andbC`, `negbK`, ...).
- **Propositional glue:** intro patterns + views (`/andP`, `/orP`,
  `/implyP`).
- If a hammer finds a proof, rewrite it into explicit steps before
  committing.

```coq
From mathcomp Require Import all_boot.

Lemma em_bool (b : bool) : b || ~~ b.
Proof. by case: b. Qed.
(* not: Proof. destruct b; auto. Qed. *)

Lemma and_swap (a b : bool) : a && b -> b && a.
Proof. by case/andP=> -> ->. Qed.   (* not: intuition *)
```

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
When a constraint is genuinely needed, write `(T : X)`. On a
`Set`-sorted carrier (`nat`, `bool`), `[the eqType of nat]` fails in
mathcomp 2.5; `[the eqType of nat : Type]` works (§48).

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
- Removing it changes the **inferred sort**. A binder
  first used as a hypothesis elaborates to `Type`, not `bool`:
  `Lemma ex_true b : b -> b || false.` fails with `The term "b" has
  type "Type" while it is expected to have type "bool"`. Keep
  `(b : bool)` or declare `Implicit Types b : bool.` (§16; errors.md
  §2).

```coq
From mathcomp Require Import all_boot.
Fail Lemma ex_true b : b -> b || false.  (* b : Type, expected bool *)
Lemma ex_true (b : bool) : b -> b || false.
Proof. by move=> ->. Qed.
```

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

### 25.5 Know the implicit status first

- Before writing `@lem _ _ x` or `(x := ...)`, run `About lem`
  (MCB §6.2). It
  prints `Arguments lem ...`: `{x}` is a maximal implicit, `[x]` a
  non-maximal one (the default under `Set Implicit Arguments`), and a
  bare name is explicit.
- Prefer the named form `(x := ...)` when the name is stable (§25.2,
  §31.2); otherwise use `@`.
- Design rule for new lemmas: keep explicit the arguments users must
  supply to pin a rewrite occurrence, e.g. `rewrite (bigD1 j)`.

```coq
From mathcomp Require Import all_boot.
About eq_op.  (* Arguments eq_op {s} _ _            s is maximal *)
About bigD1.
(* Arguments bigD1 [R] [op x I] j [P] [F] _
   j explicit, the rest non-maximal; op : SemiGroup.com_law R *)
```

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

### 26.5 Why terminators are mandatory: mathcomp disables bullet checking

`boot/ssreflect.v:4` (lines 4-6) does `Global Set`
of `SsrOldRewriteGoalsOrder`, `Asymmetric Patterns` and
`Bullet Behavior "None"` for every file that imports mathcomp.
`Test Bullet Behavior.` prints `"None"`. Vanilla Rocq defaults to
`"Strict Subproofs"`, so stdlib habits wrongly trust bullets.

**Consequence.** `-` / `+` / `*` are layout only. A branch that fails
to close gives **no error at the bullet**: the next bullet silently
works on the wrong goal, and the failure surfaces later, often as
`Attempt to save an incomplete proof` at `Qed` (errors.md §9).

**Rules.**

- The last line of every branch is `by ...`, `exact: ...` or `done`.
  `by` fails immediately, at the right line. This is the semantic
  reason behind §26.1-§26.3.
- When repairing, do not rely on bullets to localise errors. Step with
  `rocq_check` and watch the goal count.
- Do not add `Set Bullet Behavior "Strict Subproofs"` to mathcomp
  files; it is not house style.

```coq
From mathcomp Require Import all_boot.

Test Bullet Behavior.   (* "None" once mathcomp is imported *)

(* WRONG -- the first branch is left open; nothing complains *)
Lemma t (a b : nat) : (a = b /\ b = a) /\ True.
Proof.
split.
- split.   (* 2 new goals, NOT closed *)
- (* no error: bullets are inert under mathcomp *)
  Show.    (* shows 3 goals: a = b, b = a, True *)
Abort.

(* RIGHT -- every branch ends with a terminator that fails in place *)
Lemma t_ok (a : nat) : (a = a /\ a = a) /\ True.
Proof.
split.
- by split.
- by [].
Qed.
```

- **Asymmetric Patterns:** constructor patterns in `match` omit the
  inductive's parameters: for `Inductive box A := Box of A`, write
  `Box x`, not `Box _ x` (`@Box _ x` binds them explicitly).
- **SsrOldRewriteGoalsOrder:** decides the order of the side goals of
  conditional rewrites; see §27.9.

---

## 27. Book-Keeping Idioms in Proof Scripts

The single biggest source of "extra book-keeping" in proofs is
introducing names for hypotheses that are used only once. Prefer
SSReflect's intro-pattern combinators.

**Goal-as-stack vocabulary** (MCB §4.1):

- The goal is a stack; **Top** is its first premise.
- `=>` pops: it names, destructs, views and rewrites (§27.1–§27.7).
- `tac: items` pushes context items or terms back **before** `tac`
  runs (§27.10).
- `move` is the no-op carrier for either side: `move=> x`, `move: x`.

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
| `move=> /(_ x) h` | Specialize a ∀-hypothesis at `x` (`/lem` instead applies `lem` **to** the item) |
| `move=> /(_ _ hx)` | Feed a premise; the `_` is inferred from `hx` |
| `move=> /v1/v2 h` | Chain views on one item: `v2` receives `v1`'s **result** (nest inside brackets for `andP`-style splits, phrasebook §2) |
| `move=> /prime_gt1-x_gt1` | Name a view's result (the `-` is cosmetic) |
| `move=> [x [//\|z]]` | Close a trivial branch inside the pattern |
| `move=> [x y] /= h` | Simplify (e.g. `.1`/`.2`) before introducing `h` |
| `move=> {h}` | Clear `h` |
| `move=> {}h` | Introduce the goal's Top under the existing name `h`, replacing the old `h` (§27.11) |
| `case=> [y -> {x}]` | Destruct `exists2`, rewrite with the equation, clear the stale `x` |
| `=> /leq_trans->` | Partial application as a view, then rewrite with the result |
| `=> {n}// n` | Clear, close trivial goals, re-introduce |

**Pitfall: `case: n => [|m]` does not split twice.** The first bracket
after `case:`/`elim:` only distributes names over the goals the tactic
created (2 goals, not 4). To also split the next premise, add a second
bracket (`case: n => [|n] [|m]`, 4 goals), or nest it to split in one
branch only (`case: n => [|n [|m]]`, 3 goals). A bracket splits on its
own only on an un-split goal (`move=> [|m]`). (MCB §4.1.1; MCB
Part III, cheat sheet)

```coq
From mathcomp Require Import all_boot.

Lemma ex1 : forall xy : nat * nat,
  prime xy.1 -> odd xy.2 -> 2 < xy.2 + xy.1.
Proof.
move=> [x [//|z]] /= /prime_gt1-x_gt1 _.   (* xy.2 = 0: closed by // *)
by apply: ltn_addl x_gt1.
Qed.

Lemma spec (P : nat -> Prop) (G : Prop) :
  (forall n, P n) -> (P 3 -> G) -> G.
Proof. by move=> /(_ 3) h; apply. Qed.

Lemma feed (P : nat -> Prop) (hx : 0 < 2) :
  (forall n, 0 < n -> P n) -> P 2.
Proof. by move=> /(_ _ hx). Qed.

Lemma chain p : prime p -> 0 < p.
Proof. by move=> /prime_gt1/ltnW. Qed.

Lemma ex2 (P Q : nat -> Prop) x :
  (exists2 y, x = y & Q y) -> (Q x -> P x) -> P x.
Proof. by case=> [y -> {x} qy] /(_ qy). Qed.

Lemma pview m n p : n <= p -> m <= n -> m <= p.
Proof. by move=> np /leq_trans->. Qed.   (* side goal n <= p: by np *)

Lemma route n : forall m, n + m = m + n.
Proof.
(* 1st bracket routes the 2 goals of `case: n`; 2nd splits m: 4 goals *)
by case: n => [|n] [|m]; rewrite // addnC.
Qed.
```

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
- A side branch that closes in one short line needs no indentation at
  all: `t; first by a`, `t; last by a` or `t; [a | b]` (§27.9).
- Never mix bullet styles at the same level.

**No bullets when only 2 subgoals are generated** -- two-space
indentation suffices (analysis PR #410).

### 27.9 Sequencing and goal selectors

(MCB §2.2.2, §2.3.3, §5.1.1. The `..` ranges, `last 1 first` /
`first 1 last`, `all:` and `try` are not from the book.)

| Form | Meaning |
|---|---|
| `t1; t2` | `t2` on **every** subgoal of `t1`, including the side conditions of a conditional rewrite. Not the same as `t1. t2.`, which runs `t2` on the current goal only |
| `t; [a \| b]` | one tactic per goal, in order; the counts must match; `[\| b]` leaves goal 1 untouched |
| `t; [t1 \| t ..]` / `t; [t1 \| t .. \| tn]` | `t` repeated on every middle goal; the ends are pinned |
| `t; first by a` / `t; last by a` | close goal 1 / the last goal in place; fails loudly if `a` does not close it (MCB Introduction) |
| `t; last first` / `t; first last` | reverse the goal list (a swap for 2 goals; MCB §2.2.2). To move only the last goal up: `t; last 1 first`; only goal 1 down: `t; first 1 last` |
| `all: t` | `t` on every open goal. Sentence-initial only: `split. all: by …`; `split; all: …` is a syntax error |
| `elim: n => // n IHn` | `//` closes every goal `done` solves during introduction, typically the base case |
| `t; try t'` | review point: which goals `t'` fails on stays implicit; prefer an explicit selector |

Rules:

1. For a 2-goal split whose side branch closes in one short line,
   prefer `t; first by a` (or `t; last by a`) over an indented block
   (§27.8).
2. A bare `t; first a` without `by` is not safe: if `a` leaves the goal
   open, the script continues with more goals than you think.
   `first by a` is safe.
3. Never turn `.` into `;` "for compaction" without checking the goal
   count: `rewrite lem; t` also runs `t` on `lem`'s side conditions.
4. **Side conditions of conditional rewrites.** Close them inside the
   chain: `//`, `?lem`, or the proof passed as an argument
   (`rewrite (divnMDl _ _ d0)`). Do not write `rewrite lem; last by …`.
   The side-goal order depends on `SsrOldRewriteGoalsOrder`:
   - mathcomp 2.5 sets it. After `rewrite -[m * d]addn0 divnMDl` the
     main goal `m + 0 %/ d = m` comes first and `0 < d` last.
   - After `Unset SsrOldRewriteGoalsOrder` the order is reversed. Some
     analysis 1.16 files already carry the `Unset`. Upstream header
     comments say to flip `Set` to `Unset` when porting a file and to
     drop the line when requiring MathComp >= 2.6 (§5).
   - After the flip, `; last by …` fails and a bare `; first a` /
     `; last a` runs on the wrong goal. With bullets inert (§26.5) the
     error surfaces far away.
5. Explicit arguments follow the signature. In `mathcomp/boot/div.v`,
   `divnMDl` (l. 95) is `forall (q m : nat) [d : nat], 0 < d -> …`,
   so `(divnMDl _ _ d0)` fills `q`, `m`, then the proof (`d` is
   implicit). Check with `About` before writing the underscores.

```coq
From mathcomp Require Import all_boot.

Lemma t1 n : n + 0 = n /\ 0 + n = n.
Proof. by split; [rewrite addn0 | rewrite add0n]. Qed.

Lemma t2 (a b : nat) : a + 0 = a /\ b * 1 = b.
Proof. split; last by rewrite muln1. by rewrite addn0. Qed.

Lemma t3 (a b : nat) : a + 0 = a /\ b + 0 = b.
Proof. split. all: by rewrite addn0. Qed.

(* 4 goals: goal 1 pinned, `..` repeats `right => -[]` on the rest *)
Lemma myandP (b1 b2 : bool) : reflect (b1 /\ b2) (b1 && b2).
Proof. by case: b1; case: b2; [left | right => -[] ..]. Qed.
```

```coq
From mathcomp Require Import all_boot.

(* RIGHT -- side condition `0 < d` closed in the chain by `//` *)
Lemma t4 m d : 0 < d -> (m * d + 0) %/ d = m.
Proof. by move=> d0; rewrite divnMDl // div0n addn0. Qed.

(* RIGHT -- proof passed explicitly: no side goal is created *)
Lemma t4' m d : 0 < d -> (m * d + 0) %/ d = m.
Proof. by move=> d0; rewrite (divnMDl _ _ d0) div0n addn0. Qed.

(* WRONG -- assumes the side goal comes last; breaks once   *)
(* SsrOldRewriteGoalsOrder is unset:                        *)
(* move=> d0; rewrite divnMDl; last by [].                  *)
```

### 27.10 The discharge side: `tac: items`, generalization, `in H *`

(MCB §4.1.3, §5.4, Part III cheat sheet. Not from the book: the
`move: (t) => x`, `move E: (t) => x` and `apply: lem H` rows; MCB
MCB §4.1.3 calls the colon of `apply:` a marker, not a discharge.)

| Form | Effect |
|---|---|
| `case: y odd_y` | push `y` **and** the hypotheses that mention it: list the variable first, then its dependents |
| `case: y {odd_y}` | push `y`, clear `odd_y` |
| `case E: y => [\|y']` | also record the branch equation `E : y = 0` / `E : y = y'.+1` (replaces the book's `{-2}x (erefl x)`) |
| `move: (lem args)` | push a fact without naming it |
| `move: (H)` vs `move: H` | push a copy and keep `H`, vs push and clear `H`. `apply: H`, `case: H`, `elim: H` and `apply: lem H _` clear `H` too; write `apply: (lem H)` to keep it |
| `move: @x` | push a let-bound `x` and keep its body (`let x := e in …`) |
| `move: (t) => x` | abstract every occurrence of the term `t` (e.g. `size s`) as a fresh `x`; the link to `t` is lost, so only when the proof no longer needs it |
| `move E: (t) => x` | same, and keep `E : t = x` (ssreflect's `remember`; `case E: (t)` likewise) |
| `apply: lem H` / `exact: lem H` | the `:` discharges: `H` is pushed and cleared first (≈ `move: H; apply: lem`), so it must fit `lem`'s last premise; `apply: leq_trans H` fails for `H : m <= n`. To pass `H` as an argument (and keep it), parenthesize: `apply: (leq_trans H)` |

**Generalize before induction.** Push every variable or hypothesis that
must vary in the IH: `elim: n m h => [|n IHn] m h`, or
`elim: n => [|n IHn] in m h *` (library style, boot/ssrnat.v:494:
`elim: n => // n IHn in M leMn *`). Never write `elim: n` and then
fight a weak IH. The same `: items` list works for `case:`, `elim:`
and `apply:`.

**Localisation with `in`.**

- `rewrite E in H` rewrites `H` only. `rewrite E in H *` rewrites `H`
  and the goal (MCB §7.2). `in H1 H2 *` rewrites several.
- `case: n => [|n] in H *` and `do [tac] in H *` generalize `H`, run,
  and reintroduce it. See algebra/matrix.v:594:
  `do [case: e_mn; case: m3 /; case: n3 /] in A *`.
- `in (H) *` keeps a copy of `H` in the context (boot/ssrnat.v:512).
- Prefer these over `move: H; rewrite E => H`. When `H` is consumed
  once, prefer an intro-pattern rewrite or view (§27.1, §27.3).
- A statement may name a repeated subterm with a let-binder
  `(ed := edivn m d)`. When `case`/`elim` would generalize `ed`, add
  `@ed` to the item list to keep its body: `case: (ubnPgeq m) @ed`
  (MCB §5.4). Use this sparingly: public statements usually avoid
  lets.

| Message | Likely cause | Fix |
|---|---|---|
| `y is used in hypothesis odd_y.` on `move: y` / `case: y` | a hypothesis that mentions `y` stays in the context | push it too (`case: y odd_y`) or clear it (`case: y {odd_y}`) |
| `p is used in hypothesis q.` on `rewrite E in p` or `apply: lem p` | another hypothesis depends on `p` | rewrite the dependents too (`rewrite E in p q *`); parenthesize the term (`apply: (lem p)`) |

More bookkeeping errors: errors.md §7.

```coq
From mathcomp Require Import all_boot.

Lemma disc y (odd_y : odd y) : 0 < y.
Proof. by case E: y odd_y => [|y'] //=. Qed.

Lemma disc2 y (odd_y : odd y) : y.+1 != 0.
Proof. by case: y {odd_y}. Qed.

Lemma push : 7 <= 7.
Proof. by move: (leqnn 7). Qed.

Lemma dep y (odd_y : odd y) : 0 < y.
Proof.
Fail move: y.     (* y is used in hypothesis odd_y. *)
by case: y odd_y.
Qed.

Lemma double_leq m n : m <= n -> m.*2 <= n.*2.
Proof.
elim: n => [|n IHn] in m *; first by rewrite leqn0 => /eqP->.
by case: m => [//|m] /IHn; rewrite doubleS.
Qed.

Lemma size0 (s : seq nat) : size s = 0 -> s = [::].
Proof. by case E: s => [//|x t]. Qed.
```

```coq
From mathcomp Require Import all_boot.

Lemma in_star (n : nat) (h : n + 0 > 0) : n + 0 = n.
Proof. by rewrite addn0 in h *. Qed.

Lemma case_in n (h : 0 < n) : n.-1.+1 = n.
Proof. by case: n => [|n] in h *. Qed.

Lemma rw_in (a b : nat) (h : a = b) (p : a < 3) : a < 4.
Proof. rewrite h in p *. exact: leq_trans p _. Qed.

Lemma rw_dep (a b : nat) (h : a = b) (p : a < 3) (q : p = p) : a < 4.
Proof.
Fail rewrite h in p.     (* p is used in hypothesis q. *)
by rewrite h in p q *; exact: (leq_trans p).
Qed.

(* `@k` keeps the body of `k`, so `/k` can unfold it *)
Lemma keep_let m (k := m + 0) : k = m.
Proof. by case: m @k => [|m] k; rewrite /k addn0. Qed.
```

### 27.11 Refining and clearing hypotheses

(MCB §4.3.3 for items 1, 4 and 7; MCB Part III, cheat sheet for the
clear items of 3 and 5.)

1. To replace `H` by a transformed version, write `have {}H : T by …`
   or `move/view: H => {}H`. Never build `H1`, `H2`, `H3` chains.
2. Never write `have {H}H : T`. Rocq 9.1 warns `Duplicate clear of H.
   Use {}H instead of {H}H [duplicate-clear,ssr]` (errors.md §9).
   This departs from the book, which uses `have {H}H` (MCB §4.3.3).
3. Clear a hypothesis once it is dead (`=> {H}`, `case: x {H}`). Then a
   later `//` cannot pick up the wrong fact.
4. `apply: H`, `move: H`, `case: H` and `elim: H` consume `H`. Write
   `(H)` to push a copy and keep `H`: `move: (H) => /(_ 1) h1`.
5. `rewrite {}H` rewrites with `H`, then clears it. `rewrite: H` is a
   syntax error, not ssreflect (the book's `rewrite: (eqP Eab)`, MCB
   Part III, cheat sheet, no longer parses).
6. `move=> {}h` introduces the goal's Top. On a goal with no premise it
   fails with `No assumption in …` (errors.md §7).
7. Checkpoints: put `have`s at paper-proof milestones (§8
   "Granularity"). Repair then restarts from the nearest `have`.

`{}h` / `{h}` are clear items, not the focusing braces §8 forbids.

```coq
From mathcomp Require Import all_boot.

Lemma refine_ex n (H : 0 < n) : 0 < n.+1 * n.
Proof.
(* WRONG: have {H}H : ...  -- warns [duplicate-clear,ssr] *)
have {}H : 0 < n.+1 * n by rewrite muln_gt0 H.
exact: H.
Qed.

Lemma cl a b (E : a = b) : a + 0 = b.
Proof.
Fail move=> {}E.            (* no premise on the goal to re-introduce *)
(* rewrite: E               -- syntax error, not ssreflect *)
by rewrite {}E addn0.       (* use E, then clear it *)
Qed.

Lemma keep (P : nat -> Prop) (H : forall n, P n) : P 1 /\ P 2.
Proof.
move: (H) => /(_ 1) h1.     (* (H) pushes a copy: H stays *)
by split; last exact: H.
Qed.
```

### 27.12 Instantiate lemmas as functions

A lemma is a function: apply it to arguments instead of adding steps
(MCB §3.3). §22.2 still applies: instantiate only to pin an occurrence
or to discharge a premise.

| Intent | WRONG | RIGHT |
|---|---|---|
| Pin a rewrite | `rewrite {2}addnC` (§8) | `rewrite (addnC n)` / `rewrite [n + _]addnC` |
| Use a hypothesis | `apply: prime_gt0; exact: p_pr` | `exact: prime_gt0 p_pr` (or `exact: prime_gt0`) |
| Chain | `apply: (leq_trans h1); exact: h2` | `exact: leq_trans h1 h2` / `exact: leq_trans h1 _` |
| Specialize in place | `have Hx := H x; clear H` | `move/(_ x) in H` / `move=> /(_ x) Hx` |
| Conditional rewrite | `have e := divnK d_dvd; rewrite e` | `rewrite (divnK d_dvd)` or `rewrite divnK //` |

- For a conditional rewrite, pick the form that leaves no side goal
  (§26.4). The explicit `(divnK d_dvd)` does not depend on side-goal
  order (§27.9).
- Intro views: `move=> /[dup] h /andP[a b]` keeps `h` and destructs a
  copy; `/[swap]` exchanges the two top premises; `/[apply]` applies the
  top premise to the next one (e.g. `boot/bigop.v:2697`).

```coq
From mathcomp Require Import all_boot.

Lemma inst_ex p n (p_pr : prime p) (h : forall m, m < p -> m < n) :
  0 < n.
Proof. by move/(_ 0 (prime_gt0 p_pr)): h. Qed.

Lemma rw_ex a b : a + (b + 3) = a + (3 + b).
Proof. by rewrite (addnC 3). Qed.

Lemma arg_ex p (p_pr : prime p) : 0 < p.
Proof. exact: prime_gt0 p_pr. Qed.

Lemma chain_ex m n p (h1 : m <= n) (h2 : n <= p) : m <= p.
Proof. exact: leq_trans h1 _. Qed.

Lemma spec_in (P : nat -> Prop) (H : forall x, P x) : P 2.
Proof. by move/(_ 2) in H. Qed.

Lemma div_ex d m (d_dvd : d %| m) : m %/ d * d + 0 = m.
Proof. by rewrite (divnK d_dvd) addn0. Qed.
```

---

## 28. Idiomatic Case Analysis

Mathcomp culture prefers reflection-style case analysis through
**dedicated lemmas** (`leqP`/`ltnP`/`ltngtP` on `nat`, `leP`/`ltgtP` on
ordered types, `eqVneq`, `altP`, etc.) rather
than ad-hoc `destruct` / `case` on raw inductive data. The dedicated
lemmas leave the **goal in equational form** so they can be chained.

### 28.1 The standard family

Pick the spec by the **carrier** of the comparison. A `nat` comparison
is a `leq` term (`m < n` is `m.+1 <= n`), so it takes the `n`-suffixed
specs (MCB §1.2.3, §1.7, §5.2.1).

**`nat`** (ssrnat, no extra import):

| Spec | Branches | Notes |
|------|----------|-------|
| `leqP m n` | `m <= n` / `n < m` | indices also rewrite `minn m n`, `maxn m n` (`boot/ssrnat.v:922`) |
| `ltnP m n` | `m < n` / `n <= m` | same `minn`/`maxn` indices (`boot/ssrnat.v:933`) |
| `posnP n` | `n = 0` / `0 < n` | spec `eqn0_xor_gt0` (`boot/ssrnat.v:941`) |
| `ltngtP m n` | `m < n` / `m > n` / `m = n` | three-way (`boot/ssrnat.v:953`) |
| `eqVneq x y` | `x = y` / `x != y` | any `eqType`, no boolean residual |

**Ordered types** (`orderType`, needs `Import Order.TTheory`; the header
of `order/order.v` names these its main case-analysis lemmas):

| Spec | Branches | Notes |
|------|----------|-------|
| `leP x y` | `x <= y` / `y < x` | total order; indices rewrite `min`/`max` |
| `ltP x y` | `x < y` / `y <= x` | total order |
| `ltgtP x y` | `x < y` / `x > y` / `x = y` | total order (a lattice is not enough) |
| `comparable_leP`, `comparable_ltgtP` | same, from `x >=< y` | `porderType` (`order/order.v:1866`) |

**Real domains:**

| Spec | Branches | Notes |
|------|----------|-------|
| `lerP x y` | `x <= y` / `y < x` | `realDomainType`; indices rewrite `min`, `max`, `` `\|x - y\| `` (`algebra/num_theory/numdomain.v:2654`) |
| `ltrP x y` | `x < y` / `y <= x` | `realDomainType` (`algebra/num_theory/numdomain.v:2658`) |
| `ltrgtP x y` | three-way | `realDomainType` (`algebra/num_theory/numdomain.v:2662`) |
| `real_leP`, `real_ltgtP` | same | `numDomainType` with side conditions `x \is real`, `y \is real` (`algebra/num_theory/numdomain.v:683`) |

**Other:**

| Lemma / view | Use case |
|--------------|----------|
| `eqP` | turn `a = b` proofs into `a == b` (decidable equality) |
| `altP P` | branch on `P` vs `~~ P`, with reflect-style residual |
| `posnumP x` | get a `{posnum R}` from `0 < x` |
| `ifP` / `ifPn` / `boolP b` | split an `if` or an arbitrary `bool` (phrasebook.md §3) |

**WARNING -- ssrnat's `leP` / `ltP` are not case splits.**
`leP m n : reflect (m <= n)%coq_nat (m <= n)` (`boot/ssrnat.v:500`) and
`ltP` (`boot/ssrnat.v:520`) are **bridges to Stdlib `le`/`lt`**.
- With ssrnat alone, `case: leP` on `m <= n` leaves branches with
  `(m <= n)%coq_nat` / `~ (m <= n)%coq_nat` hypotheses.
- Under `Import Order.TTheory` (the §5 preamble), `leP` is Order's lemma,
  and `case: leP` on a `nat` goal fails with `Pattern (leP _ _) was not
  completely instantiated ...`.
- For the Stdlib bridge, write the qualified `move/ssrnat.leP` /
  `apply/ssrnat.ltP` whenever `Order.TTheory` is imported (§49.8).

```coq
From mathcomp Require Import all_boot all_order.
Import Order.TTheory.

Lemma leq_or_gt m n : (m <= n) || (n < m).
Proof. by case: leqP. Qed.

Lemma cmp3 m n : (m < n) || (m == n) || (n < m).
Proof. by case: ltngtP. Qed.

(* WRONG: `leP` is Order's lemma here, it does not match a nat `leq` *)
Lemma leq_or_gt' m n : (m <= n) || (n < m).
Proof. Fail case: leP. by case: leqP. Qed.

(* Stdlib bridge: qualify when Order.TTheory is imported *)
Lemma to_coq m n : m <= n -> (m <= n)%coq_nat.
Proof. by move/ssrnat.leP. Qed.
```

**Why specs, and pinning the occurrence** (MCB §5.2.1 for the basic
`leqP` behaviour and point 3; MCB Part III, cheat sheet for
`case: (leqP m n)`. The `minn`/`maxn`/`lerP` indices, the `boolP`
comparison and point 2 are not from the book):

1. A spec's indices abstract **every** occurrence of `m <= n`, `n < m`,
   `minn m n` and `maxn m n` in the goal (for `lerP`, also `min`, `max`,
   `` `|x - y| ``), so one `case:` simplifies the whole goal. Prefer it
   over `case: (boolP (m <= n))`.
2. The rewriting reaches **only the goal**. Push hypotheses that mention
   the comparison first: `move: h; case: leqP`, or `case: leqP h`.
3. A bare `case: specP` unifies the index with the **first** matching
   subterm, in rewrite order. On `m <= maxn m n` it matches the whole
   goal and leaves `maxn m n < m -> false`. With several comparisons or
   `&&`s, pass the arguments (`case: (leqP m n)`), or pin by pattern
   with the view-pattern form `case: (a && _) / andP`.
4. `have [..] := leqP` without arguments is legal (`subn_if_gt`,
   `boot/ssrnat.v:968`). The **explicit arguments** pin the occurrence,
   not the `have` placement: write `have [le_mn | lt_nm] := leqP m n`.

```coq
From mathcomp Require Import all_boot.

Lemma minn_leq a b : a <= b -> minn a b = a.
Proof. by case: leqP. Qed.

Lemma maxn_ifE a b : maxn a b = if a < b then b else a.
Proof. by case: ltnP. Qed.

(* comparison living in a hypothesis: push it first *)
Lemma minn_leq' a b (h : a <= b) : minn a b = a.
Proof. by move: h; case: leqP. Qed.

Lemma le_maxn m n : m <= maxn m n.
Proof.
(* WRONG: case: leqP.  matches `m <= maxn m n` itself *)
Fail by case: leqP.
by case: (leqP m n) => [h|/ltnW].
Qed.
```

```coq
(* WRONG -- manual case analysis *)
case: (eqVneq x y) => Hxy.
  rewrite Hxy ...
case: (eqVneq x y) => Hxy.
  by ...

(* RIGHT -- chained with intro patterns *)
case: (eqVneq x y) => [-> | xy_neq].
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

Design rules:

- **Indices, not fields.** Every expression that each branch should
  replace by its value (`m < n`, `minn m n`, ...) is an **index** of the
  Variant's result type, and the lemma states it in index position.
  `case: fooP` then rewrites it in the goal. An equation field
  (`of b = true`) forces a manual rewrite (MCB §5.2.1).
- **Constructor names** are CamelCase `<Spec><Case>`: `CompareIntLt`,
  `UbnGeq`, `LeqNotGtn` (library practice, not from the book).
- **`of` sugar.** `C x of P x & Q x` declares anonymous proof arguments
  (example in MCB §5.3).
- **`Arguments fooP {x y}` is optional.** Library specs (`leqP`, `ltnP`,
  `ltngtP`) declare none. A bare `case: leqP` still works because
  ssreflect inserts evars (mind the occurrence rule in §28.1). This is
  library practice; MCB §5.2.1 recommends tuning spec implicits.
- **Spec over definition.** When a definition's own `match` looks like
  the case split you need, first look for (or write) a spec lemma, and
  drive the proof by it instead of unfolding (MCB §5.2.1, R box).

Library analogue: `posnP` over `eqn0_xor_gt0` (`boot/ssrnat.v:937`).
A minimal user spec:

```coq
From mathcomp Require Import all_boot.

Variant sign_spec (n : nat) : bool -> bool -> Set :=
  | SignZero of n = 0 : sign_spec n true false
  | SignPos of 0 < n : sign_spec n false true.

Lemma signP n : sign_spec n (n == 0) (0 < n).
Proof. by case: n => [|n]; constructor. Qed.

Lemma sign_use n : (n == 0) || (0 < n).
Proof. by case: signP. Qed.
```

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

**The six selector forms** (MCB Part III, cheat sheet "Rewrite
patterns"). The book does not cover `set` or `under` with these
patterns; both take them.

| Form | What is rewritten | Example: before → after |
|---|---|---|
| `[p]L` | `L`'s redex, inside every instance of `p` | `[a + 0]addn0`: `a + 0 + (b + 0)` → `a + (b + 0)` |
| `[in p]L` | first `L` redex found inside `p` | `[in RHS]addnC`: `a + b = b + a` → `a + b = a + b` |
| `[X in p]L` | exactly the subterm at hole `X` of `p` | `[X in _ + X]addn0`: `a + 0 + (a + 0)` → `a + 0 + a` |
| `[in X in p]L` | first `L` redex found inside hole `X` | `[in X in _ + X = _]addnC`: `a + (b + c) = _` → `a + (c + b) = _` |
| `[e in X in p]L` | `e` (overrides the inferred redex), inside `X` | `[a in X in f _ X]E` (`E : a = c`): `f a (a + a)` → `f a (c + c)` |
| `[e as X in p]L` | hole `X` of the instance of `p[X := e]` | `[_ + 0 as X in X + _]addn0`: `a + 0 + (a + 0)` → `a + (a + 0)` |

```coq
From mathcomp Require Import all_boot.

Lemma p_sel a b : a + 0 + (b + 0) = a + b.
Proof. by rewrite [a + 0]addn0 addn0. Qed.

Lemma in_sel a b : a + b = b + a.
Proof. by rewrite [in RHS]addnC. Qed.

Lemma X_sel a b : a + 0 = b -> a + 0 + (a + 0) = b + a.
Proof. by move=> E; rewrite [X in _ + X]addn0 E. Qed.

Lemma inX_sel a b c : a + (b + c) = a + (c + b).
Proof. by rewrite [in X in _ + X = _]addnC. Qed.

Lemma eX_sel (f : nat -> nat -> nat) a c (E : a = c) :
  a + f a (a + a) = f a (c + c) + a.
Proof. by rewrite [a in X in f _ X]E addnC. Qed.

Lemma asX_sel a b (E : a = b) : a + 0 + (a + 0) = b + b.
Proof. by rewrite [_ + 0 as X in X + _]addn0 E addn0. Qed.
```

**How an instance is chosen (keyed matching)** (MCB §2.4.1; MCB
Part III, cheat sheet, "Pattern matching detailed rules"):

1. The key is the head symbol of the pattern (or of `L`'s LHS).
2. The goal is scanned outside-in, left to right, for that key.
3. At each key occurrence, the arguments are matched up to conversion.
4. The first success fixes the instance.
5. Every copy of that instance is rewritten; copies are also compared
   up to conversion.

Consequences:

- `rewrite` never finds a redex that exists only **by computation**
  under another head. `n <= n` is `n - n == 0` by definition, yet
  `rewrite subnn` fails on it. Expose the key first (`rewrite /leq`,
  `-[t]/(t')`, §29.8) or use `apply:`/`exact:`.
- `m < n` is notation for `m.+1 <= n`: same term, key `leq`, so
  `<`-lemmas and `.+1 <=`-lemmas match each other.
- `apply:`/`exact:` unify the whole conclusion up to conversion:
  `exact: leqnn` closes `a.+1 + b <= (a + b).+1`.
- A selected copy can be a term that only *reduces* to the instance.
  Pin the occurrence with a context pattern: `set n := (X in X + _)`.

```coq
From mathcomp Require Import all_boot.

Lemma key_hidden n : n <= n.            (* leq n n is n - n == 0 *)
Proof. Fail rewrite subnn. by rewrite /leq subnn. Qed.

Lemma leq_ex a b : a.+1 + b <= (a + b).+1.
Proof. exact: leqnn. Qed.               (* unifies up to conversion *)

Lemma set_copy a b : a + b + (0 + a + b) = 2 * (a + b).
Proof.
set n := (_ + b).       (* goal n + n = 2 * n: 0 + a + b was caught too *)
by rewrite mul2n addnn.
Qed.
```

### 29.3 `!` for repeated, `?` for optional

| Form | Meaning |
|------|---------|
| `rewrite L` | rewrite once; fails if no match |
| `rewrite ?L` | rewrite if applicable; never fails |
| `rewrite !L` | rewrite as many times as possible; fails if zero |
| `rewrite 2!L` | rewrite exactly twice |
| `rewrite -L` | rewrite right-to-left |
| `rewrite L1 L2 // L3` | discharge intermediate trivial subgoals |
| `rewrite 3?L` | rewrite 0 to 3 times |
| `rewrite {}h` | rewrite with hypothesis `h`, then clear it (§27.11) |
| `rewrite /=` | simplify with `simpl` (see §29.9) |

The `{}` in `rewrite {}h` is a clear item, not the focusing braces
banned in §8.

**Fail early and locally** (MCB §4.3.2). `?L` never fails, so it moves
the breakage of a proof to a later, unrelated line.

- Use `?` only on rules that serve **side conditions**, immediately
  followed by `//`. Main-goal rewrites stay plain (or `!`), so they
  fail on the line that broke.
- WRONG `rewrite L1 ?L2 ?L3 //.` / RIGHT `rewrite L1 ?L2 // L3.`
- Never add `?` to silence "nothing to rewrite": the goal is not what
  you think. Inspect it.

```coq
From mathcomp Require Import all_boot.

(* RIGHT: the ?-rules only serve mulnK's side condition 0 < a * b and *)
(* are closed by //; the main-goal rewrite addn0 stays strict.        *)
Lemma fe3 m a b : 0 < a -> 0 < b -> m * (a * b) %/ (a * b) + 0 = m.
Proof. by move=> a_gt0 b_gt0; rewrite mulnK ?muln_gt0 ?a_gt0 // addn0. Qed.
(* WRONG: rewrite mulnK ?muln_gt0 ?a_gt0 ?addn0 //.                   *)

Lemma cl a b (E : a = b) : a + 0 = b.
Proof. by rewrite {}E addn0. Qed.       (* E is gone after the rewrite *)
```

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

Destruct a hypothesis equation between constructors (`n.+1 = m.+1`,
`x :: s = y :: t`) with `case=> ->`, `move=> [->]` or
`move/succn_inj`, not `injection`. An absurd one (`n.+1 = 0`) closes
with `by []` (phrasebook §1, §12).

### 29.8 Conversion steps inside `rewrite`

These steps use no lemma: the new goal must be convertible to the old
one (MCB §2.4, §2.4.1, §5.4; MCB Part III, cheat sheet; the
`-[t in LHS]/(t')` row is not shown in the book).

| Form | Effect |
|---|---|
| `/d` | unfold every occurrence of `d` (a δ step) |
| `/(pat)` | unfold only instances of `pat`: `rewrite /(_ && _)` |
| `[p]/d` | unfold `d` only inside the subterms selected by `p`: `rewrite [LHS]/leq` |
| `-/d`, `-/(d _ _)` | fold back to `d`; give the folded shape: `rewrite -/(leq _ _)` |
| `-[t]/(t')` | replace `t` by the convertible `t'` (the ssreflect `change`) |
| `-[t in LHS]/(t')` | same, restricted by a context pattern |

Rules:

- Prefer these to `unfold`/`fold`, and to `have -> : t = t' by []` when
  `t` and `t'` are convertible (§22.1). `change` remains acceptable
  upstream. The gain is that these steps chain inside one `rewrite`
  and take context patterns.
- Only `-[t]/(t')` changes a term. Without `-`, `[p]/(t)` unfolds the
  head of `t` inside `p`: `rewrite [a.+1]/(1 + a)` leaves
  `(1 + a)%coq_nat`.
- Keep the selector small: a bare `-[m]` hits every occurrence of `m`.
- A non-convertible `t'` fails with
  `fold pattern (t') does not match redex (t)`. Example:
  `-[m ^ 2]/(m * (m * 1))` fails because `m * 1` does not compute, while
  `-[m ^ 2]/(m * m)` works. When in doubt, rewrite with lemmas
  (`expnS`, `muln1`).
- Conversion steps do not see through `HB.lock`ed or `locked` heads
  (`#|_|`, `\big`, finset operations, polynomials). Use their `*E` or
  `unlock` lemmas (§35.8, §40.10).

```coq
From mathcomp Require Import all_boot.

Lemma ex_unfold m n : (m <= n) = (m - n == 0).
Proof. by rewrite [LHS]/leq. Qed.                     (* [p]/d *)

Lemma ex_and b c : b && c = c && b.
Proof. by rewrite /(_ && _); case: b; case: c. Qed.   (* /(pat) *)

Definition K := 3.
Lemma ex_foldc : 3 + 3 = K + K.
Proof. by rewrite -/K. Qed.                           (* -/d *)

Lemma ex_foldleq m n : m - n == 0 -> m <= n.
Proof. by rewrite -/(leq _ _). Qed.                   (* -/(d _ _) *)

Lemma ex_fold n1 n2 : n1 <= n2 -> 0 + n1 <= n2.
Proof. by rewrite -[0 + n1]/n1. Qed.                  (* -[t]/(t') *)

Lemma fold_ex m d : m = 0 * d + m.
Proof. by rewrite -[m in LHS]/(0 * d + m). Qed.       (* restricted *)

Lemma lock_ex (T : finType) (A : {pred T}) : #|A| = size (enum A).
Proof. Fail rewrite -[#|A|]/(size (enum A)). by rewrite cardE. Qed.
```

**Controlled unfolding of recursive definitions** (MCB §5.4). For a
non-trivial `Fixpoint` or `fix`, state a one-step equation `fooE` /
`foo_recE` (usually proved `by case: n` or `by []`) and rewrite with
it. `/=` and `rewrite /foo` may expose the internal `fix`. Name the
equation after the head (§37.2).

```coq
From mathcomp Require Import all_boot.

Definition edivn_rec d :=
  fix loop m q := if m - d is m'.+1 then loop m' q.+1 else (q, m).

Lemma edivn_recE d m q : edivn_rec d m q =
  if m - d is m'.+1 then edivn_rec d m' q.+1 else (q, m).
Proof. by case: m. Qed.
```

### 29.9 `/=` and `simpl never` operators

- `addn`/`subn`/`muln`/`expn`/`factorial`/`double` are
  `simpl never`, and `leq` does not compute under `/=`: rewrite
  (`addSn`, `ltnS`, `eqSS`). Details and lemma table: §49.4.
- `//=` combines `/=` and `//` (MCB §2.4); it runs `/=` first, then
  tries `//` on the result.

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
Here `x y` live in an `orderType`, so `leP` is Order's lemma (§28.1). On
`nat` write `case: (leqP x y) => xy`; the intro names stay the same, and
the second branch gets `xy : y < x` (use `ltnW` for `y <= x`).

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

### 30.7 `have` / `suff` / `wlog`: choosing the cut

All three add a cut; pick the one whose shape matches the argument
(MCB §4.2.1, §4.2.2, §4.3.4).

| Use | When |
|---|---|
| `have n : S` | `S` is reused and its proof is short or naturally first |
| `have /view[pat] : S` | only the destructed content of `S` matters, e.g. `have /pdivP[p pr_p p_dv] : 1 < n.+2 by []` |
| `have lem x y : H -> C` | a symmetric sub-argument used in several branches; parameters go before `:` as in `Lemma` |
| `suff lem : S` | the reduction is the main message: prove the goal from `S` first, `S` last (the shortest paragraph) |
| `wlog h : x y / x <= y` | the cut would restate the whole goal; `wlog` builds it and generalizes the listed variables |
| `gen have lem, hx : x / P x` | you need both `lem : forall x, P x` (over the listed context variables) and the instance `hx : P x` (§30.2) |

Rules:

- **Never duplicate a proof script for symmetric branches.** State the
  branch once as a parameterised `have`/`suff` or a `wlog`, instantiate
  it in each branch, and finish the mirrored one with
  `; last rewrite fooC barC`.
- **The name slot of `have`/`suff` is an intro pattern.** Destruct at
  the cut instead of naming the fact and running `move/andP: h` on the
  next line.
- **`wlog h : vars / P => [hsym|]`**: the suffix only names the
  generalized hypothesis on the first goal. Without it, open that goal
  with `move=> hsym`. The second goal already has `h` in context.

```coq
From mathcomp Require Import all_boot.

Lemma have_view (P : pred nat) (a b c : nat) (h : P a && (b == c)) : b = c.
Proof.
(* WRONG: name the fact, then destruct it on the next line
   have hPbc : P a && (b == c) by [].
   move/andP: hPbc => [_ /eqP bc]. *)
(* RIGHT: the name slot of have is an intro pattern *)
by have /andP[_ /eqP->] : P a && (b == c) by [].
Qed.
```

The same symmetric argument, with `suff` and with `wlog`. The mirrored
branch is one `last rewrite`, not a copy of the proof:

```coq
From mathcomp Require Import all_boot.

(* suff + parameterised cut: reduction first, auxiliary proof last *)
Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
suff th_sym x y : y <= x -> (m <= maxn x y) = (m <= x) || (m <= y).
  by case: (orP (leq_total n2 n1)) => /th_sym; last rewrite maxnC orbC.
move=> le_yx; rewrite (maxn_idPl le_yx) orb_idr // => le_my.
exact: leq_trans le_my le_yx.
Qed.

(* wlog builds the same cut without restating the goal *)
Lemma leq_max' m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
wlog le_n21 : n1 n2 / n2 <= n1 => [th_sym|].
  by case: (orP (leq_total n2 n1)) => /th_sym; last rewrite maxnC orbC.
by rewrite (maxn_idPl le_n21) orb_idr // => /leq_trans->.
Qed.
```

`maxn_idPl` is `reflect (maxn m n = m) (m >= n)` with maximal implicits
`{m n}` (boot/ssrnat.v:768). `rewrite (maxn_idPl le)` still uses it as an
equation through the `elimT` coercion.

### 30.8 `set`, `pose`, and when not to extract a lemma

Keep a large proof readable with local names instead of forcing
top-level lemmas (MCB §4.3.4).

| Form | Effect |
|---|---|
| `set t := (pat).` | adds `t :=` the first instance of `pat` and abstracts every occurrence, convertible copies included (§29.2; MCB Part III, cheat sheet) |
| `set t := (X in _ = _ + X).` | context pattern: abstracts that position only; use it instead of numeric occurrences `{2 4}` (§8) |
| `set t := pat in h.` | abstracts in `h` only, goal untouched; `in h *` does both |
| `rewrite /t` / `rewrite -/t` | unfold `t` again / fold an instance back into `t` (MCB Part III, cheat sheet) |
| `pose f x := body.` | local definition not taken from the goal (goal untouched); unfold with `rewrite /f` |

```coq
From mathcomp Require Import all_boot.

Lemma setpose n : (n + 1) * (n + 1) = (n + 1) ^ 2.
Proof.
set k := n + 1.               (* every copy: k * k = k ^ 2 *)
by rewrite expnS expn1.
Qed.

(* goal adapted from MCB Part III, cheat sheet (set example) *)
Lemma st a b : (a + b) + (a + b) = (a + b) + (0 + a + b).
Proof.
(* set n := (a + b) gives n + n = n + n: it grabs 0 + a + b too *)
set n := (X in _ = _ + X).    (* one position: a + b + (a + b) = a + b + n *)
by [].
Qed.
```

```coq
From mathcomp Require Import all_boot.

Lemma set_in a b (h : a + b = 0) : (a + b) * (a + b) = 0.
Proof.
set t := (_ + b) in h.       (* h : t = 0;  goal unchanged *)
rewrite /t in h.             (* unfold: h : a + b = 0 (t stays defined) *)
set u := (_ + b) in h *.     (* h : u = 0;  goal : u * u = 0 *)
by rewrite h.
Qed.

Lemma pose_local n : n + n = n.*2.
Proof.
pose f x := x + x.           (* f := fun x => x + x;  goal unchanged *)
rewrite -/(f n).             (* fold by conversion: f n = n.*2 *)
by rewrite /f addnn.         (* unfold f *)
Qed.
```

Pitfall: `set` on a denominator hides it from `field` (§45.9).

**Extraction criterion** (counterweight to playbook.md "Extract a
reusable algebraic identity to a top-level lemma"):

- Extract a top-level `Lemma` only when the statement is self-contained:
  few hypotheses and a result you can name.
- Otherwise keep it local: `have lem params : …`, `suff` or `wlog`
  (§30.7), or `gen have` (§30.2). Restating a large context as
  hypotheses gives a lemma that is hard to name, state and reuse.

---

## 31. Maximal Implicits and `Arguments` Discipline

### 31.1 Maximal implicits

A trailing implicit argument (no explicit argument after it) must be
declared with **braces**. Square brackets denote *non-maximal*
implicits (§25.5); on a trailing position Rocq 9.1 rejects them with
`Error: Argument T is a trailing implicit, so it can't be declared non
maximal. Please use { } instead of [ ].` Non-trailing `[x]` is legal.

```coq
From mathcomp Require Import all_boot.
Definition bar (x : nat) (T : Type) := x.
(* WRONG -- Error: Argument T is a trailing implicit ... *)
Fail Arguments bar _ [T].

(* RIGHT -- braces make the trailing implicit maximal *)
Arguments bar _ {T}.
```

Reviewers (math-comp PR #447) consistently push for braces on
implicits that must be filled even when the function is partially
applied.

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
Definition is_normal_pdf (x : R) : R := ...

(* RIGHT -- operator name; binders left of := (§32.5) *)
Definition normal_pdf (x : R) : R := ...
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
Lemma foo_pos v : 0 < v -> 0 < norm v.

(* STRONGER, prefer when both directions hold *)
Lemma foo_norm_neq0 v : (0 < norm v) = (v != 0).
```
(math-comp PR #1333)

When the equivalence holds, rephrase. Prefer **bidirectional**
statements; reviewers consistently push for this generalization.

Which side is the LHS, which variables it must contain, pivot-first
binder order, `exists2` over `/\`: §37.13.

### 32.5 Definition bodies: mathcomp Gallina style

Write bodies the way `boot/` does (MCB §1.1.1-1.1.2, §1.2.2-1.2.3,
§1.3.1, §1.3.3-1.3.4, §1.4, §1.5, §3.5; items 4 and 8, `n.+1` over
`n + 1`, `fooE`, `simpl never` and `HB.instance` are library practice,
not from the book):

1. **Binders left of `:=`:** `Definition f (n : nat) := …`, never
   `Definition f := fun n => …`. Share annotations: `(m n : nat)`; omit
   those `Implicit Types` already fixes (§16, §24.5). A result type is
   optional (boot mostly omits it); state it when it documents intent.
2. **Two-way match: `if x is C a then … else …`.** Irrefutable pattern
   (pair, record): `let: (a, b) := p in …`. Use `match … with … end`
   only for 3+ branches. Branches are tried top-down and the first match
   wins, so put `0`/`1` before a `_` catch-all.
3. **nat postfix notations:** `n.+1`, `n.+2`, `n.-1`, `n.*2`, `n./2`.
   Never `S n`, `pred n`, `Nat.succ`. In statements prefer `n.+1` to
   `n + 1`: `ltnS`, `addnS`, `big_ord_recr` are stated with `.+1`, and
   `n + 1` needs `rewrite addn1` first. `n.-1.+1 = n` holds only under
   `0 < n` (mathcomp/boot/ssrnat.v, `prednK` (l. 350)). Notation table:
   §49.1.
4. **Decidable predicates are `bool`-valued** (`pred T`, `rel T`), so
   `==`, `&&`, `[&& …]` and views apply (§36.7).
5. **Keep functions total.** Lookups take a default (`nth x0 s i`,
   `head x0 s`; §49.5). Return `option T` only when absence is
   information the caller must branch on.
6. **Reuse before recursing:** `iter`, `foldr`, `map`/`filter`, bigops.
   A new `Fixpoint` peels the constructor at the top of the body so
   `simpl` makes progress. Pair it with a one-step `fooE` equation
   (§29.8). If users should not see the unfolding, add
   `Arguments foo : simpl never` (§31.5). Termination / `ill-formed`
   errors: errors.md §8.
7. **More than two components: a `Record`**, never nested tuples such
   as `(3, true, 4).1.2`. One `HB.instance` line equips it (§36.12).
8. **Sanity-check with `Compute`** on 2-3 small inputs (§37.12).
   `Compute` stops at `\big[…]` because the bigop head is locked
   (mathcomp/boot/bigop.v, `bigop` (l. 588)). Test bigop-based
   definitions with a small lemma instead.

```coq
From mathcomp Require Import all_boot.

(* WRONG: binder hidden behind fun *)
Definition dbl_bad := fun n => n + n.
(* RIGHT: binders left of := *)
Definition dbl (n : nat) : nat := n + n.

(* two-way match: if-is; irrefutable pattern: let: *)
Definition pred2 (n : nat) : nat := if n is p.+2 then p else 0.
Definition swap (A B : Type) (p : A * B) : B * A :=
  let: (a, b) := p in (b, a).
Definition first_odd (s : seq nat) : option nat :=
  if [seq x <- s | odd x] is x :: _ then Some x else None.

(* 3+ branches: match; first matching branch wins *)
Definition small (n : nat) : nat :=
  match n with 0 => 0 | 1 => 1 | _.+2 => 2 end.

Lemma pred_succ n : 0 < n -> n.-1.+1 = n.
Proof. exact: prednK. Qed.
(* WRONG: n + 1 blocks ltnS / addnS-shaped lemmas *)
Lemma le_succ_bad m n : m <= n -> m < n + 1.
Proof. by rewrite addn1 ltnS. Qed.
(* RIGHT: state with .+1 *)
Lemma le_succ m n : m <= n -> m < n.+1.
Proof. by rewrite ltnS. Qed.
```

Iterators, recursion with `fooE`, records, `Compute`:

```coq
From mathcomp Require Import all_boot.

(* reuse an iterator before writing a Fixpoint *)
Definition pow2 (n : nat) : nat := iter n double 1.
Definition sum_sq (s : seq nat) : nat := \sum_(x <- s) x ^ 2.

(* recursion: peel the constructor at the top, pair with fooE *)
Fixpoint tri (n : nat) : nat := if n is m.+1 then n + tri m else 0.
Lemma triE n : tri n.+1 = n.+1 + tri n.
Proof. by []. Qed.
Arguments tri : simpl never.

(* 3+ components: a Record, not (3, true, 4).1.2 *)
Record cell := Cell { row : nat; col : nat; alive : bool }.
Definition shift (c : cell) : cell :=
  let: Cell r k a := c in Cell r k.+1 a.

(* sanity-check on small inputs *)
Compute (pow2 3, tri 4).          (* = (8, 10) *)
Compute col (shift (Cell 0 3 true)). (* = 4 *)
(* bigops are locked: Compute stops at \big[..]; test with a lemma *)
Lemma sum_sq12 : sum_sq [:: 1; 2] = 5.
Proof. by rewrite /sum_sq big_cons big_seq1. Qed.
```

### 32.6 Declaring new notations

(MCB §1.7 for items 2-4 and the symbol shapes; MCB §1.3.3 for item 6.
Items 1, 5, 7 and `Print Notation` are not from the book.) For
precedence changes to existing notations see §6.3.

1. `Reserved Notation "x <op> y" (at level L, assoc).` goes at the top
   of the file (§2 step 5). The `Notation … : scope` line comes after
   the `Definition`. Always attach a scope.
2. Reuse the level and associativity of an analogous notation, found
   with `Print Notation "_ + _".` or `Locate "+".`:

   | Kind | Level / associativity | Examples |
   |---|---|---|
   | additive | 50, left | `+`, `-` |
   | multiplicative | 40, left | `*` |
   | relation | 70, no associativity | `<=`, `<`, `==` |

3. Put spaces around the symbol in the string. The string is split on
   spaces into tokens, so `"m<+>n"` is one token and `m`, `n` are
   unbound.
4. Input-only aliases take `(only parsing)` (ssrnat's `>`, `>=`). Goals
   print the canonical form, so write statements, `Search` and rewrite
   patterns in the **printed** form (`0 < n`, never `n > 0`): the source
   then reads like the goal.
5. Use `Local Notation` for section- or file-private shorthands.
6. `*` is both nat product and pair type. Add `%type` or `%N` only when
   the surrounding scope is wrong (§22.3).
7. `notation-overridden` on your own `Notation` line is a real clash:
   change symbol or scope (on mathcomp's `Require Import` it is harmless).

Symbol shapes that look native:

| Shape | Meaning | Examples |
|---|---|---|
| leading `.` | postfix operator | `n.+1`, `n.*2`, `p.-group G` |
| leading `'` | letter-like concept | `'N(G)`, `'C(A)` |
| `'X_` subscript | subscripted argument | `'I_n`, `'N_G(H)` |
| leading `\` | LaTeX-like operator | `\sum_(i < n)`, `x \in A` |
| `[op …]` | n-ary / data builders | `[seq …]`, `[&& a, b & c]` |
| `{…}` | parameterized types, localized statements | `{poly R}`, `{in A, P}` |

```coq
From mathcomp Require Import all_boot.

Print Notation "_ + _".     (* at level 50, left associativity *)

(* top of file, after the header setup *)
Reserved Notation "m <+> n" (at level 50, left associativity).

Definition oplus (m n : nat) := m + n.+1.
(* no spaces: "m<+>n" is ONE token, so m and n are unbound *)
Fail Notation "m<+>n" := (oplus m n) : nat_scope.
Notation "m <+> n" := (oplus m n) : nat_scope.

Lemma oplus0n n : 0 <+> n = n.+1.
Proof. by rewrite /oplus add0n. Qed.

Local Notation sq n := (n * n).   (* file-private shorthand *)

Check (nat * bool)%type.    (* pair type, not nat product *)
Check (forall n, n > 0 -> n.-1.+1 = n). (* prints 0 < n *)
```

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
| `big_nat_recr` (l. 1927) | `m <= n -> \big_(m <= i < n.+1) F i = \big_(m <= i < n) F i * F n`; needs `op : Monoid.law idx`, whereas `big_nat_recl` takes any `op` |
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
| outer pair-product | `big_distrlr` |
| product of sums | table below |
| arbitrary morphism | `big_morph` (or `big_endo` if same monoid) |

Product of sums (mathcomp/boot/bigop.v, `big_distr_big_dep` (l. 2421),
`big_distr_big` (l. 2451), `bigA_distr_big_dep` (l. 2459),
`bigA_distr_big` (l. 2475), `bigA_distr_bigA` (l. 2480)):

| Shape | Lemma: right-hand side |
|---|---|
| `\prod_(i : I) \sum_(j : J) F i j` over finTypes | `bigA_distr_bigA`: `\sum_(f : {ffun I -> J}) \prod_i F i (f i)` |
| inner sum filtered by `Q j` | `bigA_distr_big`: `\sum_(f in ffun_on Q)` |
| inner filter depends on `i` (`Q i j`) | `bigA_distr_big_dep`: `\sum_(f in family Q)` |
| product over a set `P`, default `j0` | `big_distr_big(_dep) j0`: `\sum_(f in pffun_on j0 P Q)` / `(f in pfamily j0 P Q)` |

The law needs a `Monoid.mul_law`/`add_law` pair, so it works for
`\prod`/`\sum` over a commutative semiring. `rewrite bigA_distr_bigA`
expands, `rewrite -bigA_distr_bigA` factors.

```coq
From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma prod_sum (R : comPzRingType) (I J : finType) (F : I -> J -> R) :
  \prod_i \sum_j F i j = \sum_(f : {ffun I -> J}) \prod_i F i (f i).
Proof. exact: bigA_distr_bigA. Qed.
```

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

**Peel a nat range** (MCB §6.7.1). Range lemmas match only an
**unfiltered** range. Use `big_mkcond` to move the filter into the body
(`if P i then F i else idx`), peel, then restore the filter with
`-big_mkcond`.

| Range | Peel with |
|-------|-----------|
| `(m <= i < n.+1)` | `rewrite big_nat_recr //` (last index; side goal `m <= n`), `big_nat_recl //` (first) |
| `(m <= i < n.+1 \| P i)` | `rewrite big_mkcond big_nat_recr //= -big_mkcond` |
| `(m <= i < n.+1 \| P i && Q i)`, move only `Q` | `big_mkcondr` (`big_mkcondl` moves `P`) |
| `(i < n.+1)` (ordinal) | `big_ord_recr` / `big_ord_recl`, not `big_nat_rec*` |
| `(n <= i < n.+1)` | `big_nat1` |

```coq
From mathcomp Require Import all_boot.

Lemma sum_peel n : \sum_(0 <= i < n.+1) i = \sum_(0 <= i < n) i + n.
Proof. by rewrite big_nat_recr. Qed.

Lemma sum_odd_peel n : \sum_(0 <= i < n.+1 | odd i) i =
  \sum_(0 <= i < n | odd i) i + (if odd n then n else 0).
Proof. by rewrite big_mkcond big_nat_recr //= -big_mkcond. Qed.
```

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

To *find* a bigop lemma, search by name substring (`"big"` plus
`"rec"`, `"cond"`, `"ind"`, `"exchange"`), not by a concrete `\sum`
pattern. See the bigop recipe in §37.11 (MCB §6.7.3).

To *find* bigop lemmas by these families, use the recipe in §37.11.

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

**Append `/=` after a generic bigop rewrite** (MCB §6.9). After
`big_cat`, `big_split`, `bigID` or `big_mkcond` on a nat or ring
operator, the goal shows the law projection instead of the operator
(`ssrnat_addn__canonical__Monoid_Law (…) (…)` for `addn`,
`Algebra.Algebra_add__canonical__Monoid_Law R (…) (…)` for `+%R`).
`rewrite addnC` / `addrC` then fails with "The LHS of addnC … does not
match any subterm" (mathcomp 2.5 behaviour; the book's own MCB §6.9 proof
rewrites `addnC` without `/=`). This is a display and unification artifact, not a
type error. Any `<prefix>_<op>__canonical__…` head in the goal means
you must insert `/=` before the next rewrite, or pin the occurrence
(`rewrite [LHS]addnC`).

```coq
From mathcomp Require Import all_boot.

(* adapted from MCB §6.9 *)
Lemma sum_catC (l1 l2 : seq nat) F :
  \sum_(i <- l1 ++ l2) F i = \sum_(i <- l2 ++ l1) F i.
Proof.
rewrite big_cat.
(* goal: ssrnat_addn__canonical__Monoid_Law (\big[...]...) (...) = ... *)
Fail rewrite addnC.          (* The LHS of addnC ... does not match *)
by rewrite /= addnC -big_cat. (* RIGHT: /= first; or [LHS]addnC *)
Qed.
```

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
    -> rewrite big_nat_recr //  (m <= i < n.+1; filtered range: §34.5)

  Two nested bigops, swap order?
    -> rewrite exchange_big

  Pull a function out?
    -> rewrite raddf_sum / rmorph_sum / mulr_suml / mulr_sumr / ...
       (named alias FIRST; big_morph only as a last resort)

  Reduce to seq concat / map / filter?
    -> big_cat, big_map, big_filter, big_filter_cond

  A bigop lemma does not fire on a custom operator?
    -> declare its Monoid law (§34.10); never unlock bigop
```

### 34.10 Custom operators: declaring Monoid laws

Generic bigop lemmas take the operator as a **law structure** that is
keyed on the operator constant (MCB §6.7.2, §8.2). If the operator has
no law, the lemma does not fire. The HB structures and factories live
in `mathcomp/boot/bigop.v` (`Module SemiGroup`, `Module Monoid`).
`boot/monoid.v` is the unrelated Magma/Semigroup/Monoid *type*
hierarchy.

**Which law each lemma family needs** (mathcomp 2.5):

| Law on `op` | Lemmas |
|-------------|--------|
| none (any `op : R -> R -> R`) | `eq_bigr`, `big_nat_recl`, `big_ord_recl` |
| `Monoid.law idx` (assoc, two-sided identity) | `big_cat` (l. 1817), `big_mkcond` (l. 1786), `big_nat_recr` (l. 1927), `big_ord_recr` |
| `SemiGroup.com_law R` (assoc, comm, **no** identity) | `bigD1` (l. 1389), `reindex` (l. 1446) |
| `Monoid.com_law idx` | `bigID`, `big_split`, `exchange_big`, `pair_big`, `partition_big` (the `Abelian` section) |
| `Monoid.mul_law zero` + `Monoid.add_law zero times` | `big_distrl` (l. 2408), `big_distr_big` (l. 2451) |

Consequence: `big_split`, `bigID` or `exchange_big` on a `\prod` needs
`R : comPzSemiRingType`. On a `pzRingType` they fail to match.

**Factories and mixins** (argument order checked against the source):

| Axioms you have | `HB.instance Definition _ :=` | Site |
|-----------------|-------------------------------|------|
| assoc + left/right identity | `Monoid.isLaw.Build T idx op opA op1x opx1` | `boot/bigop.v:414` |
| assoc + comm + left identity | `Monoid.isComLaw.Build T idx op opA opC op1x` | `boot/bigop.v:432` |
| assoc + comm, no identity | `SemiGroup.isComLaw.Build T op opA opC` | `boot/bigop.v:356` |
| left/right zero of `times` | `Monoid.isMulLaw.Build T zero times op0x opx0` | `boot/bigop.v:447` |
| `times` distributes over `plus` | `Monoid.isAddLaw.Build T times plus opDl opDr` | `boot/bigop.v:456` |

`isAddLaw` is keyed on the **added** operator, which must already be a
`Monoid.com_law zero` (`isAddLaw.Build nat muln addn mulnDl mulnDr`,
`boot/bigop.v:545`).

**Existing instances. Do not redeclare these:**

| Operator | Laws | Site |
|----------|------|------|
| `andb`, `orb`, `addb` | `com_law`; `andb`, `orb` also `mul_law`; all three `add_law` | `boot/bigop.v:532` |
| `addn`, `muln`, `maxn`, `gcdn`, `lcmn` | `com_law`; `muln` `mul_law 0`; the others `add_law _ muln` | `boot/bigop.v:542` |
| `cat` | `law [::]` | `boot/bigop.v:556` |
| `+%R` (`nmodType`) | `com_law 0` | `boot/nmodule.v:398` |
| `*%R` | `law 1`, `mul_law 0` (`+%R` its `add_law`); `com_law 1` only on `comPzSemiRingType` (`algebra/ssralg.v:2974`) | `algebra/ssralg.v:1070` |
| `setI`, `setU` | `com_law`, `mul_law`, `add_law` | `boot/finset.v:1069` |
| `*%g` (`monoidType`) | `law 1` | `boot/monoid.v:364` |

Rules:

- State the operator as a named `Definition`. Prove each axiom as a
  named lemma with the §11/§12 names (`bxorA`, `bxorC`, `bxorFb`). Then
  write one `HB.instance` line with the weakest factory that covers the
  lemmas you need.
- Check first with `HB.about op`: it lists `Monoid.Law`,
  `Monoid.ComLaw`, … or fails with "uninteresting constant". Re-declaring
  prints "HB: no new instance is generated"; the
  `redundant-canonical-projection` warnings on a new law are harmless.
- Do not test with `Check (op : Monoid.com_law idx)`: it succeeds through
  delta/eta even on a binder alias whose `rewrite` still fails.

**Pitfall: delta alias vs. binder alias.**

- A plain delta alias (`Definition myadd := addn.`) inherits `addn`'s
  laws by unfolding, and `rewrite big_cat` works.
- A `Definition` with binders (`Definition ad a b := a + b.`) has no
  law of its own, even when its body is a known operator: `rewrite
  big_cat` / `big_split` fails with "The LHS of big_cat … does not
  match". Declare the instance, or instantiate the law explicitly,
  `rewrite (big_cat (ad : Monoid.law 0))`. Never `unlock` bigop (§34.1).

```coq
From mathcomp Require Import all_boot.
From HB Require Import structures.

Definition myadd := addn.                (* delta alias: inherits laws *)
Lemma myadd_cat (s1 s2 : seq nat) :
  \big[myadd/0]_(i <- s1 ++ s2) i =
  myadd (\big[myadd/0]_(i <- s1) i) (\big[myadd/0]_(i <- s2) i).
Proof. by rewrite big_cat. Qed.

Definition ad (a b : nat) := a + b.      (* binders: no law of its own *)
Lemma ad_cat (s1 s2 : seq nat) :
  \big[ad/0]_(i <- s1 ++ s2) i =
  ad (\big[ad/0]_(i <- s1) i) (\big[ad/0]_(i <- s2) i).
Proof.
Fail rewrite big_cat.                    (* LHS of big_cat ... not match *)
by rewrite (big_cat (ad : Monoid.law 0)). (* or declare an instance *)
Qed.

(* Declaring a commutative law for a new operator. *)
Definition bxor (a b : bool) := a (+) b.
Lemma bxorA : associative bxor. Proof. exact: addbA. Qed.
Lemma bxorC : commutative bxor. Proof. exact: addbC. Qed.
Lemma bxorFb : left_id false bxor. Proof. exact: addFb. Qed.
HB.instance Definition _ :=
  Monoid.isComLaw.Build bool false bxor bxorA bxorC bxorFb.

Lemma bxor_split (F G : 'I_3 -> bool) :
  \big[bxor/false]_(i < 3) bxor (F i) (G i) =
  bxor (\big[bxor/false]_(i < 3) F i) (\big[bxor/false]_(i < 3) G i).
Proof. by rewrite big_split. Qed.
```

Sources: `mathcomp/boot/bigop.v` (file header lines 7-100; lemma
sites cited in 34.2 above; law mixins and factories `boot/bigop.v:340`
through `boot/bigop.v:462`; pervasive instances `boot/bigop.v:532`
through `boot/bigop.v:556`); `mathcomp/algebra/ssralg.v` (`mulr_suml`
l. 1076, `mulr_sumr` l. 1080, `rmorph_sum` l. 2324, `rmorph_prod`
l. 2338); math-comp PR #965 (`under` discipline); PR #682
("reformulate to the most general bigop form"); PR #517
(`_l` / `_r` suffixes); the MathComp book (pre-HB, see §48):
(MCB §6.7, §6.9) for big operators and (MCB §8.2) for Monoid laws. The
named-distribution-lemma rule was re-stated in math-comp/analysis
review threads on PRs #1230 and #1340.

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
| `Check (T : eqType).` / `Check (op : Monoid.com_law idx).` | Succeeds when unification finds an instance, possibly after unfolding. Replaces the book's `[eqType of T]` / `[law of op]` (MCB §6.10.2), now syntax errors (§48). So an alias passes too, even a binder alias (`ad a b := a + b`) whose `rewrite big_cat` fails; `HB.about op` tells whether `op` itself carries the instance (§34.10). |
| `HB.about addn.` | Works on operators as well as types. Output: `Monoid.Law SemiGroup.Law Monoid.ComLaw SemiGroup.ComLaw (from "./bigop.v", line 542)` and `Monoid.AddLaw (from "./bigop.v", line 545)`, i.e. `boot/bigop.v:542`. |
| `Print Canonical Projections p.` | For plain (non-HB) `Structure`s, pass the projection: `tval` lists the `tuple_of` instances (`cons_tuple`, `map_tuple`, ...), `unlocked` the `Unlockable` ones. Given a type (`nat`), it lists every `S.sort <- nat` entry. |

**Rule:** run one of these before writing `[the X of T]` or declaring
an instance that may already exist. A duplicate is not an error: HB
keeps the existing instance and only warns (`HB.no-new-instance` or
`redundant-canonical-projection`).

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
- MathComp book (pre-HB, see §48): its hierarchies are hand-written
  records, mixins and `Canonical` packed classes (MCB §6.3-§6.7,
  §6.10, §8.1-§8.5). The factories and builders above replace them.

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
| `choiceType` | `xchoose`, `xchooseP`, `eq_xchoose` | pick a witness      |
| `choiceType` | `choose P x0`, `chooseP`, `choose_id` | canonical representative |
| `countType`  | `pickle`, `unpickle`, `pickleK`    | enumerate / encode  |
| `finType`    | `enum T`, `\sum_(x:T)`, `#|T|`     | finite reasoning    |
| `subType P`  | `\val`, `Sub`, `valK`              | `{x : T | P x}` (§36.13) |

**`#|T|` caveat.** `#|T|` and `x \in T` read `T` as a predicate. That
works for a `T : finType` variable and for `Inductive T : predArgType`
(as `mathcomp/boot/fintype.v` declares `ordinal` (l. 1727)). For a plain
`Inductive T := ...` with a `finType` instance, `#|T|` is ill-typed:
write `#|{: T}|` and `x \in {: T}` (§36.12).

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
- `choiceType` -- extracting a witness via `xchoose` from `exists x, P x`,
  or a canonical representative via `choose P x0` (§36.5).
- `countType` -- enumerating the carrier or coding into `nat`.
- `finType` -- finiteness is **mathematically essential** (`#|T|`,
  bigop over the whole type). Convenience does not count.

For analysis: most measure-theoretic / topological types do not need
this hierarchy at all. `pointedType`, `topologicalType` etc. bring
their own typeclasses; do not add `eqType` unless a lemma in the
proof body asks for it.

**Algebraic level: Pz vs Nz.** The same rule holds
for rings. `pzSemiRingType`, `pzRingType`, `comPzRingType`, ...
("potentially zero") allow the trivial ring `1 = 0`; this says nothing
about the characteristic. The **Nz** variants add exactly the mixin
field `oner_neq0` (`mathcomp/algebra/ssralg.v`). The book-era
`semiRingType`, `ringType`, `comSemiRingType`, `comRingType`,
`subSemiRingType`, `subComSemiRingType` and `subRingType` (nontrivial
rings in the book, MCB §8.1, §8.3) are `(only parsing)` notations for the **Nz** structures, deprecated since
2.4.0: `ringType` (l. 7081) and `comRingType` (l. 7087) are examples.
They warn `[deprecated-syntactic-definition-since-mathcomp-2.4.0]`.
`unitRingType`, `idomainType` and `fieldType` are not deprecated.

- State lemmas over `pzRingType` / `comPzRingType` / `pzSemiRingType`
  unless the proof uses `oner_neq0` or something built on it: units,
  polynomial degree (`size_polyX` needs Nz), fields.
- Porting: `ringType` -> `nzRingType` preserves meaning. Moving to Pz is
  a generalisation you check lemma by lemma: recompile at Pz.
- Pitfall: `'M[R]_n` with a variable `n` is only Pz, so Nz lemmas do
  not apply to it (`'M[R]_n.+1` is Nz).

```coq
From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.
Local Open Scope ring_scope.

Check oner_neq0.       (* forall s : nzSemiRingType, 1 != 0 *)
(* WRONG -- deprecated (warns), and silently asks for 1 != 0 *)
(* Lemma sqrD1 (R : ringType) (x : R) : ... *)
(* RIGHT -- the proof never uses 1 != 0 *)
Lemma sqrD1 (R : pzRingType) (x : R) :
  (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Proof. exact: sqrrD1. Qed.
Check fun (R : pzRingType) n => sqrD1 _ (1 : 'M[R]_n).
Fail Check fun (R : nzRingType) n => oner_neq0 'M[R]_n. (* 'M_n: Pz only *)
```

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

**Where `=` and `==` go.** Library practice refines the book's blanket
"always `==` on an `eqType`" rule (MCB §6.5):

| Where | Use | Example |
|---|---|---|
| conclusion that is a rewrite rule `lhs = rhs` | `=` | `addnC`, `big_cat` |
| premise / side condition on an `eqType` | bool `x != 0`, `x == y`; never `x <> 0`, `~ (x = y)` | PR #351 (§36.8) |
| boolean characterisation | bool on both sides of `=` | `eq_sym : (x == y) = (y == x)`, `mulf_eq0 : (x * y == 0) = (x == 0) \|\| (y == 0)` |
| Prop `x = y` in a premise | normal for positive equalities (`injective`, `cancel`, `eq_leq : m = n -> m <= n`); bool for negations / decidable side conditions | |
| type is not an `eqType` | Leibniz `=` / `<>` | |

Consume a bool premise with `case: ifP => // /eqP ->` or
`rewrite (eqP H)`:

```coq
From mathcomp Require Import all_boot.
Lemma test_EM (x y : nat) : if x == y.+1 then x != 0 else true.
Proof. by case: ifP => // /eqP ->. Qed.
Lemma cmp (T : eqType) (x y : T) : (x == y) = (y == x).
Proof. exact: eq_sym. Qed.
Lemma use_eq (T : eqType) (f : T -> nat) (x y : T) (H : x == y) :
  f x = f y.
Proof. by rewrite (eqP H). Qed.
```

**`bool` as `Prop`** (MCB §5.5). `is_true b := b = true` (Corelib
`Init/Datatypes.v`) is declared a coercion in Corelib `ssr/ssrbool.v`,
so a `bool` stands wherever a `Prop` is expected.

- State boolean facts as the bool itself: `Lemma foo : p \in s.`, not
  `(p \in s) = true`. Hypotheses likewise: `(hb : b)`, `(nb : ~~ b)`,
  never `b = true` / `b = false`.
- To rewrite with a negative fact, derive the equation on the fly:
  `rewrite (negbTE nb)` or `move=> /negPf ->`.
- `Set Printing Coercions` reveals the inserted `is_true` /
  `nat_of_bool` (errors.md §2).
- `bool` as `nat` (`nat_of_bool`, counting with `count`): see §49.7.

```coq
From mathcomp Require Import all_boot.
(* WRONG: Lemma bad (s : seq nat) : (0 \in 0 :: s) = true.  *)
(* WRONG: Lemma bad' (b : bool) (nb : b = false) : ...       *)
Lemma good (s : seq nat) : 0 \in 0 :: s.
Proof. by rewrite inE eqxx. Qed.
Lemma good' (b : bool) (nb : ~~ b) : b || false = false.
Proof. by rewrite (negbTE nb). Qed.
Lemma good'' (b c : bool) : ~~ b -> b && c = false.
Proof. by move=> /negPf ->. Qed.
```

**Boolean facts are rewrite rules** (MCB §2.1.3, §2.3.3; item 3 is
library practice). Since `b`
means `b = true`:

1. `h : b` gives `rewrite h`, which turns `b` into `true`. This chains
   with `andbT` / `orbT` / `//`.
2. A conditional boolean lemma (`prime_gt1 : prime p -> 1 < p`)
   rewrites its conclusion to `true` once the side condition is
   discharged (`rewrite prime_gt1 //`, or a hypothesis in context).
3. `(negbTE h)` with `h : ~~ b` rewrites `b` to `false`.
4. When `b` sits inside a larger boolean expression, rewrite with the
   fact instead of splitting with `apply/andP` / `apply/idP`.

```coq
From mathcomp Require Import all_boot.
Lemma hb_ex (b : bool) (hb : b) : b && true.
Proof. by rewrite hb. Qed.
Lemma pr_gt1 p : prime p -> (1 < p) && true.
Proof. by move=> pp; rewrite prime_gt1. Qed.
Lemma nb (b c : bool) (h : ~~ b) : b && c = false.
Proof. by rewrite (negbTE h). Qed.
```

**`reflect` lives in `Type`: use `x =P y` in definitions** (MCB §7.8.3).

- In **proofs**, branch with `case: eqP` / `eqVneq` (§28.1).
- In **definitions** whose positive branch needs a proof of `x = y`
  (casts, transport, dependent types), match on `x =P y` with
  `ReflectT e` / `ReflectF _`, or write
  `if x =P y is ReflectT e then ... else ...`. This works because
  `reflect P b : Type`, so it eliminates into `Type`.
- Pair the definition with characterisation lemmas proved by unfolding
  and `case: eqP` (`do 2!case: eqP` for two tests). Library model in
  `mathcomp/algebra/matrix.v`: `conform_mx` (l. 393),
  `conform_mx_id` (l. 584), `nonconform_mx` (l. 587). Matrix casts:
  §38.10.
- `if x == y then ... (eqP _) ...` does **not** put a proof of `x = y`
  in scope in the branch.

```coq
From mathcomp Require Import all_boot all_algebra.
Local Open Scope ring_scope.

Definition sq {m n : nat} (A : 'M[int]_(m, n)) : 'M[int]_(n, n) :=
  match m =P n with
  | ReflectT e => castmx (e, erefl) A
  | ReflectF _ => 0
  end.

(* same, one-branch form *)
Definition sq' {m n : nat} (A : 'M[int]_(m, n)) : 'M[int]_(n, n) :=
  if m =P n is ReflectT e then castmx (e, erefl) A else 0.

(* WRONG: `m == n` puts no proof of `m = n` in scope *)
Fail Definition sq_bad {m n : nat} (A : 'M[int]_(m, n)) :
  'M[int]_(n, n) := if m == n then castmx (eqP _, erefl) A else 0.

(* characterisation lemmas: unfold, then case: eqP *)
Lemma sq_id n (A : 'M[int]_(n, n)) : sq A = A.
Proof. by rewrite /sq; case: eqP => // e; rewrite castmx_id. Qed.

Lemma sq_neq m n (A : 'M[int]_(m, n)) : m != n -> sq A = 0.
Proof. by rewrite /sq; case: eqP. Qed.
```

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

**`choose` vs `xchoose`.** In `mathcomp/boot/choice.v`,
`xchoose exP` is indexed by a proof `exP : exists x, P x` (see
`xchooseP` (l. 319) and `eq_xchoose` (l. 322)). `choose P x0` is
indexed by a default `x0` with `P x0` (see `chooseP` (l. 359) and
`eq_choose` (l. 365)). `choose_id` (l. 362) states
`P x0 -> P y0 -> choose P x0 = choose P y0` (MCB §8.3), so
`choose (R x) x` is a
**canonical representative** of the class of `x`. On a `choiceType`,
neither operator needs the `boolp` axioms, unlike `cid`.

```coq
From mathcomp Require Import all_boot.

Section Rep.
Variables (T : choiceType) (R : rel T).
Hypothesis eqR : equivalence_rel R.
Let Rrefl x : R x x. Proof. by case: (eqR x x x). Qed.
Definition rep x := choose (R x) x.     (* canonical representative *)
Lemma repP x : R x (rep x). Proof. exact/chooseP/Rrefl. Qed.
Lemma rep_eq x y : R x y -> rep x = rep y.
Proof.
move=> Rxy; have eqRxy z : R x z = R y z by case: (eqR x y z) => _ ->.
by rewrite /rep (eq_choose eqRxy); apply: choose_id; rewrite -?eqRxy.
Qed.
End Rep.
```

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

**Defining predicates** (MCB §3.4, §3.6; views: §5.1.1, §5.1.3).

1. If every component is decidable (nat order, `==`, `prime`, `\in`,
   `all` / `has`), define the predicate as `bool`:
   `Definition oddprime x := odd x && prime x.`, not
   `odd x /\ prime x`. Filters, `[set x | P x]`, `count`,
   `\sum_(i | P i)` and `by []` (closed instances compute) then all work.
2. Bridge each connective with its view (Corelib `ssr/ssrbool.v`,
   re-exported by `all_boot`). This table gives the correspondence
   only; the tactic forms (`apply/andP; split`, `apply/orP; left`,
   `move/andP: h`, ...) live in phrasebook §2b.

   | bool | Prop | view |
   |---|---|---|
   | `a && b` | `a /\ b` | `andP` |
   | `a \|\| b` | `a \/ b` | `orP` |
   | `~~ a` | `~ a` | `negP` |
   | `a ==> b` | `a -> b` | `implyP` |
   | `x == y` | `x = y` | `eqP` |
   | `[&& a, b & c]` | `[/\ a, b & c]` | `and3P` (up to `and5P`) |
   | `[\|\| a, b \| c]` | `[\/ a, b \| c]` | `or3P` / `or4P` |

3. Destructure with `move=> /andP[ha hb]`; prove with
   `apply/andP; split`.
4. Keep `Prop` only for genuinely undecidable content (analysis sets,
   quantifiers over infinite types), or use `` `[< P >] `` (§36.4).

```coq
From mathcomp Require Import all_boot.
Definition oddprime x := odd x && prime x.
Lemma oddprime3 : oddprime 3. Proof. by []. Qed.
Lemma oddprime_gt0 x : oddprime x -> 0 < x.
Proof. by case/andP=> _ /prime_gt0. Qed.
Lemma oddprimeP x : reflect (odd x /\ prime x) (oddprime x).
Proof. exact: andP. Qed.
```

### 36.8 Common style mistakes

Repeatedly flagged in upstream review:

1. **`finType` when `eqType` suffices** (math-comp PR #351).
2. **Re-proving `xchoose`-style lemmas** or rolling a custom choice
   when an HB instance already exists.
3. **Mixing `=` and `==`** on an `eqType` (PR #351; placement table in
   §36.3). Prefer `case: eqVneq` over `case: (x =P y)` plus manual
   rewriting. Exception: inside a **reflect / `Equality.axiom` proof**,
   `case: (x =P y) => [<-|neq]` is the right tool, because you need the
   `ReflectF` branch's `x <> y` (templates.md §22).
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
- **Sub-type carriers** get Equality / Choice / Countable / Finite
  from one `[X of S by <:]` after `[isSub for v]`. Do not re-prove
  them (§36.13).
- **Avoid `Coq.Init.Logic.Decidable`**: `Decidable.decidable P` is
  `P \/ ~ P`, *not* informative. Use mathcomp's `{P}+{~P}` or `bool`.

### 36.12 Equipping a new datatype: eqType / choiceType / countType / finType

(MCB §5.1.2, §6.3-§6.5, §7.3, §8.5.) The book's `EqMixin`/`PcanEqMixin`/
`Finite.Mixin` + `Canonical` lines are gone (§48): a fresh type gets
every level from **one** `HB.instance` line. It needs
`From HB Require Import structures.` (`all_boot` does not re-export HB).

| Situation | One line |
|---|---|
| `fK : pcancel f g` (or `cancel f g`), `f : T -> K`, K known | `X.copy T (pcan_type fK)` (`can_type fK` for `cancel`). X = most derived of Equality/Choice/Countable/Finite that K has |
| Only `f_inj : injective f` into an eqType | `Equality.copy T (inj_type f_inj)` or `hasDecEq.Build T (inj_eqAxiom f_inj)`. Gives eqType only |
| Finite enumerated inductive | encode into `'I_n` with `inord`, prove `pcancel`, `Finite.copy T (pcan_type fK)` (block 2). Or, once T is a countType, `isFinite.Build T eP` with `eP : Finite.axiom e` (block 3) |
| eqType + closed enumeration `e` | `Finite.copy T (fin_type eP)`: countType + finType at once (block 1) |
| Recursive / infinite inductive | encode into `GenTree.tree X`, then `Countable.copy T (pcan_type encK)` (block 4); `Choice.copy`/`Equality.copy` if X is only a choiceType/eqType. No finType |
| Hand-written boolean test `e` | prove `eP : Equality.axiom e` (templates.md §22), then `hasDecEq.Build T eP` |
| Sub-type of an existing type | §36.13 |

Block 1, eqType by hand, by injection, by transfer (MCB §5.1.2,
§6.4-§6.5, §7.3, §8.5):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

(* Hand-written test: prove Equality.axiom, then hasDecEq.Build. *)
Inductive color := Red | Green | Blue.
Definition eqc (a b : color) : bool :=
  match a, b with
  | Red, Red | Green, Green | Blue, Blue => true
  | _, _ => false end.
Lemma eqcP : Equality.axiom eqc.
Proof. by case=> -[]; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build color eqcP.

(* eqType + closed enumeration: countType and finType in one line. *)
Lemma color_enumP : Finite.axiom [:: Red; Green; Blue]. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy color (fin_type color_enumP).

(* Transfer: f maps the NEW type into the known one. *)
Inductive color2 := C2 of color.
Definition unC2 '(C2 c) := c.
Lemma unC2K : cancel unC2 C2. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy color2 (can_type unC2K).

(* WRONG direction: C3 goes from the known type to the new one. *)
Inductive color3 := C3 of color.
Definition unC3 '(C3 c) := c.
Lemma C3K : cancel C3 unC3. Proof. by []. Qed.
Fail HB.instance Definition _ := Equality.copy color3 (can_type C3K).

(* RIGHT: only an injection into an eqType -> eqType only. *)
Lemma unC3_inj : injective unC3. Proof. by case=> a [b] /= ->. Qed.
HB.instance Definition _ := hasDecEq.Build color3 (inj_eqAxiom unC3_inj).
```

Block 2, a finite type through `'I_n` (MCB §8.5, windrose):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Inductive windrose : predArgType := N | S | E | W.
Definition w2o (w : windrose) : 'I_4 :=
  match w with N => inord 0 | S => inord 1 | E => inord 2 | W => inord 3 end.
Definition o2w (o : 'I_4) : option windrose :=
  match val o with
  | 0 => Some N | 1 => Some S | 2 => Some E | 3 => Some W | _ => None end.
Lemma w2oK : pcancel w2o o2w.
Proof. by case; rewrite /o2w /= inordK. Qed.
HB.instance Definition _ := Finite.copy windrose (pcan_type w2oK).

Check (N \in windrose).       (* predArgType: the type is a predicate *)
Lemma card_windrose : #|windrose| = 4.
Proof.
rewrite -[RHS]card_ord; apply: (bij_eq_card (f := w2o)).
exists (fun o => odflt N (o2w o)) => [w|o]; first by rewrite w2oK.
by apply: val_inj; case: o => -[|[|[|[|m]]]] //= _; rewrite inordK.
Qed.
```

Block 3, countType first (an HB requirement), then an explicit
enumeration (`Finite.axiom`, MCB §7.3):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Inductive color := Red | Green | Blue.
Definition c2o c := match c with Red => 0 | Green => 1 | Blue => 2 end.
Definition o2c n :=
  match n with 0 => Some Red | 1 => Some Green | 2 => Some Blue
  | _ => None end.
Lemma c2oK : pcancel c2o o2c. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy color (pcan_type c2oK).

Definition color_enum := [:: Red; Green; Blue].
Lemma color_enumP : Finite.axiom color_enum. Proof. by case. Qed.
(* same axiom from uniq + membership; note the (color : eqType) *)
Lemma color_uniq : uniq color_enum. Proof. by []. Qed.
Lemma mem_color_enum : color_enum =i (color : eqType). Proof. by case. Qed.
Definition color_enumP' := Finite.uniq_enumP color_uniq mem_color_enum.
HB.instance Definition _ := isFinite.Build color color_enumP.

Lemma card_color : #|{: color}| = 3.
Proof. by rewrite cardT enumT unlock. Qed.
```

Block 4, a recursive type through GenTree (MCB §8.5). Give each
constructor its own `Node k` and put payloads in `Leaf` (this encoding
and the example are not from the book):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Inductive btree := Leaf of nat | Node of btree & btree.
Fixpoint enc (t : btree) : GenTree.tree nat :=
  match t with Leaf n => GenTree.Leaf n
  | Node l r => GenTree.Node 0 [:: enc l; enc r] end.
Fixpoint dec (t : GenTree.tree nat) : option btree :=
  match t with
  | GenTree.Leaf n => Some (Leaf n)
  | GenTree.Node 0 [:: l; r] =>
      if (dec l, dec r) is (Some l', Some r') then Some (Node l' r')
      else None
  | _ => None end.
Lemma encK : pcancel enc dec. Proof. by elim=> //= l -> r ->. Qed.
HB.instance Definition _ := Countable.copy btree (pcan_type encK).
Check (Leaf 1 == Leaf 2, pickle (Leaf 1)).
```

Block 5, pitfalls (`CanIsFinite`, predArgType):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Inductive tri := T1 | T2 | T3.
Definition t2o t : 'I_3 :=
  match t with T1 => inord 0 | T2 => inord 1 | T3 => inord 2 end.
Definition o2t (o : 'I_3) :=
  match val o with 0 => T1 | 1 => T2 | _ => T3 end.
Lemma t2oK : cancel t2o o2t.
Proof. by case; rewrite /o2t /= inordK. Qed.

(* WRONG: CanIsFinite needs tri to be a countType already *)
Fail HB.instance Definition _ := CanIsFinite t2oK.
HB.instance Definition _ := Finite.copy tri (can_type t2oK).
Fail Check #|tri|.           (* "tri" ... expected "pred_sort ?pT" *)
Check #|{: tri}|.
Check (T1 \in [set: tri]).
```

Rules:

- **Cancel direction.** In `can_type fK` with `fK : cancel f g`, `f`
  maps the **new** type into the known one. The reverse direction
  fails with `Definition illtyped … has type Equality.axioms_ <known>
  while it is expected to have type Equality.axioms_ T` (errors.md §1).
- **Copy the most derived structure once.** It registers every
  ancestor; chaining `Equality.copy` … `Finite.copy` only adds warnings.
  Even one copy prints harmless `[redundant-canonical-projection]`
  warnings (errors.md §9).
- **`isFinite.Build` needs a countType.** On a T that is only an
  eqType it prints `HB: no new instance is generated`, and `#|{: T}|`
  then fails with `mem_pred T … expected mem_pred (Finite.sort ?T)`.
  Copy Countable first (block 3), or use `Finite.copy T (fin_type eP)`.
- **`Finite.uniq_enumP : uniq e -> e =i T -> Finite.axiom e`** with
  `T : eqType`. Write the premise as `e =i (T : eqType)`: `e =i T` on
  the raw inductive fails with the `pred_sort ?pT` error below.
- **`CanIsFinite fK` / `PCanIsFinite fK`** (block 5). On a fresh type
  they are ill-typed. On a countType they need the ascription
  `HB.instance Definition _ : isFinite T := CanIsFinite fK.`
  (finmap/finmap.v:2275, algebra/qpoly.v:130). Without it: `non
  forgetful inheritance detected` + `HB: no new instance is
  generated`. Default: `Finite.copy T (can_type fK)`.
- **predArgType.** Declare index universes `Inductive T : predArgType`
  (as `ordinal` is) so `x \in T` and `#|T|` parse. Otherwise write
  `#|{: T}|`, `x \in [set: T]` or `x \in {: T}`. The error `The term
  "T" has type "Set" while it is expected to have type "pred_sort ?pT"`
  is about the declaration: it remains after `Finite.copy` succeeds.
- **Computing `#|T|`:** `bij_eq_card` + `card_ord` (block 2), or
  `cardT` + `enumT` + `unlock` (block 3). Never unfold `enum`.
- **Porting only:** `deprecated_InjEqMixin` / `_PcanEqMixin` /
  `_CanEqMixin` still exist. Never use them in new code (§48).
- **Shape and names.** `Definition eqfoo`, `Lemma eqfooP :
  Equality.axiom eqfoo.` Never hand-write a comparison when a
  (p)cancel into `nat`, `seq`, a product or `'I_n` already exists.

Sources:
- mathcomp/boot/eqtype.v: `inj_type` (l. 748), `pcan_type` (l. 749),
  `can_type` (l. 750), `inj_eqAxiom` (l. 758),
  `deprecated_InjEqMixin` (l. 770).
- mathcomp/boot/fintype.v: `uniq_enumP` (l. 183), `fin_type` (l. 207),
  `bij_eq_card` (l. 1316), `PCanIsFinite` (l. 1416),
  `CanIsFinite` (l. 1418), `ordinal` (l. 1727), `card_ord` (l. 1772).
- GenTree: boot/choice.v:164; Countable along `pcan_type`: boot/choice.v:545.

### 36.13 Defining and using sub-types

A sub-type packs a value with a proof of a **boolean** invariant; the
HB sub-type kit then derives `val`, `Sub`, `insub` and every
combinatorial structure (MCB §7.2.1, §7.2.2). For a fresh datatype that
is not a value-plus-proof record, copy instances along a cancel
instead (§36.12). API in `mathcomp/boot/eqtype.v`.

**Declaring.**

1. Shape: `Record S : predArgType := MkS { sval :> T; _ : P sval }`
   with `P` a **bool** predicate (`0 < n`, `size s == n`,
   `~~ odd n`), never a `Prop`. Proofs of `b = true` are unique
   (`bool_irrelevance` (l. 326)), so `val` is injective and every
   structure of `T` transfers. A `Prop` field makes `[isSub for sval]`
   fail with `Definition illtyped … expected to have type
   "is_true (?p x)"`.
2. Leave the proof field anonymous (`_`): it is a side condition, not
   API. Read it back with `valP` or a one-line `by case: u.` lemma.
3. Declare the record `: predArgType` so `#|S|` and `x \in S` parse
   (§36.12).
4. First `HB.instance Definition _ := [isSub for sval].`, then exactly
   **one** top structure, the highest `T` has: `[Finite of S by <:]`
   or `[Countable of S by <:]` (brings Equality and Choice);
   `[Choice of S by <:]` when `T` is only a `choiceType` (e.g. a
   real type); `[Equality of S by <:]` when `T` is only an `eqType`.
   Never hand-prove `Equality.axiom` for a sub-type.
5. Elements of different subsets that must mix (compare, union,
   intersect) are not separate sub-types: keep them in `T` and use
   `{set T}` / `pred T` with `x \in A` hypotheses (§40).

| Situation | Declaration (library example) |
|---|---|
| projection is a record field | `[isSub for sval]` (boot/tuple.v:63) |
| name `S` explicitly (needed when `S` is an alias of `f`'s domain) | `[isSub of S for f]` (`ordinal`: boot/fintype.v:1731; its sub-type API `ltn_ord`/`ord_inj`: domains/46 §46.2) |
| trivial predicate (wrapper around `T`) | `[isNew for f]` (algebra/matrix.v:287) |
| book `Canonical … := Eval hnf in [subType for v]` | `HB.instance Definition _ := [isSub for v].`; the `#[hnf]` attribute replaces `Eval hnf in` where it is still wanted (boot/finfun.v:506) |
| book `[newType for v]` | `[isNew for v]` |
| book `[eqMixin of S by <:]` + `EqType` | `[Equality of S by <:]` (boot/eqtype.v:799) |

`[isSub for …]` prints `[projection-no-head-constant]` on
`isSub.Sub_rect`, and the transfers print
`[redundant-canonical-projection]`: both are benign (errors.md §9).

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

(* bool invariant, anonymous proof field, predArgType for #|_| *)
Record evn : predArgType := Evn { evv :> nat; _ : ~~ odd evv }.
HB.instance Definition _ := [isSub for evv].
HB.instance Definition _ := [Countable of evn by <:]. (* + Equality, Choice *)

Record b3 : predArgType := B3 { b3v : 'I_3; _ : b3v != ord0 }.
HB.instance Definition _ := [isSub for b3v].
HB.instance Definition _ := [Finite of b3 by <:].
Check #|b3|.

Record wrap := Wrap { unwrap : nat }.       (* trivial predicate *)
HB.instance Definition _ := [isNew for unwrap].
HB.instance Definition _ := [Countable of wrap by <:].

Lemma evn_even (u : evn) : ~~ odd u. Proof. by case: u. Qed.

(* WRONG: a Prop invariant; the sub-type kit rejects it *)
Record pevn := PEvn { pv : nat; _ : exists k, pv = k.*2 }.
Fail HB.instance Definition _ := [isSub for pv].
```

**API** (`mathcomp/boot/eqtype.v`; `P : pred T`, `u : S`):

| Name | Statement / use |
|---|---|
| `val` (l. 564) | generic projection `S -> T`; printed `\val` |
| `valP` (l. 627) | `P (val u)` |
| `SubK` (l. 588) | `val (Sub x Px) = x` |
| `val_inj` (l. 633) | `injective val` |
| `valK` (l. 630) | `pcancel val insub` |
| `insub` (l. 596) | `T -> option S`; a plain `Definition` in 2.5 (not `locked`), still not reducible by `simpl` / `reflexivity` |
| `insubP` (l. 604) | `insub_spec x (insub x)`: `InsubSome u Pu (val u = x)` \| `InsubNone (~~ P x)` |
| `insubT` (l. 609) | `insub x = Some (Sub x Px)` |
| `insubF` (l. 615) | `P x = false -> insub x = None` |
| `insubN` (l. 618) | `~~ P x -> insub x = None` |
| `isSome_insub` (l. 621) | `[eta insub] =1 P` |
| `insubK` (l. 624) | `ocancel insub val` |
| `insubd` (l. 598) | `insubd u0 x := odflt u0 (insub x)` |
| `val_insubd` (l. 639) | `val (insubd u0 x) = if P x then x else val u0` |
| `insubdK` (l. 642) | `{in P, cancel (insubd u0) val}` |
| `val_eqE` (l. 793) | `(val u == val v) = (u == v)` |

**Building and destructing.**

- Build with `Sub x Px` when the proof is in hand; with
  `insubd u0 x` in a total definition; with `insub x` when the
  caller must see failure.
- Never `rewrite /insub` or expect `simpl` / `reflexivity` to reduce
  `insub x`. Rewrite with `insubT` / `insubN` / `val_insubd`, or
  case on `insubP`.
- `case: insubP => [u Pu <-|nPx]` works only when `insub x`, at a
  known sub-type, already occurs in the goal. Otherwise instantiate
  it: `case: (@insubP _ _ S x)` (error text in errors.md §7).

```coq
(* continues the block above *)
Definition ev0 : evn := Sub 0 isT.             (* proof in hand *)
Definition mk (n : nat) : evn := insubd ev0 n.  (* total, default ev0 *)

Lemma mkE n : ~~ odd n -> val (mk n) = n.
Proof. by move=> h; rewrite val_insubd h. Qed.

Lemma mkE' n : val (mk n) = if ~~ odd n then n else 0.
Proof. by rewrite /mk /insubd; case: insubP => [u -> -> | /negbTE ->]. Qed.

Lemma insub2 : insub 2 = Some (Sub 2 isT : evn).
Proof. Fail reflexivity. by rewrite insubT. Qed.

Lemma evn_of n : ~~ odd n -> exists u : evn, val u = n.
Proof.
Fail case: insubP.                 (* insub n is not in the goal *)
by case: (@insubP _ _ evn n) => [u _ <- _ | /negP]; [exists u |].
Qed.

Lemma evn_eqE (u v : evn) : (evv u == evv v) = (u == v).
Proof. exact: val_eqE. Qed.
```

**Equality of two sub-type values.**

- `apply: val_inj` first: the goal becomes an equality of values.
- Only when destructed down to one value with two proofs:
  `by rewrite (bool_irrelevance p1 p2)`. For two proofs of an
  equality in an eqType:
  `eq_irrelevance` (l. 287), declared as a `Theorem`.
- Never the stdlib `proof_irrelevance` axiom nor
  `boolp.Prop_irrelevance` (drags in `propext`): both show up in
  `Print Assumptions` for a fact that holds constructively (§36.11).
  `congr MkS` fails with `No congruence with MkS` when the values
  differ, and on equal values only leaves `p1 = p2`.
- If the invariant is a `Prop`, redesign it as a `bool` (rule 1).

```coq
(* continues the first block *)
(* RIGHT: reduce to the values *)
Lemma evn_inj x y (p1 : ~~ odd x) (p2 : ~~ odd y) :
  x = y -> Evn x p1 = Evn y p2.
Proof. by move=> exy; apply: val_inj => /=. Qed.

(* RIGHT, fallback once destructed down to one value, two proofs *)
Lemma evn_ext x (p1 p2 : ~~ odd x) : Evn x p1 = Evn x p2.
Proof. by rewrite (bool_irrelevance p1 p2). Qed.

(* WRONG: congr cannot rewrite under the dependent proof field *)
Lemma evn_inj' x y (p1 : ~~ odd x) (p2 : ~~ odd y) :
  x = y -> Evn x p1 = Evn y p2.
Proof. move=> exy. Fail congr Evn. by apply: val_inj. Qed.
```

---

## 37. Search Discipline

A lemma is only as useful as it is findable. Mathcomp culture treats
`Search` as the primary library-navigation tool: every statement is
named, ordered, and notated so that future searchers can rediscover
it from any salient symbol. This section consolidates the rules
implicit in the upstream review threads cited in §10, §12, §17, §32.

### 37.1 The `Search` commands every contributor uses

In Rocq 9, **every argument of `Search` is a conjunctive filter, and a
pattern matches anywhere in the statement** (premises included). The
book's ssreflect-1.x semantics (MCB §2.5.1–§2.5.2, Part III cheat
sheet), where the first pattern constrains the conclusion and
`Search _ p` means "no head constraint", were removed in modern
Coq/Rocq. Today `Search _ p` only adds a trivial `_` pattern: write
`Search p`, and use `concl:` to restrict to the conclusion.

| Form | Purpose |
|------|---------|
| `Search "_eq0".` | by name substring |
| `Search "C" "muln".` | several name substrings, all required (`mulnC`, `mulnCA`, ...); pairs with the §11 suffix table |
| `Search (?x + ?y) (?x = ?y).` | by term pattern, anywhere in the statement (multiple constraints conjunctive) |
| `Search concl:(odd _) "D".` | pattern in the conclusion only (`oddD`, `halfD`); replaces the book's first-pattern rule |
| `Search hyp:(odd _) "prime".` | pattern in some premise (`odd_prime_gt2`) |
| `Search headconcl:(_ <= _) inside ssrnat.` | the conclusion itself has this shape (see pitfall below) |
| `Search head:(_ <= _) "trans".` | head of the conclusion **or** of a premise (`headhyp:` = premises only) |
| `Search "max" inside Order.TotalTheory.` | within a module (`in M` is a synonym of `inside M`) |
| `Search "addn" outside ssrnat.` | excluding a module |
| `Search -is_true (?x <= ?y).` | exclude a head/wrapper |
| `Search "_le" (?x + _).` then `Search "_lt" (?x + _).` | (Rocq's `Search` does not support disjunction of name patterns; run two queries) |

`Search` needs at least one pattern or string: a bare
`Search inside M.` is a parse error.

**Pitfall: `headconcl:` / `head:` match the shape of the whole
conclusion, not a symbol inside it.**

- Equations have head `_ = _`, so `Search headconcl:(_ + _)`,
  `headconcl:addn` and `head:addn` return nothing for `m + n = …`
  lemmas.
- Boolean conclusions are `is_true (odd n)`, so the bare constant
  `Search headconcl:odd` is empty. The applied pattern
  `headconcl:(odd _)` works (`dvdn_odd`).
- Default to `concl:(pat)`. Reserve `headconcl:` for relation- or
  predicate-headed statements (`(_ <= _)`, `(odd _)`, `reflect`).

```coq
From mathcomp Require Import all_boot.

Search addn (_ * _) "C" inside ssrnat.  (* book query, modern *)
Search concl:(_ + _) "C" inside ssrnat. (* conclusion only *)
Search concl:(odd _) "D".               (* oddD, halfD *)
Search hyp:(odd _) "prime".             (* odd_prime_gt2 *)
Search headconcl:(odd _).               (* dvdn_odd *)
Search headconcl:odd.                   (* EMPTY: head is is_true *)
Search headconcl:(_ + _) inside ssrnat. (* EMPTY: head is _ = _ *)
```

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

2. **`mainSymbol_unaryPredicate`** (§10) for property lemmas:
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
suffix `P` (§11). To prove a new view: templates.md §22.

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
`Search "name" inside Module` (§37.1). Always add a short user-facing
alias so
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

Registration rules (MCB §2.3.3 shows the pre-8.10 bare form):

- **Always name the database.** A bare `Hint Resolve lem.` warns
  `Adding and removing hints in the core database implicitly is
  deprecated. Please specify a hint database.
  [implicit-core-hint-db,deprecated-since-8.10]`.
- **Choose a locality.** `#[local]` for file-local convenience,
  `#[export]` to reach every file that imports yours.
- `done`, `by []` and `//` run `trivial`, which consults `core`. That is
  why a core hint shortens proofs, and why every extra core hint slows
  every `//`.
- In library code, prefer passing the lemma explicitly
  (`exact: leqnn`) unless the fact is a one-step, ubiquitous side
  condition.

In mathcomp/boot/ssrnat.v, `leqnn` (l. 333), `leqnSn` (l. 337) and
`ltnW` (l. 406) are already `#[global]` core hints: a book line that
re-registers them is dead weight.

```coq
From mathcomp Require Import all_boot.

(* leqnn, leqnSn, ltnW are already #[global] core hints (ssrnat.v): *)
(* delete book lines that re-add them.                              *)
Lemma leq_double n : n <= n.*2.
Proof. by rewrite -addnn leq_addr. Qed.
(* WRONG (book form): Hint Resolve leq_double.  -- warns            *)
#[export] Hint Resolve leq_double : core.   (* RIGHT: db + locality *)
Lemma hint_ex n : n <= n.*2.
Proof. by []. Qed.
```

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

When *looking for* a **bigop** lemma (MCB §6.7.3, Part III cheat
sheet), a pattern over a concrete `\sum` usually returns nothing,
because generic lemmas are stated over `\big[op/idx]_(i <- r | P) F`:

1. Start with the `"big"` name substring plus the range shape:
   `Search "big" (_ ++ _).`, `Search "big" (index_iota _ _).`
2. Pattern-search with the generic form **including the filter slot**:
   `\big[_/_]_(_ <- _ ++ _ | _) _` finds `big_cat`. A `\sum` pattern,
   or a pattern without `| _`, finds nothing.
3. Operation-specific lemmas carry `sum`/`prod` names (`sumrB`
   algebra/ssralg.v:852, `prodfV` algebra/ssralg.v:4743), so also try
   `Search "sum" …`.
4. `inside bigop` silently resolves to the **nested** module
   `mathcomp.boot.bigop.bigop` and returns nothing. Write
   `inside boot.bigop` (or `inside mathcomp.boot.bigop`), or drop the
   restriction. `Locate Module M` reveals such shadowing.
5. Name families (§34.7): `"rec"` peels one term (`big_nat_recl`,
   `big_ord_recr`), `"cond"` handles filters (`big_mkcond`,
   `big_seq_cond`), `"ind"` gives induction principles (`big_ind`,
   `big_ind2`), `"exchange"` swaps nested bigops (`exchange_big`),
   `"geq"`/`"nil"` close empty ranges (`big_geq`, `big_nil`).

```coq
From mathcomp Require Import all_boot.

Search "big" (_ ++ _).                  (* big_cat, big_catl, ... *)
Search (\big[_/_]_(_ <- _ ++ _ | _) _). (* same hits *)
Search "big" "cat" inside boot.bigop.   (* NOT inside bigop *)
Search "big" "rec".                     (* big_nat_recl, big_ord_recr *)
(* No hit: Search (\sum_(_ <- _ ++ _) _).
   No hit: Search (\big[_/_]_(_ <- _ ++ _) _).   -- no `| _` slot
   No hit: Search "big" "cat" inside bigop.      -- nested module *)
```

For contrapositives, `Search "contra".` lists the `contra*` family;
`phrasebook.md` §16 says which member to pick.

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

### 37.12 Beyond `Search`: `About` / `Print` / `Check` / `Locate` / `Compute` / `Fail`, and the file header

(MCB §1.1.1, §1.2.3, §1.7, §2.1.1, §3.1, §3.2, §3.5; `Print Implicit`,
`Print Notation`, `Set Printing Coercions` and `HB.lock` are not from
the book)

`Search` finds a name; these commands tell you how to use it. Send them
through `rocq_query` with `from_state`, so they see the live context
(section variables, local notations, open scopes).

| Question | Command | What to read |
|---|---|---|
| Does this instantiation have the type I think? | `Check (lem x y) : T.` | A mismatch error here is cheaper than a failed `rewrite` / `apply:`. |
| Which arguments, which implicit, in what order? Where is it declared? | `About lem.` / `Print Implicit lem.` | `{x}` maximal, `[x]` non-maximal, bare = explicit (§25.5). Read it before `apply:`, `exact:`, `(x := …)` or `@`. The last line names the library and line (`Declared in library mathcomp.boot.seq, line 378`). |
| What does this notation mean, in which scope? | `Locate "_ < _".` | Use the underscore pattern: a single token such as `"<"` lists every notation containing it (`m < n <= p`, `\sum_ (m <= i < n) F`, …). Then `Search` by the head constant it prints, or by pattern (`Search (_ %/ _).`). |
| Level / associativity of a notation? | `Print Notation "_ + _".` | `at level 50 …, left associativity`. |
| What does this definition unfold to? | `Print foo.` | An `HB.lock`ed definition shows only the lock; rewrite with `foo.unlock` (§35.8). |
| Does my new `Definition` / `Fixpoint` compute what I expect? | `Compute foo 4.` | Closed, small, ground terms only. A `Qed`-opaque head stays stuck (`= f 3`); a bigop over a `finType` prints a huge unreduced term. Run it on 2–3 inputs right after each new definition, before proving anything about it. |
| Is this really rejected? Is this side condition needed? | `Fail Check …` / `Fail apply: …` | Scratch/probe files and test files only; never in library code sent upstream. |
| What is behind the display? | `Set Printing All.` / `Set Printing Coercions.` / `Unset Printing Notations.` | Shows `S`, `leq`, `addn`, `is_true`, `nat_of_bool` behind `.+1`, `<`, `+` and coercions. |

**The echo is not your input.** `Check leqnn 3 : 3 <= 3.` succeeds and
prints `leqnn 3 : 2 < 3`: `m < n` is notation for `m.+1 <= n`, and the
printer prefers it. Do not "fix" a statement because its echo differs;
compare raw terms with `Unset Printing Notations`.

```coq
From mathcomp Require Import all_boot.
About nth.          (* nth : forall {T : Type}, T -> seq T -> nat -> T *)
Print Implicit nth. (* Argument T is implicit and maximally inserted *)
Locate "_ < _".     (* (leq (S m) n) : nat_scope (default interpretation) *)
Print Notation "_ + _".       (* at level 50 ..., left associativity *)
Check leqnn 3 : 3 <= 3.       (* echoes  leqnn 3 : 2 < 3 *)
Check [seq i <- [:: 1; 2] | odd i].
Compute [seq i.+1 | i <- iota 0 3].                (* = [:: 1; 2; 3] *)
Compute (fun n => if n is p.+1 then p else 0) 5.   (* = 4 *)
Fail Check (3 : bool).
Unset Printing Notations.
Check fun m n => m.+1 < n.    (* fun m n : nat => leq (S (S m)) n *)
Set Printing Notations.
Set Printing Coercions.
Check fun b : bool => b + 1.  (* fun b : bool => nat_of_bool b + 1 *)
Unset Printing Coercions.
```

Workflow on an unfamiliar name or symbol:

1. `About` → `Print` → `Locate`.
2. Read the defining file's header comment: it is the file's API index
   (operations, notations, naming conventions). `About f.` prints the
   library (`mathcomp.boot.seq`), i.e. the file
   `$(rocq c -where)/user-contrib/mathcomp/boot/seq.v`.
3. For HB structures and instances use `HB.about` / `HB.locate` (§35.7).

### 37.13 Statement shape for `rewrite` / `apply` usability

(MCB §4.3; rules 1-4: §4.3.5; rule 5: §4.2.1; rule 6's notation, not
the preference: §1.2.1, §1.3.1, §1.7)

`rewrite` uses the LHS as its pattern and infers the other arguments by
matching it; `apply:` infers what the conclusion and the passed
hypotheses determine. State lemmas so that callers supply as little as
possible. Complements §32.4 (equations over implications), §37.2 (name
after the LHS head) and §37.5 (side-condition placement).

| Rule | WRONG | RIGHT |
|---|---|---|
| 1. The LHS is the specific redex the user has in the goal; the RHS is simpler | `0 = 0 * n` | `mul0n : 0 * n = 0` |
| 2. Every variable occurs in the LHS (or in a hypothesis the caller passes) | `0 = 0 * n`: `rewrite` fails, `Unable to find an instance for the variable n` | `rewrite mul0n` needs no argument |
| 3. No conditional equation with a generic LHS | `n = 0 -> n * m = 0` rewrites the first product it meets | put the constant in the LHS: `0 * m = 0` |
| 4. Binders not inferable from the conclusion (transitivity pivot, witness) come first | `forall m p n, m <= n -> n <= p -> m <= p` | `leq_trans n m p : m <= n -> n <= p -> m <= p` |
| 5. "Exists x with two properties" | `exists x, P x /\ Q x` | `exists2 x, P x & Q x` |
| 6. Three or more boolean conjuncts | `a && b && c` | `[&& a, b & c]` |

```coq
From mathcomp Require Import all_boot.

(* WRONG: bare-constant LHS; the pattern `0` does not determine n. *)
Lemma mul0n_bad n : 0 = 0 * n.  Proof. by []. Qed.
(* WRONG: generic LHS; matches the first product in the goal. *)
Lemma mul0n_if n m : n = 0 -> n * m = 0.  Proof. by move->. Qed.
(* RIGHT: the redex is the LHS and every variable occurs in it. *)
Check mul0n : forall n, 0 * n = 0.

Goal forall m, 2 * 3 + 0 * m = 6.
Proof.
move=> m.
Fail rewrite mul0n_bad.  (* Unable to find an instance for the variable n *)
rewrite mul0n_if.        (* rewrote 2 * 3, side goal 2 = 0 *)
Abort.

Goal forall m, 2 * 3 + 0 * m = 6.
Proof. by move=> m; rewrite mul0n. Qed.
```

**Pivot first (rule 4).** In `mathcomp/boot/ssrnat.v`,
`leq_trans` (l. 398) quantifies `n m p` as non-maximal implicits
(`About leq_trans` prints `forall [n m p : nat]`), so `leq_trans 5` is
ill-typed.

- With the hypotheses at hand, pass them: `leq_trans h1 h2`,
  `apply: (leq_trans h1)`.
- To fix only the pivot, write `@leq_trans 5` (short *because* the
  pivot is first) or `leq_trans (_ : m <= 5)`.
- In `mathcomp/order/preorder.v`, `le_trans` (l. 1043) is stated as
  `transitive`, whose first binder is the pivot: `@le_trans _ _ y`.
- If callers keep writing `@lem _ _ x`, make `x` explicit (§31.3).

```coq
From mathcomp Require Import all_boot all_order.
Import Order.TTheory.  (* else `About le_trans` finds no object *)

(* leq_trans: the pivot n comes first; n m p are non-maximal implicits *)
About leq_trans. (* leq_trans : forall [n m p : nat], m <= n -> n <= p -> ... *)
Lemma via5 m p : m <= 5 -> 5 <= p -> m <= p.
Proof.
move=> h1 h2.
Fail apply: (leq_trans 5).   (* 5 is taken as the proof of m <= n *)
apply: (@leq_trans 5).       (* pivot first: a short @ *)
  by [].
by [].
Qed.
Lemma via5' m p : m <= 5 -> 5 <= p -> m <= p.
Proof. by move=> h1 h2; apply: (leq_trans (_ : m <= 5)). Qed.
Lemma via_h m n p : m <= n -> n <= p -> m <= p.
Proof. by move=> mn; apply: (leq_trans mn). Qed.
About le_trans.  (* le_trans : forall {disp} {T} [y x z : T], ... *)
```

**Existentials and n-ary conjunctions (rules 5, 6).**

- State `exists2 x, P x & Q x` (Prop), or `{x | P x & Q x}` when the
  witness must be computed (sig2). Never `exists x, P x /\ Q x`.
- Destructure both the same way: `case=> x Px Qx`,
  `move=> /lem[x Px Qx]`, `have /lem[x Px Qx] := …`.
- Prove with `exists x`, which leaves the two goals (`by exists x` when
  they compute, else `exists x => //`).
- Three properties: `exists x, [/\ P x, Q x & R x]`, destructured with
  `[x [Px Qx Rx]]`, proved with `exists x; split`. There is no
  `exists3` / `sig3`.
- In `mathcomp/boot/prime.v`, `pdivP` (l. 561) is Type-valued:
  `1 < n -> {p | prime p & p %| n}`. It destructures in a Prop goal
  exactly like `exists2`.
- Boolean conjuncts: `a && b && c` parses left-nested, so `/and3P` does
  not match it (`/andP[/andP[ha hb] hc]` is needed). State
  `[&& a, b & c]` / `[|| a, b | c]` so that `and3P`…`and5P` and
  `or3P`/`or4P` apply. View idioms: phrasebook.md §2.

```coq
From mathcomp Require Import all_boot.

Lemma odd_above2 : exists2 n, 2 < n & odd n.
Proof. by exists 3. Qed.

Lemma ex2_elim (P Q : nat -> Prop) :
  (exists2 x, P x & Q x) -> exists x, Q x.
Proof. by case=> x _ Qx; exists x. Qed.

Lemma prime_div n : 1 < n -> exists2 p, prime p & p %| n.
Proof. by move=> /pdivP[p pr_p p_dv_n]; exists p. Qed.

Lemma ex3d (P Q R : nat -> Prop) :
  (exists x, [/\ P x, Q x & R x]) -> exists x, P x.
Proof. by case=> x [Px _ _]; exists x. Qed.

Lemma and3_mid (a b c : bool) : [&& a, b & c] -> b.
Proof. by case/and3P. Qed.

Lemma and_mid (a b c : bool) : a && b && c -> b.
Proof. Fail move=> /and3P. by case/andP=> /andP[]. Qed.
```

---

---

## 48. Coming from the MathComp Book (mathcomp 1.x / Coq 8 → mathcomp 2.5 / HB / Rocq 9)

Source: Mahboubi & Tassi, *Mathematical Components* (2022 draft
v1.0.2, doi:10.5281/zenodo.3999478). The book predates Hierarchy
Builder. Its ch. 6-8 instance machinery and some of its lemma names
no longer compile (MCB §6.3-§6.7, §6.10, §7.2-§7.7, §8.1-§8.5). This
section is the single old → new map. Other sections point here.

### 48.1 Process rules

1. Compile every book idiom before you trust it. On "not found",
   `Search` with the modern suffix scheme (§11: `D`/`B`/`M`/`X`,
   `p`/`n` prefixes as in `ltr_pM2l`).
2. Treat the book's **R** boxes as rules and its **!** boxes as
   pitfalls (MCB Introduction, Conventions).
3. On style conflicts the skill's upstream-review rules win, e.g. no
   numeric occurrence selectors (§8) and `==` rather than blanket
   Leibniz statements (§36.3).
4. Never paste the book's pedagogical re-definitions (MCB §1.2-§1.3)
   of `bool`, `nat`,
   `seq`, `addn`, `leq`, …: they shadow the library (§49.8).
5. `ssreflect.v` sets global options that the book assumes silently.
   Bullets are inert (`Bullet Behavior "None"`, boot/ssreflect.v:6)
   and a conditional rewrite leaves the main goal first and its side
   conditions last (`SsrOldRewriteGoalsOrder`, boot/ssreflect.v:4).
   See §26.5 and §27.9.

### 48.2 Old → new tables

Every row below was checked on Rocq 9.1.1 / mathcomp 2.5.0.

**Imports and files** (§3)

| Book / 1.x | mathcomp 2.5 / Rocq 9 |
|---|---|
| `From mathcomp Require Import all_ssreflect.` | `all_boot` (+ `all_order`). `all_ssreflect` is deprecated since 2.5.0 (§3) |
| `mathcomp/ssreflect/<f>.v` | `mathcomp/boot/<f>.v`; `order.v`/`preorder.v` → `mathcomp/order/` |
| `all_character` | separate `mathcomp-character` package, not in core |
| `From Coq Require …` | `From Stdlib Require …` (`From Coq` warns `deprecated-from-Coq`), imported **before** mathcomp (§49.8) |
| `reflect`, `iffP`, `contra*`, `is_true` in mathcomp's `ssrbool` | They now live in Corelib: `Locate iffP` answers `Corelib.ssr.ssrbool.iffP` |

**Instances** (§36.12, §36.13, §34.10, §35)

| Book / 1.x | mathcomp 2.5 / HB |
|---|---|
| `Definition m := EqMixin p.` + `Canonical T_eqType := EqType T m.` | `HB.instance Definition _ := hasDecEq.Build T p.` |
| `PcanEqMixin fK` / `CanEqMixin` / `InjEqMixin` + `EqType`/`ChoiceType`/`CountType`/`FinType` + `Canonical` (≈ 8 lines) | `HB.instance Definition _ := X.copy T (pcan_type fK).` (`can_type` for `cancel`; X = most derived of Equality/Choice/Countable/Finite the target has, §36.12); `InjEqMixin`: `Equality.copy T (inj_type f_inj)`. `deprecated_PcanEqMixin` etc. exist (boot/eqtype.v:771); never use them |
| `Canonical S_subType := Eval hnf in [subType for v].` | `HB.instance Definition _ := [isSub for v].` |
| `[newType for v]` | `[isNew for v]` |
| `Eval hnf in …` | `#[hnf] HB.instance …` (boot/eqtype.v:789) |
| `[eqMixin of S by <:]` + `EqType` | `[Equality of S by <:]` (boot/eqtype.v:799); likewise `[Choice of S by <:]`, `[Countable of S by <:]`, `[Finite of S by <:]` |
| `FinMixin` / `UniqFinMixin` + `FinType` | `isFinite.Build T enumP` (`enumP : Finite.axiom e`) or `isFinite.Build T (Finite.uniq_enumP e_uniq mem_e)`; when `T` is only an eqType, `Finite.copy T (fin_type enumP)` (boot/fintype.v:207) |
| `ZmodMixin addA addC add0 addN` + `ZmodType` | `GRing.isZmodule.Build T addA addC add0 addN` (factory at boot/nmodule.v:499; library use at algebra/zmodp.v:152) |
| `ComRingMixin … nontriv` + `RingType` + `ComRingType` | `GRing.Zmodule_isComNzRing.Build …` (algebra/zmodp.v:252). Check with `HB.howto T comNzRingType` |
| `Canonical Zmn_ringType := [ringType of Zmn].` (alias) | `HB.instance Definition _ := GRing.NzRing.copy Zmn (A * B)%type.` |
| `[finRingType of 'I_p]` join declarations | Nothing: HB builds the joins |
| `[eqType of T]`, `[choiceType of T]`, `[finType of T]`, `[law of op]` | **Syntax error** (`[lconstr] expected`). Use `(T : eqType)`, `HB.about T`, or a clone `Equality.clone T _` when one is needed (§35.7). `[the eqType of T]` fails for `T : Set` (`nat`, `bool`) unless you write `[the eqType of T : Type]` |
| `Canonical addn_monoid := Monoid.Law addnA add0n addn0.` | `HB.instance Definition _ := Monoid.isLaw.Build T idx op opA op1x opx1.` or `Monoid.isComLaw.Build T idx op opA opC op1x` (boot/bigop.v:542, §34.10) |
| Hand-written `Module Foo.` `Record mixin_of …` `class_of …` `Structure type := Pack …` `Exports` `phant_id` | `HB.mixin Record` + `HB.structure Definition` (§35). Never hand-write packed classes. `phant`/`id_phant` only show up in HB-generated code (errors.md §1) |
| `Canonical` on anything | Survives only for plain `Structure`s (`tuple_of`, `Unlockable`) (§46.2) |

**Structure names** (§36.2, §45.1)

| Book / 1.x | mathcomp 2.5 |
|---|---|
| `ringType`, `comRingType`, `semiRingType`, `comSemiRingType`, `subSemiRingType`, `subComSemiRingType`, `subRingType` | Deprecated since 2.4.0, `(only parsing)` (algebra/ssralg.v:7081). The **Nz** name preserves the meaning (`ringType` = `nzRingType`). Use the **Pz** name (`pzRingType`, `comPzRingType`, …) when the proof never uses `1 != 0` |
| `subComRingType` | No alias in 2.5. Prefer `subComPzRingType`; `subComNzRingType` works but warns `deprecated since mathcomp 2.4.0` (upstream self-alias, algebra/ssralg.v:7099) |
| `unitRingType` | Unchanged, not deprecated |

**Removed lemma names (no alias left)**

| mathcomp 1.x | mathcomp 2.5 | Needs |
|---|---|---|
| `ler_add` | `lerD` | `Import Num.Theory` |
| `ler_add2l` | `lerD2l` | `Import Num.Theory` |
| `ltr_pmul2l` | `ltr_pM2l` | `Import Num.Theory` |
| `ler_trans` | `le_trans` | `Import Order.TTheory` |
| `ltr_le_trans` | `lt_le_trans` | `Import Order.TTheory` |
| `rmorphX` | `rmorphXn` | `Import GRing.Theory` |

Stable, compile as in the book: ssrnat/div/bigop basics (`addnC`,
`mulnS`, `divnMDl`, `big_nat_recr`, `big_nat1`).

**Changed statements and status**

(Book statements: MCB §4.2.1, §4.2.2, §5.5, §7.2.1; the other rows are
mathcomp 1.x.)

| Name | 2.5 behaviour |
|---|---|
| `count_uniq_mem` | `uniq s -> count_mem x s = (x \in s)` (boot/seq.v:1360) |
| `maxn_idPl` | A `reflect` view (boot/ssrnat.v:768); `rewrite (maxn_idPl h)` still works via `elimT` |
| `pdivP` | Returns a `sig2`: `{p \| prime p & p %\| n}` (boot/prime.v:561) |
| `fact_gt0` | `` n`! > 0 `` (boot/ssrnat.v:1375) |
| `idempotent` | Deprecated since 2.3.0: use `idempotent_op` (boot/ssrfun.v:39) |
| `addn_rec` / `muln_rec` / `subn_rec` | Deprecated since 2.3.0 (boot/ssrnat.v:196). The operators are `simpl never` (§49.4) |
| `insub` | Plain `Definition` (boot/eqtype.v:596). Reason with `insubT` / `insubN` / `insubP` |
| `leP` / `ltP` | Under `Import Order.TTheory` they are Order's case lemmas and shadow ssrnat's `nat` bridges (§28.1) |

**Proof language**

(Book forms: MCB §2.3.3, §2.5.1, §3.7, §4.3.3, §6.7.1, §7.1, Part III
cheat sheet.)

| Book / 1.x | mathcomp 2.5 / Rocq 9 |
|---|---|
| `Search _ pat` (first pattern = conclusion head) | `Search pat`; restrict with `Search concl:(pat)` (`headconcl:(f _)` only for predicate-headed statements) (§37.1) |
| `Hint Resolve lem.` | Warns `implicit-core-hint-db`: write `#[export] Hint Resolve lem : core.` (§37.9) |
| `have {H}H` / `move=> {H}H` | Warns `duplicate-clear`: write `{}H` (§27.11) |
| `elim: n.+1 {-2}n (ltnSn n)`, `strong_nat_ind` | `elim/ltn_ind` or `ubnP` (templates.md §21) |
| `{-2}x (erefl x)` generalisation | `case E: x` (§27.10) |
| Occurrence numbers `rewrite {2}addnC` | Context patterns `rewrite [in RHS]addnC`, `[X in _ = X]addnC` (§8) |
| Book-local notations `[LHS of …]`, `[unify … with …]` | Not in the library: use `Check`, `Set Printing All`, `HB.about` (§35.7) |
| `\big[+%N/0]`, `\big[*%N/1]`, `\big[*%M/1]` (book operator names) | Syntax error: `Local Notation`s of boot/bigop.v. Write `\sum`/`\prod` (§34.1) or name the constant: `\big[addn/0]`, `\big[muln/1]`, `\big[maxn/0]`; `+%R`/`*%R` in ring_scope |

### 48.3 Worked translations

Equality and sub-type instances (MCB §7.2, §8.1):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Inductive color := Red | Blue.
Definition eqc (a b : color) :=
  match a, b with Red, Red | Blue, Blue => true | _, _ => false end.
Lemma eqcP : Equality.axiom eqc. Proof. by do 2 case; constructor. Qed.

(* mathcomp 1.x style (cf. MCB §8.1; not a book example):        *)
(*   Canonical color_eqType := EqType color (EqMixin eqcP).      *)
(* mathcomp 2.5 / HB:                                            *)
HB.instance Definition _ := hasDecEq.Build color eqcP.
Check (color : eqType).

(* mathcomp 1.x style (cf. MCB §7.2; the book has no pos):          *)
(*   Canonical pos_subType := Eval hnf in [subType for pval].       *)
(*   Canonical pos_eqType := EqType pos [eqMixin of pos by <:].     *)
Record pos : predArgType := Pos { pval :> nat; _ : 0 < pval }.
HB.instance Definition _ := [isSub for pval].
(* 1.x lines: eqType only; one line now gives Equality+Choice+Countable *)
HB.instance Definition _ := [Countable of pos by <:].
Check (pos : countType).
```

Algebraic instances (MCB §8.1). `'I_p` is already a ring in the
library, so the first translation is shown as a comment:

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.

(* book: Definition Zp_zmodMixin :=                                *)
(*         ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.           *)
(*       Canonical Zp_zmodType := ZmodType 'I_p Zp_zmodMixin.     *)
(* 2.5 (algebra/zmodp.v:152), already in the library:             *)
(*   HB.instance Definition _ :=                                   *)
(*     GRing.isZmodule.Build 'I_p                                  *)
(*       (@Zp_addA _) (@Zp_addC _) Zp_add0z Zp_addNz.              *)

(* book: Canonical Zmn_ringType := [ringType of Zmn].             *)
Definition Zmn := ('Z_3 * 'Z_5)%type.
HB.instance Definition _ := GRing.NzRing.copy Zmn ('Z_3 * 'Z_5)%type.
Check (Zmn : nzRingType).
```

Monoid laws for bigops (MCB §6.7.2 for `Monoid.Law`, §8.2 for
`ComLaw`; canonical home §34.10):

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

(* book: Canonical myop_monoid := Monoid.Law addnA add0n addn0.  *)
(*       Canonical myop_comoid := Monoid.ComLaw addnC.           *)
Definition myop := addn.
HB.instance Definition _ :=
  Monoid.isComLaw.Build nat 0 myop addnA addnC add0n.
Check (myop : Monoid.com_law 0).
Lemma big_myop n : \big[myop/0]_(i < n) 0 = 0.
Proof. by rewrite big_const_ord; elim: n => //= n ->. Qed.
```

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
- [ ] Imports use `all_boot`/`all_order` (or upstream's
  `all_ssreflect_compat` in analysis ≥ 1.16), no new `all_ssreflect`;
  the three implicit-argument flags follow the imports (§3, §5)
- [ ] No structure name deprecated since mathcomp 2.4 (`ringType`,
  `comRingType`, `semiRingType`, …); pick the weakest Pz/Nz level
  (§36.2)

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
- [ ] No `Focus` or focusing braces `{ ... }` in proofs (clear items
  `{}h` are fine, §8)
- [ ] Tactic spacing: `move=>`, `apply/`, `apply:` (no space);
  `rewrite /def` (space)
- [ ] No numerical occurrence selectors in proofs
- [ ] Bullets use `-`, `+`, `*` hierarchy
- [ ] Indentation: 2 spaces for branches, `last first` to keep main
  flow at outer level (Section 27.8)
- [ ] Every branch ends with `by` / `exact:` / `done`; bullets are
  inert under mathcomp and do not check closure (§26.5)
- [ ] No `auto`/`eauto`/`intuition`/`firstorder` closers; `tauto`
  only on classical `Prop`/set goals (§22.5)
- [ ] nat case splits use `leqP`/`ltnP`/`ltngtP`, not ssrnat
  `leP`/`ltP` (§28.1)
- [ ] `?rule` only on side-condition rewrites, immediately followed by
  `//`; main-goal rewrites stay strict (§29.3)
- [ ] `have {}H` / `move/v: H => {}H`, never `have {H}H` (§27.11)
- [ ] Lemmas end with `Qed`; `Defined` only with a comment saying why
  (§8)

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
- [ ] Instances for new types via `X.copy T (pcan_type fK)`, or
  `[isSub for v]` then `[X of S by <:]` (§36.12, §36.13)
- [ ] No mathcomp-1 idioms (`EqMixin`, `[eqType of T]`,
  `Canonical … Pack`) (§48)

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
- Assia Mahboubi and Enrico Tassi, *Mathematical Components*, Zenodo,
  2022 (draft v1.0.2, 2022-09-28),
  [doi:10.5281/zenodo.3999478](https://doi.org/10.5281/zenodo.3999478)
  (version record 10.5281/zenodo.7118596); HTML/PDF at
  <https://math-comp.github.io/mcb/>. Targets Coq 8 / mathcomp 1.x
  (pre-HB): read §48 before reusing its code. Cited as "(MCB §x.y)".
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
