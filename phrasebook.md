# Phrasebook — intent to ssreflect/mathcomp idiom

> An **intent-first** index. You are mid-proof, you know *what you want
> to do in English*, and you want the idiomatic ssreflect/mathcomp
> chord in seconds. This is the inverse of `templates.md` (keyed by
> goal **shape**) and of `reference.md` (keyed by **rule**).

## How to use this file

1. Find the table whose heading matches your intent ("introduce…",
   "decide…", "rewrite…", "close…").
2. Read the row: **intent → idiom → cross-ref**.
3. Follow the `(§N)` to the full rule / worked example. Per the guide
   convention: `(§N)` with `N ≤ 37` lives in `reference.md`; `N ≥ 38`
   lives in `domains/<N>_<topic>.md`. `templates.md §k` refs are
   spelled out in full.

Every idiom below is current mathcomp 2.5 / analysis 1.16 ssreflect.
Subtle preconditions are noted inline.

---

## 1. Introduce + transform in one `move=>`

The intro-pattern after `move=>` (or trailing a `case:` / `apply:`)
does book-keeping *as it introduces*. Never `move=> H` then act on
`H` next line — fold the action in.

| intent | idiom | ref |
|---|---|---|
| intro hyp + rewrite L→R by it | `move=> ->` | §27.1 |
| intro hyp + rewrite R→L by it | `move=> <-` | §27.1 |
| intro + discard (don't name) | `move=> _` | §27.2 |
| intro + destruct a conjunction | `move=> [a b]` | §27.5, §28.3 |
| intro + destruct a disjunction | `move=> [a \| b]` | §28.3 |
| intro + destruct an `exists` | `move=> [x Px]` | §27.5 |
| intro, keep for `//` (no name) | `move=> ?` | §27.6 |
| name only if reused several× | `move=> Hname` | §14, §27.6 |
| `case:` then intro both pieces | `case=> a b` | §28.1, §28.3 |

`move=> [a b]` and `case=> a b` coincide on a single top hypothesis;
prefer `move=> [a b]` when already introducing, `case=> a b` when
splitting the conclusion's first premise. Don't write
`move=> H; case: H => a b` (§28.3).

---

## 2. Apply a view while introducing

A `/view` inside an intro-pattern applies the view to the hypothesis
*as it is introduced*, replacing the `move=> H; move/view: H`
two-step (§27.3, §27.7).

| intent | idiom | ref |
|---|---|---|
| intro `a == b`, rewrite by it | `move=> /eqP->` | §27.7, §36.9 |
| intro `a == b` as eqn, keep it | `move=> /eqP eqab` | §36.9 |
| split intro'd `_ && _` | `move=> /andP[h1 h2]` | §28.1 |
| split intro'd `_ \|\| _` | `move=> /orP[h1\|h2]` | §28.1 |
| feed intro'd hyp through a view | `move=> /myview h` | §27.3 |
| view then rewrite by result | `move=> /eq_foo->` | §27.7 |

The `/` chains left-to-right: `move=> /eqP/andP[h1 h2]` applies
`eqP` then `andP` to the same incoming hypothesis.

---

## 3. Case-split on a boolean decision

These keep the **goal in equational/boolean form** so it can be
chained — mathcomp culture over raw `destruct` (§28).

| intent | idiom | ref |
|---|---|---|
| split on the test of an `if` | `case: ifP => Hc` | §34 (l.2312) |
| same, `else` arm negated | `case: ifPn => Hc` | §28.1 |
| split a generic `b : bool` | `case: b` | §28.1 |
| split `b`, name fact each side | `case: (boolP b)` | §28.1 |

`ifP` yields `Hc : c = true` / `c = false` (the raw test value);
`ifPn` yields `c` / `~~ c` as reflected facts — pick `ifPn` when the
negated form is what later rewrites need.

---

## 4. Decide an order comparison

Reflection-style splits that leave equations, not opaque `is_true`
hypotheses (§28.1).

| intent | idiom | ref |
|---|---|---|
| `m <= n` vs `n < m` on `nat` | `case: leP` | §28.1 |
| `m < n` vs `n <= m` on `nat` | `case: ltP` | §28.1 |
| three-way `<` / `=` / `>` | `case: ltgtP` | §28.1 |
| three-way with `->` on eq arm | `have [..\|\|->] := ltgtP x y` | §28.1 |
| `<=` / `>` in ordered field/num | `case: lerP` | §28.1 |
| `<` / `>=` in ordered field/num | `case: ltrP` | §28.1 |
| `leP`-analogue on a real domain | `case: real_leP` | §28.1 |

`leP` / `ltP` are the `nat` forms; `lerP` / `ltrP` / `ltgtP` are the
`Order` / `ssrnum` forms over `porderType` / `numDomainType`. Use the
`have [..] := ltgtP x y` placement when the equality branch should
land as a rewrite `->` into the main flow (§28.1 example).

---

## 5. Decide an equality (with the off-branch hyp)

| intent | idiom | ref |
|---|---|---|
| `x = y` vs `x != y`, no residual | `case: eqVneq` | §28.1 |
| same, rewrite on equal branch | `case: eqVneq => [->\|hne]` | §28.1 |
| same, placed forward | `have [->\|hne] := eqVneq x y` | §28.1 |
| pred `P`, keep `~~ P` off-branch | `case: (altP P)` | §28.1 |
| reflect-residual split | `case: altP` | §28.1 |

`eqVneq` gives `x = y` / `x != y` (the off branch is a `!=`, ready to
discharge `_ != 0` side goals with `//`). `altP myReflectP` gives the
reflected `Prop` on one branch and `~~`-negation on the other — use it
when you want the off-branch in `bool` form. Don't
`case: (eqVneq x y) => H` then `rewrite H`; fold to `=> [->|hne]`
(§28.1).

---

## 6. Prove a conjunction / split goal

| intent | idiom | ref |
|---|---|---|
| `A /\ B`, two short branches | `by split; [..\|..]` | §27.8 |
| `A /\ B`, first branch trivial | `split=> //; <rest>` | §28.3 |
| split + intro into each branch | `split=> [a\|b]` | §28.3 |
| set-equality two-inclusion split | `apply/seteqP; split=> x` | tmpl §9 |
| iff via reflect each side | `apply/idP/idP` | §37.6 |

**No bullets when only two subgoals are generated** — use
`by split; [t1 \| t2]` for a one-liner, or 2-space indent + an
un-indented second goal for multi-line branches (§27.8). Reserve
`-` / `+` / `*` bullets for three or more subgoals.

---

## 7. Forward a fact into the proof

| intent | idiom | ref |
|---|---|---|
| establish `T`, reuse by name | `have hname : T by …` | §27.6 |
| establish `T` only for later `//` | `have ? : T by …` | §27.6 |
| surface a top lemma into `//` pool | `have ? := lemma args.` | §27.6 |
| establish `T`, rewrite by it | `have -> : T by …` | §27.6, §27.1 |
| factor an in-proof lemma | `gen have lem, _ : x / P x` | §30.2 |
| specialise an existing hyp | `have h2 := h x y.` | §27.6 |

`have ? : T by …` requires a **single-line** `by` sub-proof; if it
needs a bulleted multi-line split, name it instead (§27.6 parser
caveat). The anonymous `?` front-loads positivity / non-zeroness so
later `rewrite lemma//` chains shrink to one line.

---

## 8. Rewrite under a binder / bigop / integral

`under` rewrites *inside* a `\sum` / `\prod` / `\int` body without
breaking it into a goal-tower (§29.1, §34.3).

| intent | idiom | ref |
|---|---|---|
| each summand of `\sum`/`\prod` | `under eq_bigr => i Pi do <t>` | §34.3 |
| the predicate side of a bigop | `under eq_bigl => i do <t>` | §34.3 |
| both range-pred and body | `under eq_big => [i\|i Pi] …` | §34.3 |
| only the LHS bigop | `under [LHS]eq_bigr do <t>` | §34.3 |
| integrand of `\int[mu]_x f x` | `under eq_integral do <t>` | §43.6 |
| one side's integrand only | `under [LHS]eq_integral do <t>` | §43.6 |
| body of a `lim` / `cvg` | `under eq_cvg => n do <t>` | §29.1, tmpl §2 |
| multi-line body (no `do`) | `under eq_bigr => i Pi.` … `over.` | §34.3 |

Without `do`, `under` opens a sub-proof closed by `over.` (§34.3). To
*prove* an integral equality pointwise instead, use
`apply: eq_integral => x _` (templates.md §5).

---

## 9. Prove a `near` / filter goal

For `\forall x \near F, P x`: open the filter, prove `P x`, push the
witness side-goals back via `near: x`, then discharge the shelved
existentials (§30.3, §44.5, templates.md §1).

| intent | idiom | ref |
|---|---|---|
| open filter, intro near point | `near=> x` | §30.3, §44.5 |
| push "x close to …" to filter | `near: x` | §44.5 |
| run a tactic under the filter | `near do <t>` | tmpl §1 |
| close existentials (modern) | `Unshelve. all: by end_near.` | §44.5 |
| close (legacy form) | `Grab Existential Variables. all: end_near.` | §44.5 |
| one-shot pointwise lift | `apply: filterS2` / `filterS3` | §44.4 |
| `nbhs x`: exhibit a ball ε | `apply/nbhs_ballP; exists ε` | tmpl §1b, §30.5 |
| `nbhs x`: exhibit a norm ε | `apply/nbhs_normP; exists ε` | tmpl §1b, §30.5 |

Always pair `near=>` with its closer; forgetting
`Unshelve. all: by end_near.` leaves shelved goals at `Qed` (§44.5).
When ε need not shrink, prefer `filterS2`/`filterS3` over `near=>`
(§44.4).

---

## 10. WLOG by symmetry

| intent | idiom | ref |
|---|---|---|
| assume `x <= y` WLOG | `wlog: x y / x <= y` | §30.1 |
| name symmetry hyp + case | `wlog: x y / x <= y => [hsym\|xy]` | §30.1 |
| WLOG a sign normalisation | `wlog: x / 0 < x => [h\|x0]` | §30.1 |

The first branch (`hsym`) must discharge the symmetric case by
re-applying the WLOG'd statement; a `case: leP` / `ltgtP` typically
feeds it (§30.1 example).

---

## 11. Classical / decidability case-split

`mathcomp-analysis` is classical via `mathcomp/classical/boolp.v`
(§36.4, §36.5, templates.md §15).

| intent | idiom | ref |
|---|---|---|
| classically split a `Prop` | `have [h\|h] := pselect P` | §36.5, tmpl §15 |
| same, inline | `case: (pselect P) => [h\|h]` | §36.5 |
| split on inhabitation of `X` | `have [h\|x0] := pselectT X` | tmpl §15 |
| switch a `Prop` to `bool` | `have /asboolP h := H` | §36.4 |
| witness from `exists x, P x` | `have [x Px] := cid H` | §36.5 |

Do **not** `destruct (pselect P)` — that is not ssreflect style; use
`have [..] := pselect P` or `case: (pselect P)` (§36.5).

---

## 12. Close the goal

| intent | idiom | ref |
|---|---|---|
| close trivial/assumption/compute | `by []` | §22.1, §26 |
| close a one-liner that does work | `by <tac>` | §26.1 |
| term solves the goal exactly | `exact: term` | §26.2 |
| term solves with trivial residue | `exact: term` | §26.2 |
| discharge trivial goal mid-chain | `… //` | §26.4 |
| discharge trivial goal + simplify | `… //=` | §26.4 |
| standalone `by []` synonym | `done` | §26 |

Every goal-closing line must start with `by` or be an `exact:` —
`apply:` alone should never close a goal (§26.2). `//` inside a chain
is `by []`; `//=` is `by []` plus `simpl` (§26.4).

---

## 13. Ring / field identity

`(§45)` is the decision tree; the head call is one of two (§45.3).

| intent | idiom | ref |
|---|---|---|
| polynomial identity, `comRingType` | `by ring` | §45.3 |
| identity with `^-1` over a field | `by field` | §45.3 |
| ring identity modulo eqns `H` | `by ring: H` | §45.3 |
| field identity discharging `H` | `field: H` | §45.3 |
| linear (in)equality, real field | `by lra` | §45.4 |
| nonlinear (in)equality | `by nra` / `by psatz` | §45.4 |
| `nat`/`int` lifted to `Z` | `zify; lia` | §45.5 |

`ring` does **not** know `^-1`; reach for `field`, which emits
`denominator != 0` side conditions to discharge afterward. For
numeral denominators over a `numFieldType` these close automatically
(§45.3).

---

## 14. Disambiguation — frequent LLM mistakes

The same English word maps to **different** tactics in ssreflect vs
vanilla Coq. Getting these wrong is the most common generated-proof
failure.

| if you mean… | ssreflect | not (vanilla) | ref |
|---|---|---|---|
| rewrite, chained | `rewrite l1 l2 //` | `rewrite l1; rewrite l2` | §29 |
| case-split, **consuming** | `case: h` | `case h` / `destruct h` | §28.1 |
| induct, **consuming** | `elim: n` | `induction n` | §28.1 |
| view an **incoming hyp** | `move=> /view` | `apply/view` as intro | §27.3 |
| switch the **goal** via view | `apply/view` | (not `move=>`) | §37.6 |
| apply a lemma, **consuming** | `apply: lem` | `apply lem` | §26.2 |
| close exactly with a term | `exact: t` | `exact t` | §26 |

Key distinctions, spelled out:

- **`rewrite` (ssr) vs `rewrite` (vanilla)**: ssreflect `rewrite` is
  multi-rule, multi-direction, occurrence-aware —
  `rewrite l1 -l2 [in RHS]l3 //`. Never emit `rewrite l1; rewrite l2`
  when one `rewrite l1 l2` suffices (§29.3, §29.2).
- **`case:` / `elim:` (consume) vs `case` / `elim`**: the trailing
  `:` **moves the named item into the goal** before splitting —
  `case: h` / `elim: n IHn` is the idiom. Bare `case` / `elim`
  operate on the goal's top and are rarely what you want (§28.1).
- **`move=> /view` vs `apply/view`**: `/view` in an intro-pattern
  transforms a **hypothesis being introduced**; `apply/view`
  transforms the **goal** through the reflection lemma. Not
  interchangeable (§27.3 vs §37.6).
- **`apply:` vs `apply`**: `apply:` is the ssreflect form — it can
  consume hypotheses given after it (`apply: lem h1 h2`) and unifies
  more aggressively. Prefer `apply:`; prefer `exact:` when the term
  closes the goal (§26.2).

---

## 15. Quick cross-reference map

| intent group | this file | `templates.md` sibling |
|---|---|---|
| intro + transform | §1, §2 | — |
| boolean / order / eq splits | §3, §4, §5 | §14 (finite split) |
| conjunction / set split | §6 | §8, §9 (extensionality) |
| forward `have` / `wlog` | §7, §10 | — |
| under-binder rewrite | §8 | §5, §6, §7 (eq.) |
| `near` / filter | §9 | §1, §1b |
| classical | §11 | §15 (`decidable P`) |
| closing / ring | §12, §13 | §12 (ring identity) |
