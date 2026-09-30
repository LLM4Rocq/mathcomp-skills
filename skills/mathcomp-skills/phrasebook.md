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
   convention: `(§N)` with `N ≤ 37` or `N = 48` lives in `reference.md`;
   `38 ≤ N ≤ 47` and `N = 49` live in `domains/<N>_<topic>.md`.
   `templates.md §k` refs are spelled out in full (`tmpl §k` in tables);
   `§k (here)` and the "this file" column of the closing map point into
   this file.

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
| hyp `n.+1 = m.+1`, use `n = m` | `move=> [->]` / `case=> ->` / `move/succn_inj` | §27.5, §29.7 |
| hyp `x :: s = y :: t` | `case=> -> ->` | §27.5, §29.7 |
| hyp `Some a = Some b` | `case=> ->` | §27.5, §29.7 |
| same, stated in `bool` | `eqSS`, `eqseq_cons` | §49.4 |
| specialise a ∀-hyp as you intro | `move=> /(_ x) h` | §27.5, §27.12 |
| feed a premise as you intro | `move=> /(_ _ hx) h` | §27.12 |
| specialise a hyp in place | `move/(_ x) in H` | §27.12 |
| rewrite in a hyp / hyp and goal | `rewrite E in H` / `rewrite E in H *` | §27.10 |
| rewrite by `h`, then clear it | `rewrite {}h` | §27.11 |
| clear a dead hyp | `move=> {h}` | §27.11 |

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
| split intro'd `[&& a, b & c]` | `move=> /and3P[ha hb hc]` (`and4P`, `and5P`) | §36.7 |
| prove `[&& a, b & c]` | `apply/and3P; split` | §36.7 |
| split intro'd `[\|\| a, b \| c]` | `case/or3P=> [ha\|hb\|hc]` (`or4P`) | §36.7 |
| use intro'd `[forall x, P x]` at `x` | `move=> /forallP/(_ x) Px` | §40.9, §27.12 |
| prove `[forall x, P x]` | `apply/forallP => x` | §40.9 |
| destruct intro'd `[exists x, P x]` | `move=> /existsP[x Px]` | §40.9 |
| prove `[exists x, P x]` | `apply/existsP; exists x` | §40.9 |
| negated `[forall]` / `[exists]` | `move=> /forallPn[x nPx]` / `/existsPn h` | §40.9 |
| feed intro'd hyp through a view | `move=> /myview h` | §27.3 |
| view then rewrite by result | `move=> /eq_foo->` | §27.7 |
| split `&&` and view one side | `move=> /andP[/eqP-> h]` | §27.5 |

`/V1/V2` applies `V1`, then `V2` **to `V1`'s result**
(`move=> /eqP/esym` turns `x == y` into `y = x`); it only makes sense
when `V1`'s output has `V2`'s input shape. To apply different views to
the pieces of a conjunction, **nest** them inside the brackets:
`move=> /andP[/eqP-> h]` splits `(x == y) && b`, rewrites by `x = y`
and names `h : b` (MCB §5.1.3). `move=> /eqP/andP[h1 h2]` fails:
`andP` cannot consume what `eqP` returns.

`a && b && c` parses as `(a && b) && c`, so `/and3P` does not match
it: state `[&& a, b & c]` (MCB §1.2.1, §1.3.1, §1.7), or nest
`/andP[/andP[ha hb] hc]`.

```coq
From mathcomp Require Import all_boot.

Lemma and3_mid (a b c : bool) : [&& a, b & c] -> b.
Proof. by case/and3P. Qed.

Lemma and3_intro (a b c : bool) : a -> b -> c -> [&& a, b & c].
Proof. by move=> ha hb hc; apply/and3P. Qed.

Lemma or3_ex (a b c : bool) : [|| a, b | c] -> a || b || c.
Proof. by case/or3P=> ->; rewrite ?orbT. Qed.

(* a && b && c is (a && b) && c: /and3P does not match, nest /andP *)
Lemma and_nested (a b c : bool) : a && b && c -> b.
Proof. by move=> /andP[/andP[_ hb] _]. Qed.
```

---

## 2b. Apply a view to the goal or to a term

(MCB §5.1.3-§5.1.4.) Outside an intro-pattern a view goes after
`apply/` (on the goal), after `case/` or `move/` (on a term pushed with
`:`), or inside `rewrite (VP h)`.

| intent | idiom | ref |
|---|---|---|
| goal `a && b` → two goals | `apply/andP; split` | §37.6 |
| goal `a \|\| b`, prove the left side | `apply/orP; left` | §37.6 |
| goal `a ==> b` → `a -> b` | `apply/implyP => ha` | §37.6 |
| goal `~~ b` → `~ b` | `apply/negP => hb` | §37.6 |
| case-split a lemma's boolean result | `case/orP: (leq_total m n) => [le\|ge]` | §28.3 |
| view a named hyp, re-intro the pieces | `move/andP: h => [h1 h2]` | §27.3 |
| rewrite with a view applied to a hyp | `rewrite (maxn_idPl le_nm)` | §36.9 |
| reshape a bool goal before a view | `rewrite -implyNb -ltnNge; apply/implyP` | §36.3 |

- **Stay boolean while rewriting; switch to `Prop` through a view only
  to destructure or to introduce** (§36.3).
- A `reflect` lemma works in both directions and on `~~`/`= false`
  forms: Corelib `ssr/ssrbool.v` declares hint views (`introT`,
  `elimT`, `elimTF`, …). `rewrite (VP h)` works because `elimT` is a
  coercion from `reflect P b` to `b -> P`.

```coq
From mathcomp Require Import all_boot.

Lemma maxn_cases n1 n2 : maxn n1 n2 = n1 \/ maxn n1 n2 = n2.
Proof.
by case/orP: (leq_total n2 n1) => [/maxn_idPl -> | /maxn_idPr ->];
  [left | right].
Qed.

Lemma or_goal m n (b : bool) : (m <= m + n) || b.
Proof. by apply/orP; left; exact: leq_addr. Qed.

Lemma or_via_imp m n : (n <= m) || (0 < n).
Proof.
rewrite -implyNb -ltnNge; apply/implyP => lt_mn.
exact: leq_ltn_trans (leq0n m) lt_mn.
Qed.
```

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

Spec-lemma splits: one `case:` substitutes every occurrence of the
comparison in the **goal** by `true` / `false` in each branch (§28.1).

| intent | idiom | ref |
|---|---|---|
| `m <= n` vs `n < m` on `nat` | `case: leqP` / `case: (leqP m n)` | §28.1 |
| `m < n` vs `n <= m` on `nat` | `case: ltnP` | §28.1 |
| three-way on `nat`, `->` on eq arm | `have [lt\|gt\|->] := ltngtP m n` | §28.1 |
| `n == 0` vs `0 < n` on `nat` | `case: posnP` | §28.1 |
| `x <= y` vs `y < x`, `orderType` | `case: leP` / `case: ltP` | §28.1 |
| three-way, `orderType` | `case: ltgtP` | §28.1 |
| same, `->` on eq arm, `orderType` | `have [..\|\|->] := ltgtP x y` | §28.1 |
| `<=` / `>` on a `realDomainType` | `case: lerP` | §28.1 |
| `<` / `>=` on a `realDomainType` | `case: ltrP` | §28.1 |
| same on `numDomainType`, `\is real` | `case: real_leP` | §28.1 |

On `nat` use `leqP` / `ltngtP` (MCB §5.2.1), `ltnP` and `posnP`;
`leqP` / `ltnP` indices also rewrite `minn` / `maxn` (ssrnat.v). ssrnat's `leP` / `ltP` are
Stdlib bridges (`reflect (m <= n)%coq_nat (m <= n)`): `case: leP` leaves
`%coq_nat` hypotheses. Under `Import Order.TTheory` the name `leP` means
Order's lemma, and `case: leP` on a `nat` goal fails with
*Pattern (leP _ _) was not completely instantiated*; write `ssrnat.leP`
for the bridge (§28.1). The `orderType` rows need `Import Order.TTheory`
and a total order; `lerP` / `ltrP` need `Import Num.Theory`. Use the
`have [..] := ltgtP x y` placement when the equality branch should land
as a rewrite `->` into the main flow; the goal must still mention `x`
after the split, else name the equation instead of `->`.

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

## 6. Prove a conjunction, existential or disjunction / split goal

| intent | idiom | ref |
|---|---|---|
| `A /\ B`, two short branches | `by split; [..\|..]` | §27.8 |
| `A /\ B`, first branch trivial | `split=> //; <rest>` | §28.3 |
| split + intro into each branch | `split=> [a\|b]` | §28.3 |
| set-equality two-inclusion split | `apply/seteqP; split=> x` | tmpl §9 |
| `b1 = b2` in `bool`, reflect each side | `apply/idP/idP` / `apply/V1/V2` | tmpl §22 |
| prove `reflect P b` | `apply: (iffP idP) => [hb\|hP]` (or `iffP andP`, …) | tmpl §22 |
| exhibit a witness | `by exists w` / `exists w => //` | MCB §3.6, §4.2.1 |
| several witnesses | `by exists x, y` | — |
| pick a disjunct (`Prop` `\/`) | `by left` / `by right; apply: …` | MCB §3.6, §5.1.1 |
| pick a disjunct (`bool` `\|\|`) | `apply/orP; left` / `by rewrite h orbT` | §2b (here) |
| goal `True` | `by []` | §22.1 |
| two goals, close one inline | `t; first by t1` / `t; last by t2` | §27.9 |
| one tactic per goal | `t; [t1 \| t2]` / `t; [t1 \| t ..]` | §27.9 |

**No bullets when only two subgoals are generated** — use
`by split; [t1 \| t2]` for a one-liner, or 2-space indent + an
un-indented second goal for multi-line branches (§27.8). Reserve
`-` / `+` / `*` bullets for three or more subgoals.

Don't write `eexists`, `exact (ex_intro _ w h)` or `destruct` on
`False`: use `exists w`, and `by []` / `by case: f` (a skill
convention; `ex` / `False` elimination: MCB §3.6; `exists`: MCB §4.2.1).
`first by` fails unless it closes its goal; a bare `first t` does not.

```coq
From mathcomp Require Import all_boot.

Lemma ex_ex : exists n, 2 < n. Proof. by exists 3. Qed.
Lemma ex2_ex : exists m n, m + n = 3. Proof. by exists 1, 2. Qed.
Lemma or_ex n : n = 0 \/ 0 < n.
Proof. by case: n => [|n]; [left | right]. Qed.
Lemma absurd_ex n (h : n.+1 = 0) : n = 42. Proof. by []. Qed.
Lemma false_ex (f : False) : 0 = 1. Proof. by case: f. Qed.
```

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
| reduce goal to `S`, prove `S` last | `suff h : S.` / `suff h : S by …` | §30.7 |
| prove a fact and destruct it | `have /andP[h1 /eqP->] : b1 && (x == y) by …` | §30.7 |
| prove `x == y`, keep it as `=` | `have /eqP xy : x == y by …` | §30.7 |
| symmetric sub-argument | `have th x y : y <= x -> … by …` | §30.7 |
| abbreviate a subterm | `set t := (pat)` / `set t := (X in _ = X)` | §30.8 |
| abbreviate it in a hyp too | `set t := pat in h` / `… in h *` | §30.8 |
| local helper function | `pose f x := …` | §30.8 |

`have ? : T by …` requires a **single-line** `by` sub-proof; if it
needs a bulleted multi-line split, name it instead (§27.6 parser
caveat). The anonymous `?` front-loads positivity / non-zeroness so
later `rewrite lemma//` chains shrink to one line.

A view pattern after `have` applies **after** the sub-proof: the `by`
proves the stated boolean form (MCB Part III, cheat sheet). Prefer it
to `have h : A && B by …; move/andP: h => [h1 h2]`.

```coq
From mathcomp Require Import all_boot.

Lemma hv (a b c : nat) (P : pred nat) (h : P a && (b == c)) : b = c.
Proof. by have /andP[_ /eqP->] : P a && (b == c) by []. Qed.

Lemma sf m n (h : m <= n) : m < n.+2.
Proof.
suff h1 : m < n.+1 by exact: ltn_trans h1 _.
by rewrite ltnS.
Qed.
```

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
re-applying the WLOG'd statement; a `case: leqP` (`nat`) or
`case: leP` / `ltgtP` (ordered types) typically feeds it (§30.1
example).

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
| closed by computation (`0 < n.+1`) | `by []` (also `size [:: a; b] = 2`) | §22.1 |
| lemma needs a computable fact | pass `(isT : 1 < p.+2)` as the argument | §22.1 |
| use `h : b` inside `&&`/`\|\|`/`if` | `rewrite h /=` | §36.3 |
| rewrite with `nb : ~~ b` | `rewrite (negbTE nb)` / `move=> /negPf ->` | §36.3 |
| absurd `0 = n.+1`, `[::] = x :: s`, `true = false` | `by []` (`by case` warns `spurious-ssr-injection`) | §22.1, §29.7 |
| hyp `f : False` | `by case: f` | MCB §3.6 |
| expose a successor under `+`/`*` | `rewrite addSn` / `addnS` / `mulSn` (not `/=`) | §49.4 |

Every goal-closing line must start with `by` or be an `exact:` —
`apply:` alone should never close a goal (§26.2). `//` inside a chain
is `by []`; `//=` is `by []` plus `simpl` (§26.4).

---

## 13. Ring / field identity

`(§45)` is the decision tree; the head call is one of two (§45.3).

| intent | idiom | ref |
|---|---|---|
| polynomial identity, `comPzRingType` | `by ring` | §45.3 |
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
| induct, **consuming** | `elim: n => [\|n IHn]` | `induction n` | tmpl §21 |
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
  `case: h` / `elim: n => [|n IHn]` is the idiom. Names after `:` are
  **pushed** (generalized); names after `=>` are **introduced** (MCB
  §2.2.2, §2.3.4, §4.1).
  `elim: n IHn` fails with *The variable IHn was not found in the
  current environment*. Bare `case` / `elim` operate on the goal's top
  and are rarely what you want (§28.1; induction shapes in
  templates.md §21).
- **`move=> /view` vs `apply/view`**: `/view` in an intro-pattern
  transforms a **hypothesis being introduced**; `apply/view`
  transforms the **goal** through the reflection lemma. Not
  interchangeable (§27.3 vs §37.6).
- **`apply:` vs `apply`**: `apply:` is the ssreflect form — it can
  consume hypotheses given after it (`apply: lem h1 h2`) and unifies
  more aggressively. Prefer `apply:`; prefer `exact:` when the term
  closes the goal (§26.2).

---

## 15. Induct

(MCB §2.3.4, §3.7, §5.3.) Skeletons, pitfalls and worked examples live
in templates.md §21. The
mechanics of pushing items before `elim` (`elim: n m`, `in m *`) are
in §27.10.

| intent | idiom | ref |
|---|---|---|
| structural induction on `nat` | `elim: n => [\|n IHn]` | tmpl §21 |
| same, base case closed by `done` | `elim: n => // n IHn` | tmpl §21 |
| structural induction on a `seq` | `elim: s => [\|x s IHs]` | tmpl §21 |
| generalize `m` so the IH quantifies it | `elim: n m => [\|n IHn] m` | tmpl §21, §27.10 |
| same, without re-listing `m` | `elim: n => [\|n IHn] in m *` | tmpl §21, §27.10 |
| IH for every smaller value | `elim/ltn_ind: n => n IHn` | tmpl §21 |
| least `n` with `P n` (minimal witness) | `case: (ex_minnP exP) => m Pm m_min` | §49.11 |
| induct on a size / measure | `have [k] := ubnP (size s); elim: k => // k IHk in s *` | tmpl §21 |
| `seq` from the right (`rcons`) | `elim/last_ind: s => [\|s x IHs]` | tmpl §21 |
| polynomials (`all_algebra`) | `elim/poly_ind: p => [\|p c IHp]` | §39.8 |
| two bigops in lockstep | `elim/big_rec2: _ => // i y1 y2 _ ->` | tmpl §21 |
| consume the IH (used once) | `rewrite {}IHn` / `rewrite -{}IHn` | §27.11 |

- Never `intros; induction n`, and never a numeric occurrence selector
  to load a bound (`{-2}n`, §8): use `ltn_ind` / `ubnP`.
- After `//=` the step goal still shows `n.+1 + m` (`addn` is
  `simpl never`): rewrite with `addSn` / `addnS` / `mulSn` (§49.4).

---

## 16. Prove a negation / contrapose

With a hypothesis to contrapose against, `apply:` the `contra*` lemma
whose shape matches (MCB §2.3.3, §4.2.1) instead of `apply/negP => h`
plus a manual contradiction. The lookup table below is library
material, not from the book. Negation-goal skeletons and the worked
`m < p` example: templates.md §23.

| intent | idiom | ref |
|---|---|---|
| goal `m < p`, have `H : b` | `rewrite ltnNge; apply: contraTN H => le_pm` | tmpl §23 |
| goal `b -> c`, prove `~~ c -> ~~ b` | `apply: contraTT => nc` | tmpl §23 |
| goal `x1 != x2` from `H : f x1 != f x2` | `apply: contra_neq H => ->` | tmpl §23 |
| goal `~ Q` from `H : ~ P` | `apply: contra_not H => hq` | tmpl §23 |

Lookup table (letter-coded names first; in parentheses the older
Corelib lemma each one is defined as):

| statement | lemma |
|---|---|
| `(c -> b) -> ~~ b -> ~~ c` | `contraNN` (`contra`) |
| `(c -> ~~ b) -> b -> ~~ c` | `contraTN` (`contraL`) |
| `(~~ c -> b) -> ~~ b -> c` | `contraNT` (`contraR`) |
| `(~~ c -> ~~ b) -> b -> c` | `contraTT` (`contraLR`) |
| `(~~ b -> false) -> b` | `contraT` |
| `(c -> ~~ b) -> b -> c = false` | `contraTF` |
| `(c -> b) -> ~~ b -> c = false` | `contraNF` |
| `(c -> b) -> b = false -> ~~ c` | `contraFN` |
| `(c -> b) -> b = false -> c = false` | `contraFF` |
| `(~~ c -> b) -> b = false -> c` | `contraFT` |
| `(Q -> P) -> ~ P -> ~ Q` | `contra_not` |
| `(Q -> ~ P) -> P -> ~ Q` | `contraPnot` |
| `(P -> ~~ b) -> b -> ~ P` | `contraTnot` |
| `(P -> b) -> ~~ b -> ~ P` | `contraNnot` |
| `(~~ b -> ~ P) -> P -> b` | `contraPT` |
| `(~~ b -> P) -> ~ P -> b` | `contra_notT` |
| `(b -> P) -> ~ P -> ~~ b` | `contra_notN` |
| `(b -> ~ P) -> P -> ~~ b` | `contraPN` |
| `(x1 = x2 -> z1 = z2) -> z1 != z2 -> x1 != x2` | `contra_neq` |
| `(x = y -> b) -> ~~ b -> x != y` | `contraNneq` |
| `(x = y -> ~~ b) -> b -> x != y` | `contraTneq` |
| `(x != y -> ~~ b) -> b -> x = y` | `contraTeq` |
| `(x != y -> b) -> ~~ b -> x = y` | `contraNeq` |
| `(x = y -> P) -> ~ P -> x != y` | `contra_not_neq` |

- Letter key: first letter = the **given hypothesis**, second = the
  **goal**; `T` = `b`, `N` = `~~ b`, `F` = `b = false`, `P` = `P`,
  `not` = `~ P`, `eq` / `neq` = `x = y` / `x != y`. The older names
  (`contra`, `contraL`, `contraR`, `contraLR`), `contra_not` and
  `contra_neq` break the key: look names up, do not derive them.
- Location: the `bool` and `Prop` forms are in Corelib `ssr/ssrbool.v`
  (`contraNN`/`TN`/`NT`/`TT` are `Definition`s aliasing `contra`,
  `contraL`, `contraR`, `contraLR`). The `eq`/`neq` forms are in
  `mathcomp/boot/eqtype.v`: `contraNneq` (l. 222), `contra_neq`
  (l. 258).
- Search: `Search "contra".`, or `Search "contra" inside eqtype.` for
  the equality forms.

```coq
From mathcomp Require Import all_boot.

Lemma c3 m n : m * n != 0 -> m != 0.
Proof. by apply: contraNN => /eqP ->; rewrite mul0n. Qed.
```

---

## 17. Reason about membership in a seq

(MCB §6.6.) Lemma statements, the `pT of mem` pitfall and examples:
§49.6.

| intent | idiom | ref |
|---|---|---|
| unfold membership in a cons | `rewrite in_cons` / `!inE`, then `=> /orP[/eqP->\|]` | §49.6 |
| membership in `++` / filter / rev / undup | `mem_cat`, `mem_filter`, `mem_rev`, `mem_undup` | §49.6 |
| membership in `map f s`, `f` injective | `rewrite (mem_map f_inj)` | §49.6 |
| state "same elements" | `s1 =i s2` (`perm_eq` counts multiplicities) | §49.6 |
| `=i` from `perm_eq` | `perm_mem` | §49.6 |
| no duplicates | `uniq s`; `undup_uniq`, `cons_uniq` | §49.6 |
| case-split on membership | `have [xs\|xNs] := boolP (x \in s)` | §49.6, §28.1 |
| count occurrences | `count_mem x s`; `count_uniq_mem` | §49.6 |

---

## 18. Quick cross-reference map

| intent group | this file | `templates.md` sibling |
|---|---|---|
| intro + transform | §1, §2 | — |
| view on goal / term | §2b | §22 (prove a view) |
| boolean / order / eq splits | §3, §4, §5 | §14 (finite split) |
| conjunction / ∃ / ∨ / set split | §6 | §8, §9 (extensionality) |
| forward `have` / `wlog` | §7, §10 | — |
| under-binder rewrite | §8 | §5, §6, §7 (eq.) |
| `near` / filter | §9 | §1, §1b |
| classical | §11 | §15 (`decidable P`) |
| closing / ring | §12, §13 | §12 (ring identity) |
| induction | §15 | §21 (induction) |
| negation / contraposition | §16 | §23 (negation) |
| seq membership | §17 | — |
