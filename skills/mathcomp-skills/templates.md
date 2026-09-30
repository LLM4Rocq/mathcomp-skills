# Proof Templates by Goal Shape

> A catalog of canonical proof skeletons keyed by the **shape of the goal**, not
> the library it comes from. This is a companion to `reference.md` (style and
> conventions) and `domains/*.md` (library-specific idioms). When you don't know
> how to start, look up the goal's shape here.

## How to use this file

1. Squint at the goal until you can match its shape to one of the templates
   below (the headings are written in Rocq notation, with `_` for irrelevant
   sub-terms).
2. Read the **Strategy** to confirm it's the right template.
3. Copy the **Skeleton** and fill in the holes with your actual reasoning.
4. Follow the **Example** citation to a real, accepted proof of the same shape.
5. Consult the cross-references for the surrounding style/library section.

Templates are intentionally short. They are **not** a substitute for thinking,
they are a starting harness so you don't waste time on the boilerplate.

---

## Table of Contents

1. `\forall x \near F, P x` — filter / topology goals (and 1b. NBHS / exists)
2. `f x @[x --> F] --> l` (and `_ --> _`) — convergence / limit goals
3. `measurable_fun D f` — measurability of a composite function
4. `is_derive x v (f x) (f' x)` — instance-driven differentiation
5. `\int[mu]_x f x = \int[mu]_x g x` — integral equality
6. `\sum_(i <- r | P i) F i = X` — bigop with explicit target
7. `\big[op/idx]_(...) F i = \big[op/idx]_(...) G i` — bigop-to-bigop equality
8. `f = g :> {ffun T -> R}` — finite-function extensionality
9. `A = B :> set T` — set extensionality
10. `A = B :> 'M[R]_(m,n)` — matrix extensionality
11. `HB.instance Definition _ := …` — structure assembly
12. `p = q :> R` for a polynomial-like ring identity — `ring` / `field` / hand
13. `(x + y) ^+ n = …` — binomial expansion
14. `P x` for `x : 'I_n` — finite case-splitting
15. `decidable P` / `P \/ ~ P` — classical choice
16. `injective f` / `cancel f g` — pointwise inversion
17. `f \is a Y` (HB predicate) — `apply/Y_P; …`
18. `closed A` / `open A` / `compact A` — topology predicates
19. `p = q :> qbsHomType _ _ _` — QBS morphism equality
20. `funext` / `f =1 g` — pointwise function equality
21. `P n` / `P s` — induction (plain, generalized, strong, bounded, from the
    right)
22. `reflect P b` / `Equality.axiom` / boolean equality — prove a view
23. `~~ b` / `x != y` / `~ P` — negation and contraposition

A goal-shape → reference section cross-index is at the end.

---

## 1. `\forall x \near F, P x` — filter / topology

**Goal shape**
```coq
\forall x \near F, P x
(* often written as: F [set x | P x] *)
```

**Strategy.** Open the filter with `near=> x`, prove `P x` under whatever
properties of `F` are available, and close any side conditions about the
witness with `near: x; …`. End the proof with the conventional
`Unshelve. all: by end_near. Qed.` to discharge shelved filter goals.
The dual form `near do <tactic>` runs a tactic under the filter.

**Skeleton.**
```coq
Lemma my_near_lemma ... : \forall x \near F, P x.
Proof.
near=> x.
(* Goal: P x, with x : T near F *)
(* prove P x; if you need facts of the form "x is close to ..." use `near: x` *)
have hx : Q x by near: x; exact: <near_lemma_for_F>.
by rewrite ...; apply: ...; exact: hx.
Unshelve. all: by end_near. Qed.
```

**Example.** `gauss_integral.v:340` —
```coq
suff: pi / 4 - integral01_u x @[x --> +oo] --> pi / 4.
  apply: cvg_trans; apply: near_eq_cvg.
  by near=> x; rewrite Ig2.
```
and the closing `Unshelve. end_near.` at line 348.

### 1b. Specialization: `A \in nbhs x` (witness an ε)

When the filter `F` is concretely `nbhs x` over a `pseudoMetricType`
or `pseudoMetricNormedZmodType`, the canonical chord is **not**
`near=>` — it is to **exhibit a ball / norm witness** via the
reflection views `nbhs_ballP` / `nbhs_normP`. This is the
"NBHS / exists" pattern the expert flagged.

**Goal shape**
```coq
A \in nbhs x           (* equivalently:  nbhs x A *)
\forall y \near x, P y (* when the filter is specifically `nbhs x` *)
```

**Strategy.** Convert the membership / near-quantifier into the
underlying existence of a ball (or norm-bounded ε) by applying
`nbhs_ballP` or `nbhs_normP`. The remaining goal is
`exists eps : posreal, ball x eps `\subset` A` (or
`exists eps : R, 0 < eps /\ ...`). Pick the ε explicitly, discharge
positivity by `posreal_lt0` / `lt0r` / hypothesis, and prove the
inclusion pointwise.

**Skeleton (ball version, pseudoMetricType).**
```coq
Lemma my_nbhs ... : A \in nbhs x.
Proof.
apply/nbhs_ballP.
exists eps_witness; first by [].          (* positivity of eps *)
move=> y y_in_ball.                       (* y : T, ball x eps y *)
(* prove y \in A using y_in_ball *)
by ...
Qed.
```

**Skeleton (norm version, pseudoMetricNormedZmodType).**
```coq
Lemma my_nbhs_norm ... : \forall y \near x, P y.
Proof.
apply/nbhs_normP.
exists eps_witness => // y y_close.       (* y_close : `|y - x| < eps *)
(* prove P y using y_close *)
by ...
Qed.
```

The `=> //` after the exists discharges the trivial `0 < eps` side
goal when `eps_witness` is built from a `posreal` (e.g. `1%:pos`,
`(eps / 2)%:pos`, or `posnumP[eps_pos]`-introduced).

**Choosing the witness.**

- For a goal that is uniform in `x` (e.g. continuity of `f`):
  pull ε out of the hypothesis (`cts_at_x` typically gives you
  `forall e > 0, exists d > 0, ...` — invert to extract `d`).
- For a goal proved by composition of two near-statements
  (Hypotheses `\near x, P y` and `\near x, Q y` ⇒ `\near x, P /\ Q`):
  use `near_andP` or apply `filterS2` rather than producing the
  ε by hand.
- For a goal where you have `nbhs_ballP`-shaped hypothesis as
  input: destruct with `move=> /nbhs_ballP[_ /posnumP[eps] subP]`
  — `subP : ball x eps `\subset` A` is then ready to use.

**Hypothesis side (the dual).**
```coq
move=> /nbhs_ballP[_ /posnumP[eps] subP].
(* eps : {posnum R}, subP : forall y, ball x eps y -> y \in A *)
```

**Example (witness side).** `mathcomp-analysis/normedtype.v` and
`standard_borel.v:585-588` follow this shape; canonical
`apply/nbhs_normP; exists eps_witness => // y ye` patterns recur
throughout `mathcomp-analysis/topology_theory/`.

**Example (hypothesis side).** `mathcomp-analysis/normedtype.v`
lemma `cvg_dist`-style proofs destruct `/nbhs_ballP` to extract
the existential ε up front, then unfold.

**Cross-references.** `domains/44_topology.md` §44.8 (the
`nbhs_ballP` / `nbhs_normP` view machinery),
`domains/44_topology.md` §44.5 (when to prefer `near=>` over
`exists ε`), `reference.md` §30.3 (`posnumP` introduction),
`reference.md` §36 (the weakest-structure rule —
`pseudoMetricType` for `ball`, `pseudoMetricNormedZmodType` for
the norm form).

**Cross-references (when to use §1 vs §1b).**

- Use **§1 (`near=>` skeleton)** when the filter `F` is abstract,
  passed as a hypothesis, or the goal is *not* directly an
  ε-quantification (e.g. it follows from another near-statement
  via `near_andP`, `near_eq_cvg`, etc.).
- Use **§1b (`nbhs_ballP` / `nbhs_normP` witness)** when the
  filter is concretely `nbhs x` and you need to *construct* the
  proof by exhibiting an ε. The two views are equivalent (via
  `nearE`) but the witness shape is the one reviewers expect when
  the proof's content is "pick this ε".

**Cross-references.** `reference.md` §26 (closing tactics), `domains/44_topology.md`
(filters, `near`), `domains/43_measure.md` (measure-theoretic ae-style goals).

---

## 2. `f x @[x --> F] --> l` — convergence / limits

**Goal shape**
```coq
f n @[n --> \oo] --> l
F --> G
cvg F            (* "F converges" *)
limn (fun n => u_n) = l
```

**Strategy.** **Never** unfold to an epsilon-delta statement.
Pick the right combinator from the `cvg_*` / `cvgr*` family and apply it.
For sums, products, sequences, use `cvgD`, `cvgM`, `cvgZ`, `cvgN`, `cvg_cst`,
`squeeze_cvgr`, `cvg_shiftS`, `near_eq_cvg`. For `limn _ = l` invoke
`cvg_lim` after proving the underlying convergence. Use `under eq_cvg do …`
to rewrite the function under the limit.

**Skeleton.**
```coq
(* Goal: f n @[n --> \oo] --> l *)
apply: <cvg_combinator>.       (* cvgD / cvgM / squeeze_cvgr / ... *)
- exact: cvg_<subcomponent>.
- exact: cvg_<subcomponent>.

(* Goal: limn u = l *)
apply: cvg_lim => //.          (* hausdorff side condition closed by // *)
exact: <the_cvg_proof>.

(* When you need to massage the function under the limit *)
under eq_cvg => n do rewrite <equation>.
```

**Example.** `theories/standard_borel.v:434-439` —
```coq
suff : (fun n => x - rem n * 2%:R^-1 ^+ n : R^o) n
         @[n --> \oo] --> (x : R^o).
  by move=> h; under eq_cvg do rewrite heq; exact: h.
have : (fun n : nat => (x : R^o)) n @[n --> \oo] --> x.
  exact: cvg_cst.
move=> hcstx; have := cvgB hcstx hrem_cvg; rewrite subr0; exact.
```
and `cvg_lim` at `standard_borel.v:637`.

**Cross-references.** `reference.md` §19 (analysis conventions),
`domains/44_topology.md` (filters and `cvg_*` combinators).

---

## 3. `measurable_fun D f` — measurability of a composite function

**Goal shape**
```coq
measurable_fun D f          (* often D = setT *)
measurable_fun setT (fun x => g (h x))
measurable_fun setT (f \+ g)
```

**Strategy.** Decompose `f` into its arithmetic / compositional pieces and
apply the matching combinator: `measurable_funD`, `measurable_funM`,
`measurable_funB`, `measurable_funN`, `measurable_funX`, `measurable_cst`,
`measurable_id`. For a composition `g \o h` use `measurableT_comp` (the
`setT` variant; for general domains use `measurable_comp` with a side
condition). Convert `\bar R` to `R` via `apply/measurable_EFinP`.

**Skeleton.**
```coq
Lemma meas_my_f : measurable_fun setT my_f.
Proof.
rewrite /my_f.
apply: measurable_funD.       (* or measurable_funM / measurable_funB ... *)
- apply: measurable_funM.
    apply: continuous_measurable_fun; exact: continuous_<...>.
  exact: measurable_cst.
exact: measurable_cst.
Qed.

(* For a composition g \o h with g pre-existing measurable_fun setT g: *)
apply: measurableT_comp => //; exact: measurable_<h>.

(* To strip \bar R: *)
apply/measurable_EFinP.
```

**Example.** `theories/standard_borel.v:155-163` —
```coq
Lemma measurable_phi : measurable_fun setT phi.
Proof.
rewrite /phi.
apply: measurable_funD.
  apply: measurable_funM.
    apply: continuous_measurable_fun; exact: continuous_atan.
  exact: measurable_cst.
exact: measurable_cst.
Qed.
```
See also `analysis/measurable_realfun.v:858, 872-875` for chained
`measurableT_comp` use.

**Cross-references.** `reference.md` §19 (analysis conventions),
`domains/43_measure.md` (measurability combinators).

---

## 4. `is_derive x v (f x) (f' x)` — instance-driven differentiation

**Goal shape**
```coq
is_derive x v f f'
is_derive x 1 (fun y => (y - a) ^+ 2) (2 * (x - a))
```

**Strategy.** This is a **typeclass goal**: build the witness with the
`is_derive_*` instance lattice (`is_derive_id`, `is_derive_cst`, `is_deriveD`,
`is_deriveB`, `is_deriveM`, `is_deriveX`, `is_deriveZ`). Avoid hand-proving
the limit; let unification pick instances. When the *value* is not in the
canonical form expected by the instance, use `apply: is_derive_eq` and finish
with `ring` / `field` / a small rewrite.

**Skeleton.**
```coq
(* Goal: is_derive x 1 (fun y => some_expr y) some_derivative *)
apply: is_derive_eq.          (* lets you rewrite the derivative term *)
rewrite <equations>.
by ring.

(* Or, when the expression matches an instance directly: *)
exact: (is_deriveX 2 (is_derive_id x 1)).

(* Composition of instances inline: *)
rewrite (@derive_val _ _ _ _ _ _ _
  (is_deriveX 2 (is_derive_id x 1))) /=.
```

**Example.** `theories/measure_as_qbs_measure.v:233-235` —
```coq
rewrite (@derive_val _ _ _ _ _ _ _
  (is_deriveX 2 (is_derive_id x 1))) /=.
```
And `analysis/derive.v:1349`:
```coq
rewrite exprS; apply: is_derive_eq.
rewrite scalerA -scalerDl mulrCA -[f x * _]exprS.
by rewrite [in LHS]mulr_natl exprfctE -mulrSr mulr_natl.
```

**Cross-references.** `domains/42_derive.md` (derivative idioms),
`reference.md` §15 (HB instance patterns — instances are the same machinery).

---

## 5. `\int[mu]_x f x = \int[mu]_x g x` — integral equality

**Goal shape**
```coq
\int[mu]_x f x = \int[mu]_x g x
\int[mu]_(x in A) f x = \int[mu]_(x in A) g x
```

**Strategy.** Reduce the equality of integrals to an equality of integrands
with `apply: eq_integral`. The remaining goal is `f x = g x` for every `x`
(possibly modulo a measurability hypothesis or restricted to `A`).
For more delicate equalities use `integral_cst`, `integralD`, `integralM`,
or `integral_indic`.

**Skeleton.**
```coq
apply: eq_integral => x _.
(* Goal: f x = g x (the trailing `_` discharges the `D x` membership) *)
by rewrite <equations>.

(* For a substitution where the integrand is replaced by a limit / sup: *)
apply: eq_integral => x _; apply/cvg_lim => //; exact: <cvg_proof>.
```

**Example.** `analysis/kernel.v:686, 694, 1359` —
```coq
- by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
- by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
apply: eq_integral => y _/=; rewrite setDE indicI indicC/=.
```

**Cross-references.** `domains/43_measure.md` (integral lemmas),
`reference.md` §27 (book-keeping under integrals).

---

## 6. `\sum_(i <- r | P i) F i = X` — bigop with explicit target

**Goal shape**
```coq
\sum_(i <- r | P i) F i = some_closed_form
\big[op/idx]_(i <- r) F i = X
```

**Strategy.** Identify which transformation produces a `bigop` of the target
shape and apply the matching member of the bigop family:

| If the RHS is …                                        | Use                                    |
|--------------------------------------------------------|----------------------------------------|
| another bigop with the same range, different body      | `apply: eq_bigr => i _`                |
| another bigop with a different range and a bijection   | `rewrite (reindex h)`                  |
| same range minus one element, plus that element        | `rewrite (bigD1 i)`                    |
| an op applied to a bigop (homomorphism)                | `rewrite (big_morph h opM hid)`        |
| a constant `idx`                                       | `rewrite big_pred0` / `big_seq1`       |
| a bigop split by a condition                           | `rewrite bigID`                        |
| factor out the first / last element                    | `rewrite big_ord_recl` / `big_ord_recr`|

**Skeleton.**
```coq
(* Pointwise rewrite under the bigop *)
apply: eq_bigr => i _.
by rewrite <equations>.

(* Extract a singled-out element *)
rewrite (bigD1 i0) //=.   (* leaves: F i0 + \sum_(i | i != i0) F i *)
rewrite <continue>.

(* Reindex by a bijection *)
rewrite (reindex h)//=.
  by apply: eq_bigr => i _; rewrite <equations>.
exists h^-1 => i _; <prove inverse>.
```

**Example.** `theories/standard_borel.v:485` —
```coq
rewrite /bin_partial_sum; apply: eq_bigr => i _.
by rewrite (heq i).
```
And `standard_borel.v:593-595`:
```coq
rewrite (bigD1 (Ordinal hmn)) //=
  [X in _ <= X - _](bigD1 (Ordinal hmn)) //=.
rewrite hdn /= mul0r add0r.
```
And `algebra/mxpoly.v:525`:
```coq
rewrite (big_morph _ (fun p q => hornerM p q a) (hornerC 1 a)).
```

**Cross-references.** `reference.md` §34 (bigop idioms),
`domains/46_tuple_perm_binomial.md` (bigops over ordinals and finite sets).

---

## 7. `\big[op/idx]_(...) F i = \big[op/idx]_(...) G i` — bigop equality

**Goal shape**
```coq
\big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(j <- s | Q j) G j
```

**Strategy.** Same machinery as §6, but choose the family member by **what's
different** between the two sides:

- bodies differ → `eq_bigr`
- predicates differ → `eq_bigl`
- ranges differ → `reindex` or `big_seq_cond`
- op differs (e.g. swap `+` and `\big[max/0]`) → `big_morph`

**Skeleton.**
```coq
(* Same range, different bodies *)
apply: eq_bigr => i Pi; rewrite <equation>.

(* Same range, predicate equivalence *)
apply: eq_bigl => i; <prove P i = Q i>.

(* Both differ; use eq_big *)
apply: eq_big => [i|i Pi]; first by <prove P i = Q i>.
by rewrite <body equation>.
```

**Example.** `algebra/ssralg.v:1281` —
```coq
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -subSn ?(valP i) //.
```

**Cross-references.** `reference.md` §34 (bigop idioms).

---

## 8. `f = g :> {ffun T -> R}` — finite-function extensionality

**Goal shape**
```coq
f = g :> {ffun T -> R}
```

**Strategy.** Apply `ffunP` to reduce to a pointwise equation, normalise the
`{ffun …}` syntax on both sides with `!ffunE`, and finish with whatever the
underlying ring / type equation needs.

**Skeleton.**
```coq
apply/ffunP => x; rewrite !ffunE.
by rewrite <type-specific equations>.
```

**Example.** `mathcomp/fingroup/gproduct.v:1139, 1180` —
```coq
Proof. by move=> x; apply/ffunP => i; rewrite !ffunE mul1g. Qed.
move=> g h; apply/ffunP=> j; have [{j}<-|nij] := eqVneq i j.
```

**Cross-references.** `domains/47_finfun.md` (finfun idioms).

---

## 9. `A = B :> set T` — set extensionality

**Goal shape**
```coq
A = B :> set T
A `<=>` B            (* in classical/set syntax *)
```

**Strategy.** For a strict equality use `apply/seteqP; split => x` to get the
two inclusions; each branch reduces to `x \in A -> x \in B`. Use `rewrite !inE`
(or `mem_setE`) to normalise the membership. For `=1` / `=2` flavored
extensionality use `apply: funext`.

**Skeleton.**
```coq
apply/seteqP; split => x /=.
- (* x \in A -> x \in B *)
  by rewrite ?inE => /...; ...
- (* x \in B -> x \in A *)
  by rewrite ?inE => /...; ...

(* Or, for a function-level equality of preimages: *)
by rewrite /preimage; apply: funext => r /=; <eqns>.
```

**Example.** `theories/qbs_giry.v:156` —
```coq
by apply/seteqP; split => x /=; rewrite decode_encode.
```
And `theories/measure_as_qbs_measure.v:184-187`:
```coq
- by apply/seteqP; split => x /=; rewrite in_itv /=.
apply/seteqP; split => x /=.
```

**Cross-references.** `domains/40_finset.md` (`{set T}` flavor),
`reference.md` §27 (book-keeping). Note: for **classical sets** (`set T`,
from `mathcomp-analysis`), use `seteqP`; for **finite sets** (`{set T}`),
use `setP`.

---

## 10. `A = B :> 'M[R]_(m,n)` — matrix extensionality

**Goal shape**
```coq
A = B :> 'M[R]_(m,n)
```

**Strategy.** Reduce to a coefficient-wise equation with `matrixP`. Normalise
both sides with `!mxE`. The remaining goal is `A i j = B i j` in `R`.

**Skeleton.**
```coq
apply/matrixP => i j; rewrite !mxE.
by rewrite <ring equations>.

(* When the coefficient depends on a case-split over splitP / lift: *)
apply/matrixP=> i j; do 3?[rewrite ?mxE ?ord1 //=; case: splitP => ? ->].
```

**Example.** `mathcomp/algebra/mxpoly.v:216, 358` —
```coq
by apply/matrixP=> i' j'; rewrite !mxE.
apply/matrixP => i j; rewrite !mxE.
```
And `mathcomp/algebra/intdiv.v:889`:
```coq
apply/matrixP=> i j; apply/eqP; rewrite mulmx1 mul1mx mxE nth_nil mul0rn.
```

**Cross-references.** `domains/38_matrix.md` (matrix idioms).

---

## 11. `HB.instance Definition _ := …` — structure assembly

**Goal shape**
```coq
(* Not a tactic goal — a top-level term to construct. *)
HB.instance Definition _ := <Factory>.Build <T> <args> <proofs>.
```

**Strategy.** Three steps:

1. Identify the **factory** that fits the data you have (e.g.
   `isQBS.Build`, `isMeasure.Build`, `Measure_isProbability.Build`).
2. Prove each axiom as a separate `Let` / `Local Lemma` above the
   `HB.instance` line, so the `Build` call reads cleanly with named
   premises.
3. Feed them in order to `Build` and put it in `HB.instance Definition _ := …`.
   When upgrading a structure (probability on top of a measure) chain factories.

**Skeleton.**
```coq
Section my_instance.
Variables (R : realType) (T : measurableType d).
Variable mu : set T -> \bar R.

Let mu0 : mu set0 = 0%E.            Proof. ... Qed.
Let mu_ge0 : forall A, (0 <= mu A)%E.   Proof. ... Qed.
Let mu_sigma_additive : semi_sigma_additive mu.   Proof. ... Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  mu mu0 mu_ge0 mu_sigma_additive.

(* Upgrade to probability: *)
Let mu_setT : mu setT = 1%:E.        Proof. ... Qed.
HB.instance Definition _ := Measure_isProbability.Build _ _ _ mu mu_setT.

End my_instance.
```

**Example.** `theories/qbs_giry.v:77-87` —
```coq
HB.instance Definition _ := isMeasure.Build _ _ _
  qbs_to_giry_mu qbs_to_giry_mu0 qbs_to_giry_mu_ge0
  qbs_to_giry_mu_semi_sigma_additive.

(* ... then later ... *)

HB.instance Definition _ := Measure_isProbability.Build _ _ _
  qbs_to_giry_mu qbs_to_giry_mu_setT.
```
And `theories/coproduct_qbs.v:210`:
```coq
HB.instance Definition _ := @isQBS.Build R (X + Y)%type Mx ax1 ax2 ax3.
```

**Skeleton — fresh enumerated type (no factory, no axioms).** Encode the type
into a known `finType` (usually `'I_n`, built with `inord`) and write a
(partial) inverse. Prove `pcancel` (or `cancel` and use `can_type`; MCB
§8.5, whose `windrose` example is adapted below), then copy the most
derived structure in **one** line. That line also registers
Equality/Choice/Countable.
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

Lemma card_windrose : #|windrose| = 4.
Proof.
rewrite -[RHS]card_ord; apply: (bij_eq_card (f := w2o)).
exists (fun o => odflt N (o2w o)) => [w|o]; first by rewrite w2oK.
by apply: val_inj; case: o => -[|[|[|[|m]]]] //= _; rewrite inordK.
Qed.
```
- Get `#|T|` from `bij_eq_card` + `card_ord`. Never unfold `enum`.
- Do not chain `Equality.copy`, `Choice.copy`, … before `Finite.copy`.
  The `redundant-canonical-projection` warnings from the single copy line
  are harmless. Full rules: `reference.md` §36.12.
- `CanIsFinite`/`PCanIsFinite` on a fresh type: ill-typed (they need an
  existing `countType`). On a type that is already a `countType`, only the
  ascribed form works (finmap/finmap.v:2275, algebra/qpoly.v:130):

  | WRONG | RIGHT |
  |---|---|
  | `HB.instance Definition _ := CanIsFinite fK.` | `HB.instance Definition _ : isFinite T := CanIsFinite fK.` |

  The WRONG line warns `non forgetful inheritance detected` +
  `HB: no new instance is generated`, and `T` stays non-`finType`.
  Default for a fresh type remains `Finite.copy T (can_type fK)`.

**Skeleton — sub-type (value + bool invariant).** Declare the record
`: predArgType` so that `#|S|` typechecks. Give `[isSub for proj]` first,
then transfer **one** top structure `by <:` (MCB §7.2).
```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Record evn : predArgType := Evn { evv :> nat; _ : ~~ odd evv }.
HB.instance Definition _ := [isSub for evv].
HB.instance Definition _ := [Countable of evn by <:].

Record b3 : predArgType := B3 { b3v : 'I_3; _ : b3v != ord0 }.
HB.instance Definition _ := [isSub for b3v].
HB.instance Definition _ := [Finite of b3 by <:].
Check #|b3|.
```
The `projection-no-head-constant` warning on `isSub.Sub_rect` is benign.
Never hand-prove `Equality.axiom` for a sub-type. `[isNew for …]` and
`[isSub of S for …]` are covered in `reference.md` §36.13.

**Cross-references.** `reference.md` §15 (HB instance patterns; its
"Instance hygiene" names the carrier and every axiom), `reference.md` §35 (HB factories and multi-step inheritance),
`reference.md` §36.12 (copy along a (p)cancel), `reference.md` §36.13
(sub-types).

---

## 12. `p = q :> R` for a ring / field identity

**Goal shape**
```coq
(x + y) * (x - y) = x ^+ 2 - y ^+ 2 :> R
pi * (y - 1/2) / pi + 1/2 = y :> R
```

**Strategy.** In order of preference:

1. **`ring`** — if `R` is a `comPzRingType` (the deprecated `comRingType`
   still parses, as `comNzRingType`; `reference.md` §36.2) and the identity
   is purely commutative-ring (no inverses, no `^-1`).
2. **`field`** — if there are inverses; the tactic generates side conditions
   `_ != 0` which you discharge afterwards (`by field; exact: hS.` or
   similar).
3. **Hand rewrites** — if the identity is conditional or mixed with non-ring
   operations (norms, integrals). Use `mulrDl`, `mulrDr`, `mulrBl`,
   `mulrBr`, `mulrA`, `mulrC`, `mulrCA`, `addrA`, `addrC`, `addrCA`,
   `addrK`, `subrK`, `opprB`, `opprD`. Use bracketed-rewrites
   `rewrite [X in _ + X]…` to point at a sub-term.

**Skeleton.**
```coq
(* Easy case — pure ring identity *)
by ring.

(* With divisions and side conditions *)
by field; rewrite ?<nonzero hyps> //.

(* Hand-driven *)
rewrite mulrDl mulrBr [in RHS]mulrC addrA.
by congr (_ + _); rewrite <subgoal>.
```

**Example.** `theories/normal_algebra.v:104, 110` —
```coq
by field; exact: hS.
field.
```
And `theories/standard_borel.v:600-604`:
```coq
have -> : (2%:R^-1 ^+ n.+1 +
  \sum_(i < m | i != Ordinal hmn) (2%:R^-1 : R) ^+ i.+1) -
  2%:R^-1 ^+ n.+1 =
  \sum_(i < m | i != Ordinal hmn) (2%:R^-1 : R) ^+ i.+1 :> R.
  by rewrite addrC addKr.
```

**Cross-references.** `domains/45_algebra_tactics.md` (`ring` / `field`
discipline), `reference.md` §29 (rewriting idioms).

---

## 13. `(x + y) ^+ n = …` and other binomial identities

**Goal shape**
```coq
(x + y) ^+ n = \sum_(i < n.+1) ...
'C(n, m) * X = Y
```

**Strategy.** The headline lemma is **`exprDn`** (resp. `exprDn_comm`,
`exprDn_pchar` in characteristic `p`). For closed-form sums use
`bin_fact`, `expr1n`. For Vandermonde / convolution-style identities use
`reindex` on the inner sum.

**Skeleton.**
```coq
(* Expand the binomial *)
rewrite exprDn.
(* Goal: \sum_(i < n.+1) x ^+ (n - i) * y ^+ i *+ 'C(n, i) = ... *)
apply: eq_bigr => i _.
by rewrite <equations>.

(* When one of x, y is 1 *)
by rewrite addrC (exprDn_comm n (commr_sym (commr1 x))).

(* Vandermonde / Chu identity: reindex over pairs *)
rewrite (reindex (fun (ij : 'I_n * 'I_n) => ij.1 + ij.2)) /=.
```

**Example.** `algebra/ssralg.v:3003` —
```coq
Proof. by rewrite exprDn !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.
```
And `algebra/ssralg.v:1287`:
```coq
rewrite addrC (exprDn_comm n (commr_sym (commr1 x))).
```

**Cross-references.** `domains/46_tuple_perm_binomial.md`,
`domains/39_polynomial.md`.

---

## 14. `P x` for `x : 'I_n` — finite case-splitting

**Goal shape**
```coq
Lemma foo (i : 'I_n.+1) : P i.
```

**Strategy.** For small `n`, `case: i => [[|...]] //` decomposes. For
arbitrary `n`, induct on the **value** of `i` via `case: i => m hm` and use
`leqVgt` / `ltnP` / `ord_inj` / `val_inj`. To enumerate use `\sum_(i : 'I_n)
…` reductions or `big_ord_recl` / `big_ord_recr`. To prove two ordinals
equal, use `apply: val_inj`.

**Rule.** If you only need the bound, use `ltn_ord i : i < n`. Do not
write `case: i => m hm` for that. Destruct only when you induct on the
value or split on small cases.

| Need | Term / lemma | Result |
|---|---|---|
| the bound | `ltn_ord i` | `i < n` |
| equal values ⇒ equal ordinals | `ord_inj` (= `val_inj`) | `injective (@nat_of_ord n)` |
| move along `e : m = n` | `cast_ord e i` (`cast_ord_id`) | `'I_n` |
| embed, `le : n <= m` | `widen_ord le i` | `'I_m` |
| skip index `h : 'I_n` | `lift h i`, `i : 'I_n.-1` | `'I_n`, value `bump h i` |
| first / last | `ord0`, `ord_max` | `'I_n.+1`, values `0` / `n` |

Full ordinal API (`val_enum_ord`, `mem_ord_enum`, `enum_rank`/`enum_val`):
`domains/46_tuple_perm_binomial.md` §46.2.
```coq
From mathcomp Require Import all_boot.

Lemma ex_ord n (i : 'I_n) : i < n.
Proof. exact: ltn_ord. Qed.

Lemma ord_eq n (i j : 'I_n) : nat_of_ord i = j -> i = j.
Proof. exact: ord_inj. Qed.

(* Verbose: case: i => m hm; by rewrite subn_gt0. *)
Lemma subn_ord_gt0 n (i : 'I_n) : 0 < n - i.
Proof. by rewrite subn_gt0 ltn_ord. Qed.
```

**Skeleton.**
```coq
case: i => m hm.
(* Goal: P (Ordinal hm), with m : nat and hm : m < n *)
(* Now do nat-level induction on m *)
elim: m hm => [|m IHm] hm.
  by rewrite ...; <base case>.
by rewrite ...; <step>.

(* Or split on small cases: *)
case: i => -[|[|i]] // hi.

(* Equality of two ordinals: *)
by apply: val_inj; rewrite /=; <prove val equality>.
```

**Example.** `mathcomp/fingroup/perm.v:282`:
```coq
apply/injectiveP=> {u} x y; rewrite !ffunE.
```
And `mathcomp/boot/seq.v:1480`:
```coq
by case: i => /= [_|i lt_i_s]; rewrite ?eqxx ?IHs ?(memPn s'x) ?mem_nth.
```

**Cross-references.** `domains/46_tuple_perm_binomial.md` §46.2 (ordinal
API), `reference.md` §34 (`big_ord_*`), `reference.md` §28 (idiomatic
case analysis).

---

## 15. `decidable P` / `P \/ ~ P` — classical choice

**Goal shape**
```coq
P \/ ~ P                      (* informative excluded middle on a Prop *)
{x | P x} + {forall x, ~ P x} (* informative existence *)
inhabited T + (T -> False)
```

**Strategy.** `mathcomp-analysis` lives in classical logic via
`mathcomp/classical/boolp.v`. The tools are:

- `pselect P : {P} + {~ P}` — informative excluded middle
- `pselectT T : T + (T -> False)` — informative inhabitation
- `cid : forall P, (exists x, P x) -> {x | P x}` — informative `cid` (Hilbert)
- `asboolP : reflect P `[<P>]` — switch between `Prop` and `bool`

The canonical pattern is `have [h|h] := pselect P` (informative) or
`have /asboolP := H` (boolean reflection).

**Skeleton.**
```coq
(* Decide a Prop *)
have [hP | hnP] := pselect P.
- (* hP : P; prove G under P *)
  ...
- (* hnP : ~ P; prove G under ~P *)
  ...

(* Decide inhabitation *)
have [Xempty | x0] := pselectT X.
- ...   (* Xempty : X -> False *)
- ...   (* x0 : X *)

(* Build a function by classical choice on each input *)
exists (fun j => match pselect (j = i0) with
                 | left heq => ...
                 | right _  => default
                 end).

(* Switch Prop <-> bool *)
have /asboolP hP := H.
```

**Example.** `theories/coproduct_qbs.v:101, 348-356`:
```coq
have [Xempty | x0] := pselectT X.
(* ... *)
exists (fun j => match pselect (j = i0) with
                 | left heq => ...
                 | right _  => ...
                 end).
case: (pselect (j = i0)) => [heq | _].
```

**Cross-references.** `reference.md` §36 (choice and decidability),
`domains/44_topology.md` (uses of `pselect` for filter constructions).

---

## 16. `injective f` / `cancel f g` — pointwise inversion

**Goal shape**
```coq
injective f
cancel f g
{in A, cancel f g}
```

**Strategy.** Reduce to the pointwise statement and apply the canonical
inversion lemma. For `injective` introduce two points and the hypothesis; for
`cancel` introduce one. `apply: val_inj` is the canonical injectivity proof
for subtype values. `apply/injectiveP` switches to a boolean form.

**Skeleton.**
```coq
(* injective f *)
move=> x y /eqP; rewrite <equation> => /eqP <-.
by ...

(* cancel f g *)
move=> x; rewrite /f /g <equations>.
by rewrite <inverse-fact>.

(* {in A, cancel f g} *)
move=> y hy; rewrite /f /g.
have /andP[hy0 hy1] : <unfold hy>.
by ...

(* Reflect to bool if you need to plug into a decidable interface *)
apply/injectiveP => x y; rewrite !<equations> => /<inv-lemma>; apply: val_inj.
```

**Equality of sub-type values.** Goal `u = v :> S` or `MkS x p1 = MkS x p2`,
with `S` a sub-type that has an `isSub` instance.
1. `apply: val_inj => /=` first. It reduces the goal to equal values
   (MCB §7.2.1).
2. Only without an `isSub` instance (raw record):
   `by rewrite (bool_irrelevance p1 p2)` (bool invariant) or
   `eq_irrelevance` (proofs of `x = y` in an `eqType`; MCB §7.2,
   §7.2.2).
3. Never `proof_irrelevance`/`Prop_irrelevance`: they add an axiom that
   shows in `Print Assumptions`. Never `congr MkS` either: it fails when the
   values differ only up to rewriting, and otherwise it just leaves `p1 = p2`.
4. Invariant stated as a `Prop`? Redesign it as a `bool` predicate
   (`reference.md` §36.13).
```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.

Record evn : predArgType := Evn { evv :> nat; _ : ~~ odd evv }.
HB.instance Definition _ := [isSub for evv].

(* Default: compare the values. *)
Lemma evn_ext' (x : nat) (p1 p2 : ~~ odd x) : Evn x p1 = Evn x p2.
Proof. exact: val_inj. Qed.

(* Values equal only up to rewriting: congr fails, val_inj works. *)
Lemma evn_addn0 x (p1 : ~~ odd (x + 0)) (p2 : ~~ odd x) :
  Evn (x + 0) p1 = Evn x p2.
Proof. Fail congr Evn. by apply: val_inj => /=; rewrite addn0. Qed.
```

**Example.** `theories/standard_borel.v:131-136` —
```coq
Lemma psiK : cancel phi psi.
Proof.
rewrite /cancel => x; rewrite /psi /phi.
rewrite addrK mulrCA divff ?mulr1; first exact: atanK.
exact: lt0r_neq0 (pi_gt0 R).
Qed.
```
And `theories/standard_borel.v:138-152`:
```coq
Lemma phiK : {in `](0:R), 1[, cancel psi phi}.
Proof.
move=> y hy; rewrite /phi /psi.
have hpi : (0 : R) < pi := pi_gt0 R.
...
```
And `mathcomp/fingroup/perm.v:277, 282`:
```coq
- by apply/injectiveP=> u v; rewrite !ffunE => /perm_inj; apply: val_inj.
apply/injectiveP=> {u} x y; rewrite !ffunE.
```

**Cross-references.** `reference.md` §27 (book-keeping), `domains/47_finfun.md`
(injectivity proofs over `{ffun T -> R}`), `reference.md` §36.13 (sub-types).

---

## 17. `f \is a Y` (HB predicate) — `apply/Y_P; …`

**Goal shape**
```coq
p \is a polyOver S
M \is a unitmx
x \is a Num.real
```

**Strategy.** Each predicate of the form `_ \is a Y` is backed by a reflection
lemma `YP : reflect (Y-property) (_ \is a Y)`. Apply `apply/YP` (or
`apply/Y_partialP` for a partial reflection) to expose the underlying
property, then prove it pointwise. For closure proofs use the dedicated
combinators (e.g. `polyOverD`, `polyOverZ`, `polyOverM`).

**Skeleton.**
```coq
(* Expose the underlying property *)
apply/<Y>P => <intros>.
by <prove underlying property>.

(* Or use closure under a constructor *)
exact: <Y>D.    (* sum closed *)
exact: <Y>M.    (* product closed *)
exact: <Y>Z.    (* scalar closed *)
exact: <Y>0.    (* 0 is in *)

(* Combine *)
apply: <Y>D; first exact: ...; exact: ...
```

**Example.** `mathcomp/algebra/poly.v:1078, 1157, 989` —
```coq
Lemma polyOver0 S : 0 \is a polyOver S.
Lemma polyOver_deriv :
  {in polyOver ringS, forall p, p^`() \is a polyOver ringS}.
Lemma polyOver_derivn :
  {in polyOver ringS, forall p n, p^`(n) \is a polyOver ringS}.
```

**Cross-references.** `domains/39_polynomial.md` (`polyOver` closures),
`reference.md` §15 (HB predicates as instances).

---

## 18. `closed A` / `open A` / `compact A` — topology predicates

**Goal shape**
```coq
closed A
open A
compact A
```

**Strategy.** Build the predicate from constructor lemmas:

- `closed`: `closedT`, `closed0`, `closedI`, `closedU`, `closed_bigcap`,
  `closed_le`, `closed_ge`, `closed_eq`, `closed_closure`.
- `open`: `openT`, `open0`, `openI`, `openU`, `open_bigcup`, `open_lt`,
  `open_gt`, `open_neq`, `open_comp`, `open_subspace`.
- `compact`: `compactT` (in compact spaces), `compact_closed`,
  `continuous_compact`, `compactU`, `compact_set1`, `compact_bigcup`.

For convergence-into-closed goals use `closed_cvg`.

**Skeleton.**
```coq
(* "A is closed because it's an intersection of closed sets" *)
apply: closedI.
- exact: closed_<...>.
- exact: closed_<...>.

(* "A is closed because limits stay in A" *)
apply: (@closed_cvg _ _ F _ f A).
- exact: closed_<...>.
- (* the sequence eventually lies in A *)
  exists N => m hm; ...

(* "A is open because it's a preimage of an open by a continuous fun" *)
apply: open_comp => // x _; exact: continuous_<...>.

(* "A is compact because it's a continuous image of a compact" *)
exact: continuous_compact.
```

**Example.** `theories/standard_borel.v:585-588` —
```coq
apply: (@closed_cvg _ _ eventually _
  (fun m => bin_partial_sum d m : R^o) (fun y : R => y <= 1 - 2%:R^-1 ^+ n.+1)
  _ _ (bin_sum d)).
- exact: closed_le.
```
And `analysis/ftc.v:77`:
```coq
- exact: openT.
```

**Cross-references.** `domains/44_topology.md` (filter + topology predicates),
`domains/43_measure.md` (`closed`/`compact` ⇒ `measurable`).

---

## 19. `(f : qbsHomType _ _ _) = g` — QBS morphism equality

**Goal shape**
```coq
(f : qbsHomType R X Y) = g
```

**Strategy.** Morphism types in the QBS development are bundled records with
a function projection. Equality of two morphisms reduces to equality of their
function components, which in turn is `funext`. The pattern is:

```coq
apply/val_inj/funext => x. (* or apply: ... if val_inj isn't the projection *)
```

Often combined with `qbs_hom_eq` or a similar dedicated lemma in
`quasi_borel.v`. See `domains/43_measure.md` (measure-side morphisms).

**Skeleton.**
```coq
apply/qbs_hom_eqP => x.    (* or whatever the named reflection is *)
by rewrite <equations>.
```

**Example.** This template is included for completeness but the QBS code base
does not yet have a canonical `qbs_hom_eqP` lemma — the morphism equalities
that arise are usually discharged by `apply: val_inj` followed by `funext`,
which is the same pattern as §20.

**Cross-references.** `theories/quasi_borel.v` (morphism definitions),
template §20 below.

---

## 20. `funext` / `f =1 g` — pointwise function equality

**Goal shape**
```coq
f = g :> A -> B           (* function as plain Coq term *)
f =1 g                    (* pointwise *)
```

**Strategy.** For full function equality, `apply: funext => x` and prove
`f x = g x` pointwise. For `=1` use `move=> x` directly. When the equality
is between a generic function and one defined by `[fun …]` or a
match-on-classical-choice expression, you usually need `congr` or a small
case analysis on the choice.

**Skeleton.**
```coq
apply: funext => x.
by rewrite <equations>.

(* Pointwise =1 *)
move=> x; rewrite <equations>.

(* When the function on one side is defined by pselect: *)
apply: funext => x.
case: pselect => [hx | hx]; first by ...; by ...
```

**Example.** `theories/measure_qbs_adjunction.v:274` —
```coq
by apply: funext => x /=; rewrite hpsi1phi1 hpsi2phi2.
```
And `theories/measure_as_qbs_measure.v:181`:
```coq
by apply: funext => x /=; rewrite indicE mem_setE.
```
And `theories/standard_borel.v:483-484`:
```coq
move=> heq; rewrite /bin_sum; congr (limn _).
apply: funext => n.
```

**Cross-references.** `reference.md` §27 (book-keeping with `funext`),
`reference.md` §29 (rewriting idioms).

---

## 21. `P n` for `n : nat` / `P s` for `s : seq T` — induction

**Goal shape**
```coq
Lemma foo n : P n.                (* n : nat *)
Lemma bar (s : seq T) : Q s.      (* s : seq T *)
```

**Strategy.** (MCB §2.3.4, §3.7, §5.3, Part III cheat sheet; item 1's
`; first by`: MCB Introduction.)

1. **Plain.** `elim: n => [|n IHn]`: one slot per constructor, the IH is
   the last name of the step slot. Use `elim: n => // n IHn` when `done`
   closes the base case, or close it with `; first by …` (reference
   §27.9).
2. **Generalize first** every variable, hypothesis or accumulator that
   must vary in the IH: `elim: n m => [|n IHn] m`, or
   `elim: n => [|n IHn] in m *`, or `elim: s z => [|x s IHs] z`. The
   names after `:` are pushed on the goal before `elim` and the pattern
   re-introduces them (reference §27.10). Never `intros; induction n`.
   Never hand-write a motive (`apply: (nat_ind (fun n => …))`).
3. **Strong induction.** `elim/ltn_ind: n => n IHn` gives
   `IHn : forall m, m < n -> P m` (`mathcomp/boot/ssrnat.v`, `ltn_ind`
   (l. 492)). It replaces the book's `elim: n.+1 {-2}n (ltnSn n)`, which
   uses a banned numeric occurrence selector (reference §8, "Replacing
   numeric occurrence selectors").
4. **Bounded / measure induction.** The ssrnat header (l. 453-483) calls
   this idiom "preferable to the legacy idiom relying on numerical
   occurrence selection". For a measure `Mxy` over `x y`:
   - `have [n leMn] := ubnP Mxy; elim: n => // n IHn in x y leMn *.`
     gives `leMn : Mxy < n.+1` and `IHn : forall x y, Mxy < n -> …`.
   - `have [n] := ubnP Mxy; elim: n => // n IHn in x y * => /ltnSE-leMn.`
     when you need exactly `leMn : Mxy <= n`.
   - For a single nat: `have [m] := ubnP n; elim: m n => // m IHm n lt_nm`.
   - `ubnP` (l. 484), `ltnSE` (l. 485). `ubnPleq`, `ubnPgeq`, `ubnPeq`
     (l. 489-491) are for goals that mention the bound: `have [n defM] :=
     ubnPleq Mxy` replaces `Mxy` by `n` in the goal and adds
     `defM : Mxy <= n` (`>=` / `==` for the others; the book's
     `case: (ubnPgeq m)`). Elimination on `n` leaves a `0` case to
     dispatch. `ltn_ind` itself is proved this way (l. 492-496).
   - The base case goes by `//` because its hypothesis `Mxy < 0` is
     false.
5. **seq.** `elim: s => [|x s IHs]`. From the right, use
   `elim/last_ind: s => [|s x IHs]` (`mathcomp/boot/seq.v`, `last_ind`
   (l. 368)). Its step is `P s -> P (rcons s x)`: finish with `rev_rcons`
   (l. 913), `cats1` (l. 324), `size_rcons` (l. 336). The principle of
   `seq` (= `list`) is `list_ind`, never `seq_ind`. For two seqs of equal
   size, use `seq_ind2` (l. 981). Other eliminators: `elim/poly_ind` (§39,
   needs `all_algebra`), `elim/big_rec2`, `elim/big_ind2` (reference
   §34). seq lemma families: `domains/49_nat_seq.md` §49.5.
6. **Sum / product indexed by n.** Peel the last term with `big_nat_recr` /
   `big_ord_recr` or the first with `big_nat_recl` / `big_ord_recl`. The
   `big_nat_rec*` side condition `m <= n` goes by `//` inside the chain
   (reference §34.5).
7. **Step-case pitfalls.**
   - `addn`, `muln`, `subn` and `expn` are `simpl never`, so after `//=`
     the step still shows `m.+1 + 0`. Rewrite with `addSn` / `addnS` /
     `mulSn` (`domains/49_nat_seq.md` §49.4).
   - The error `The LHS of IHm (m + 0) does not match any subterm of the
     goal` is this symptom (errors.md §3).
   - Consume a single-use IH with `rewrite -{}IHn`, which also clears it
     (reference §27.11).
8. **Arithmetic tail.** Upstream prefers rewrite chains (as in `gauss`
   below). `zify; lia` is acceptable in project code (§45.5).

**Skeleton.**
```coq
elim: n => [|n IHn] in m *.       (* plain; IHn : forall m, P n m *)
  (* base case: by rewrite ... *)
(* step: by rewrite <peel> IHn <arith>. *)

elim/ltn_ind: n => n IHn.         (* strong: IHn : forall k, k < n -> P k *)
have [k] := ubnP n; elim: k n => // k IHk n lt_nk.   (* bounded *)
elim: s => [|x s IHs].            (* seq from the left: Q (x :: s) *)
elim/last_ind: s => [|s x IHs].   (* seq from the right: Q (rcons s x) *)
```

**Example.** Upstream: `ltn_ind` is proved at `mathcomp/boot/ssrnat.v:494`
by `have [n leMn] := ubnP M; elim: n => // n IHn in M leMn *.` The
from-the-right idiom appears at `mathcomp/boot/seq.v:921`
(`elim/last_ind: s => // s x IHs in n *.`) and at
`mathcomp/boot/seq.v:3252` (`foldl_rev`, the model for `foldl_rev_ex`
below). Self-contained versions follow (the `gauss` lemma is from
MCB Introduction):
```coq
From mathcomp Require Import all_boot.

Lemma gauss n : \sum_(0 <= i < n.+1) i = (n * n.+1) %/ 2.
Proof.
elim: n => [|n IHn]; first by rewrite big_nat1.
rewrite big_nat_recr //= IHn addnC -divnMDl //.
by rewrite mulnS muln1 -addnA -mulSn -mulnS.
Qed.

Lemma strong (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof. by move=> ih n; elim/ltn_ind: n => n IH; apply: ih. Qed.

Lemma even_or_odd n : exists k, n = k.*2 \/ n = k.*2.+1.
Proof.
elim/ltn_ind: n => -[|[|n]] IH; first by exists 0; left.
  by exists 0; right.
have [|k [->|->]] := IH n; first exact: leqW.
  by exists k.+1; left; rewrite doubleS.
by exists k.+1; right; rewrite doubleS.
Qed.

Lemma even_or_odd' n : exists k, n = k.*2 \/ n = k.*2.+1.
Proof.
have [m] := ubnP n; elim: m n => // m IHm [|[|n]] lt_nm.
- by exists 0; left.
- by exists 0; right.
have [|k [->|->]] := IHm n; first by rewrite ltnS in lt_nm; exact: ltnW.
  by exists k.+1; left; rewrite doubleS.
by exists k.+1; right; rewrite doubleS.
Qed.

Lemma addn0' m : m + 0 = m.
Proof. by elim: m => [|m IHm] //; rewrite addSn IHm. Qed.

Lemma double_addnn n : n.*2 = n + n.
Proof. by elim: n => // n IHn; rewrite doubleS addSn addnS -{}IHn. Qed.
```
And on `seq`, from the right:
```coq
From mathcomp Require Import all_boot.

Lemma foldl_rev_ex (T R : Type) (f : R -> T -> R) z (s : seq T) :
  foldl f z (rev s) = foldr (fun x y => f y x) z s.
Proof.
elim/last_ind: s z => [|s x IHs] z //.
by rewrite rev_rcons /= -cats1 foldr_cat -IHs.
Qed.

Lemma size_rev' (s : seq nat) : size (rev s) = size s.
Proof.
by elim/last_ind: s => [//|s x IH]; rewrite rev_rcons /= IH size_rcons.
Qed.
```

**Cross-references.** `reference.md` §27.9 (`first by`, selectors),
§27.10 (generalizing, `in H *`), §27.11 (`{}H`), §29.9 (`/=` and
`simpl never`), §34.5 (peeling), §8 (occurrence-selector translations);
`domains/49_nat_seq.md` §49.4, §49.5; `phrasebook.md` §15 (induction
rows); `errors.md` §3.

---

## 22. `reflect P b` / `Equality.axiom op` / `b1 = b2` between booleans — prove a view

(MCB §5.1.2, §6.4–§6.6, Part III, cheat sheet)

**Goal shape**
```
Lemma fooP x : reflect (<math def of foo x>) (foo x).
Lemma eqfooP : Equality.axiom eqfoo.      (* for hasDecEq.Build *)
Lemma bar : b1 = b2.                      (* b1 b2 : bool *)
```

**Strategy.**

1. `apply: (iffP idP) => [hb | hP]` when `b` is atomic. Pick the base
   view that already turns `b` into the nearest Prop:
   - `(iffP V)` with `V` = `andP`, `orP`, `eqP`, `negP`, `allP`,
     `hasP`, `eqnP`, … when `b` is a connective or an `==`;
   - `apply: (equivP V)` when a Prop iff `P <-> Q` is at hand;
   - `rewrite /foo` first when `foo` is a Definition that later `<-`
     rewrites must see through.

   The library does the same: `leP` at `mathcomp/boot/ssrnat.v:500`
   (`iffP idP`), `inj_eqAxiom` at `mathcomp/boot/eqtype.v:758`
   (`iffP eqP`).
2. The two subgoals are `b -> P` and `P -> b`. Destructure in the
   intro pattern: `[|[]->]`, `[k <-]`, `[[h1 h2] | hP]`.
3. `b1 = b2` between booleans: `apply/idP/idP` when both sides are
   atomic, otherwise `apply/V1/V2` (`apply/andP/orP`, `apply/idP/negP`:
   `b1 = ~~ b2` becomes `b1 -> ~ b2` and `~ b2 -> b1`). To switch
   views inside a rewrite chain: `rewrite (sameP V1 V2)`.
4. Structural `Equality.axiom`: double induction, close all
   mismatched constructors with `do ?[exact: ReflectT | exact: ReflectF]`,
   then `case: (x =P y) => [<-|neq]` and `apply: (iffP (IH t))`.
   `case: (x =P y)` is right **here** because the `ReflectF` branch
   needs `x <> y`. This is the exception to the `eqVneq` preference of
   reference.md §36.8. Library model: `eqseqP` at
   `mathcomp/boot/seq.v:1088`.
5. Naming and shape: suffix `P` (reference.md §11, §37.6). Keep the
   boolean as the index so both `move=> /fooP` and `apply/fooP` work.
   When a public `foo : T -> bool` has a natural Prop counterpart, ship
   `fooP`. `Arguments fooP
   {x}` is optional (reference.md §31).
6. Pitfall: do not prove `reflect` on a non-closed boolean with
   `case: b; constructor`; reviewers expect `iffP`. On closed small
   booleans it is fine:
   `Lemma myandP (a b : bool) : reflect (a /\ b) (a && b).`
   `Proof. by case: a; case: b; constructor=> // -[]. Qed.`

**Skeleton.**
```
(* reflect P b *)
apply: (iffP idP) => [hb | hP].     (* or (iffP andP) => [[h1 h2] | hP] *)
- (* b -> P *) ...
- (* P -> b *) ...

(* reflect Q b from V : reflect P b and P <-> Q *)
by apply: (equivP V); split=> ...

(* b1 = b2 *)
apply/idP/idP => [h1 | h2].          (* or apply/V1/V2 *)

(* Equality.axiom on an inductive *)
elim=> [|x s IH] [|y t] /=; do ?[exact: ReflectT | exact: ReflectF].
case: (x =P y) => [<-|neqxy]; last by apply: ReflectF => -[].
by apply: (iffP (IH t)) => [<-|[]].
```

**Example.** Views proved with `iffP idP`:
```coq
From mathcomp Require Import all_boot.

Definition le3 (n : nat) : bool := n <= 3.

Lemma le3P n : reflect (exists k, n + k = 3) (le3 n).
Proof.
rewrite /le3; apply: (iffP idP) => [le_n3 | [k <-]].
  by exists (3 - n); rewrite subnKC.
exact: leq_addr.
Qed.

Lemma mulP m n : reflect (m = 0 \/ n = 0) (m * n == 0).
Proof.
apply: (iffP idP) => [|[]->]; rewrite ?muln0 //.
by rewrite muln_eq0 => /orP[]/eqP; [left | right].
Qed.
```
Structural `Equality.axiom`, and a boolean equation:
```coq
From mathcomp Require Import all_boot.

Fixpoint eqlist (s1 s2 : seq nat) :=
  match s1, s2 with
  | [::], [::] => true
  | x :: s, y :: t => (x == y) && eqlist s t
  | _, _ => false end.

Lemma eqlistP : Equality.axiom eqlist.
Proof.
elim=> [|x s IH] [|y t] /=; do ?[exact: ReflectT | exact: ReflectF].
case: (x =P y) => [<-|neqxy]; last by apply: ReflectF => -[].
by apply: (iffP (IH t)) => [<-|[]].
Qed.

Lemma bool_eq (b1 b2 : bool) :
  (b1 -> ~ b2) -> (~ b2 -> b1) -> b1 = ~~ b2.
Proof. by move=> h1 h2; apply/idP/negP. Qed.
```

**Cross-references.** `reference.md` §28.2 (spec `Variant`s for case
analysis), §36.3 (`reflect` and the decidable-equality bridge), §36.7,
§37.6 (`reflect` over `iff`); `phrasebook.md` §6.

---

## 23. `~~ b`, `x != y`, `~ P` — negation and contraposition

(MCB §2.3.3, §4.2.1 for contraposition and the `ltnNge` / `leqNgt`
normalisation; the letter codes and the `!=` / `Prop` variants are
library material, not from the book.)

**Goal shape**
```
~~ c        b -> c   (b c : bool)        x != y        ~ P
```

**Strategy.**

1. With a hypothesis to contrapose against, apply the `contra*` lemma
   whose letter code matches the shapes (first letter = given
   hypothesis, second = goal; lookup table in `phrasebook.md` §16).
   Normalise first: `rewrite ltnNge` turns `m < p` into
   `~~ (p <= m)`; `rewrite -leqNgt` turns `~~ (m < p)` into `p <= m`.
2. `apply: contraTN H => h` (older name `contraL`), with `H : b` and
   goal `~~ c`: the goal becomes `~~ b` under `h : c`.
3. `x != y`: `apply: contra_neq H` (`H : z1 != z2`, goal becomes
   `x = y -> z1 = z2`) or `contraNneq H` (`H : ~~ b`, goal
   `x = y -> b`). Prop negation: `contra_not` / `contraPnot`.
4. No hypothesis to contrapose: `apply/negP => h` and derive a
   contradiction.
5. `False` in context, or an absurd constructor equation (`0 = n.+1`),
   closes with `by []` (`by case` on the equation warns
   `spurious-ssr-injection`; `phrasebook.md` §12).

**Skeleton.**
```
rewrite ltnNge; apply: contraTN p_dv => le_pm.   (* goal: ~~ (p %| _) *)
```

**Example.**
```coq
From mathcomp Require Import all_boot.

Lemma ex_contraTN m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
move=> pp p_dv; rewrite ltnNge; apply: contraTN p_dv => le_pm.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

Lemma ex_contra m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
move=> pp; apply: contraTT; rewrite -leqNgt => lepm.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
```
WRONG/RIGHT, plus the `!=` and Prop forms:
```coq
From mathcomp Require Import all_boot.

(* WRONG: unfold both negations by hand *)
Lemma c3_hand m n : m * n != 0 -> m != 0.
Proof.
move=> h; apply/negP => /eqP m0; move/negP: h; apply.
by rewrite m0 mul0n.
Qed.

(* RIGHT: the contra lemma whose letters match (N hyp, N goal) *)
Lemma c3 m n : m * n != 0 -> m != 0.
Proof. by apply: contraNN => /eqP ->; rewrite mul0n. Qed.

Lemma succ_neq m n : m != n -> m.+1 != n.+1.
Proof. by apply: contra_neq => -[]. Qed.

Lemma not_lt_self n : ~ (n < n).
Proof. by apply/negP; rewrite ltnn. Qed.
```

**Cross-references.** `phrasebook.md` §16 (letter-code table),
`reference.md` §36.7, §37.11 (`Search "contra"`).

---

## Cross-reference table — goal shape to reference / domain

| #  | Goal shape                                  | `reference.md`       | `domains/*.md`                  |
|----|---------------------------------------------|----------------------|---------------------------------|
| 1  | `\forall x \near F, P x`                    | §30.3                | `44_topology.md`                |
| 2  | `_ --> _`, `cvg _`, `lim _ = _`             | §19                  | `44_topology.md`                |
| 3  | `measurable_fun D f`                        | §19                  | `43_measure.md`                 |
| 4  | `is_derive x v f f'`                        | §15                  | `42_derive.md`                  |
| 5  | `\int[mu]_x f x = \int[mu]_x g x`           | §27                  | `43_measure.md`                 |
| 6  | `\sum_(i …) F i = X`                        | §34                  | `46_tuple_perm_binomial.md`     |
| 7  | `\big[op/idx]_(…) F = \big[op/idx]_(…) G`   | §34                  | `46_tuple_perm_binomial.md`     |
| 8  | `f = g :> {ffun T -> R}`                    | —                    | `47_finfun.md`                  |
| 9  | `A = B :> set T`                            | §27                  | `40_finset.md`                  |
| 10 | `A = B :> 'M[R]_(m,n)`                      | —                    | `38_matrix.md`                  |
| 11 | `HB.instance Definition _ := …`             | §15, §35, §36.12, §36.13 | (cross-cutting)             |
| 12 | `p = q :> R` (ring identity)                | §29                  | `45_algebra_tactics.md`         |
| 13 | `(x + y) ^+ n = …`                          | §34                  | `39_polynomial.md`, `46_…`      |
| 14 | `P (i : 'I_n)`                              | §28                  | `46_tuple_perm_binomial.md`     |
| 15 | `decidable P`, `P \/ ~P`                    | §36                  | `44_topology.md`                |
| 16 | `injective f`, `cancel f g`                 | §27, §36.13          | `47_finfun.md`                  |
| 17 | `f \is a Y` (HB predicate)                  | §15                  | `39_polynomial.md`              |
| 18 | `closed A`, `open A`, `compact A`           | §19                  | `44_topology.md`, `43_measure.md`|
| 19 | `f = g :> qbsHomType _ _ _`                 | §15                  | (project-specific)              |
| 20 | `f = g :> A -> B`, `f =1 g`                 | §27, §29             | (cross-cutting)                 |
| 21 | `P n`, `P s`                                | §27.10, §29.9, §8    | `49_nat_seq.md`                 |
| 22 | `reflect P b`                               | §28.2, §36.3, §37.6  | (cross-cutting)                 |
| 23 | `~~ b`, `x != y`                            | §36.7, §37.11        | `49_nat_seq.md`                 |

---

## Notes on what's **not** here

- **`apply: lim_morph_inv` and like-named one-shot lemmas** were skipped; they
  are too project-specific for a general "shape-to-skeleton" table. Look them
  up by `Search` instead.
- **Borel hierarchy `Sigma` / `Pi` levels** (`measurable A` at level `n`) — no
  truly canonical skeleton exists; the proofs are case-by-case decompositions
  via `measurable_*` combinators (§3 covers the simple cases).
- **`Vandermonde` and other named binomial identities** — left out as a
  template because the proofs require domain-specific reindexings that don't
  fit a short skeleton. See `mathcomp/algebra/poly.v` and
  `mathcomp/boot/binomial.v` for the actual lemmas.
- **QBS-specific morphism equality (§19)** is a stub: the QBS codebase does
  not yet have a settled `apply/Y_P; …` lemma for `qbsHomType`. When such a
  lemma is introduced, expand §19 with a real example.
- **nat/seq lemma families** (`subnK`, `ltnS`, `nth_map`, `mem_cat`, …)
  live in `domains/49_nat_seq.md`; §21 only gives the induction skeletons.
  The book-to-2.5 translation of instance declarations (MCB `Canonical` /
  `[eqMixin of …]` → `HB.instance`) is in `reference.md` §48.
