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
And `analysis/mxpoly.v:525`:
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

**Example.** `analysis/ssralg.v:1281` —
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

**Cross-references.** `reference.md` §15 (HB instance patterns),
`reference.md` §35 (HB factories and multi-step inheritance).

---

## 12. `p = q :> R` for a ring / field identity

**Goal shape**
```coq
(x + y) * (x - y) = x ^+ 2 - y ^+ 2 :> R
pi * (y - 1/2) / pi + 1/2 = y :> R
```

**Strategy.** In order of preference:

1. **`ring`** — if `R` is a `comRingType` and the identity is purely
   commutative-ring (no inverses, no `^-1`).
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

**Example.** `analysis/ssralg.v:3003` —
```coq
Proof. by rewrite exprDn !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.
```
And `analysis/ssralg.v:1287`:
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

**Cross-references.** `domains/46_tuple_perm_binomial.md` (ordinals and
`big_ord_*`), `reference.md` §28 (idiomatic case analysis).

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
(injectivity proofs over `{ffun T -> R}`).

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
Lemma polyOver_deriv : {in polyOver ringS, forall p, p^`() \is a polyOver ringS}.
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

## Cross-reference table — goal shape to reference / domain

| #  | Goal shape                                  | `reference.md`       | `domains/*.md`                  |
|----|---------------------------------------------|----------------------|---------------------------------|
| 1  | `\forall x \near F, P x`                    | §26                  | `44_topology.md`                |
| 2  | `_ --> _`, `cvg _`, `lim _ = _`             | §19                  | `44_topology.md`                |
| 3  | `measurable_fun D f`                        | §19                  | `43_measure.md`                 |
| 4  | `is_derive x v f f'`                        | §15                  | `42_derive.md`                  |
| 5  | `\int[mu]_x f x = \int[mu]_x g x`           | §27                  | `43_measure.md`                 |
| 6  | `\sum_(i …) F i = X`                        | §34                  | `46_tuple_perm_binomial.md`     |
| 7  | `\big[op/idx]_(…) F = \big[op/idx]_(…) G`   | §34                  | `46_tuple_perm_binomial.md`     |
| 8  | `f = g :> {ffun T -> R}`                    | —                    | `47_finfun.md`                  |
| 9  | `A = B :> set T`                            | §27                  | `40_finset.md`                  |
| 10 | `A = B :> 'M[R]_(m,n)`                      | —                    | `38_matrix.md`                  |
| 11 | `HB.instance Definition _ := …`             | §15, §35             | (cross-cutting)                 |
| 12 | `p = q :> R` (ring identity)                | §29                  | `45_algebra_tactics.md`         |
| 13 | `(x + y) ^+ n = …`                          | §34                  | `39_polynomial.md`, `46_…`      |
| 14 | `P (i : 'I_n)`                              | §28                  | `46_tuple_perm_binomial.md`     |
| 15 | `decidable P`, `P \/ ~P`                    | §36                  | `44_topology.md`                |
| 16 | `injective f`, `cancel f g`                 | §27                  | `47_finfun.md`                  |
| 17 | `f \is a Y` (HB predicate)                  | §15                  | `39_polynomial.md`              |
| 18 | `closed A`, `open A`, `compact A`           | §19                  | `44_topology.md`, `43_measure.md`|
| 19 | `f = g :> qbsHomType _ _ _`                 | §15                  | (project-specific)              |
| 20 | `f = g :> A -> B`, `f =1 g`                 | §27, §29             | (cross-cutting)                 |

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
  `mathcomp/algebra/binomial.v` for the actual lemmas.
- **QBS-specific morphism equality (§19)** is a stub: the QBS codebase does
  not yet have a settled `apply/Y_P; …` lemma for `qbsHomType`. When such a
  lemma is introduced, expand §19 with a real example.
