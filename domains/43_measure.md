## 43. Measure and Lebesgue Integral Idioms

The mathcomp-analysis measure-theory stack lives in three layered
directories under `mathcomp/analysis/`:

- `measure_theory/` — sigma-algebras, measures, the bundled
  `{mfun aT >-> rT}` family, dirac/probability measures.
- `lebesgue_integral_theory/` — the integral itself: definition,
  monotone/dominated convergence, integrability, Fubini, transfer.
- `probability_theory/` — concrete distributions (Bernoulli, beta,
  uniform, normal, ...) on top of `Probability`.

Reviewers consistently flag four families of regression on PRs that
touch this stack: (1) explicit `measurable_fun [set: T] f` instead of
`{mfun T >-> R}` bundling, (2) per-`x` rewrites under an integral
that should be `under eq_integral do ...`, (3) `[the probability M R
of mu]` ascriptions over a name that already has a canonical HB
instance, and (4) display arguments spelled out as
`default_measure_display`. This section codifies the idioms.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `measurable_funP` | prove `measurable_fun D f` from a bundled `{mfun}` | §43.3 |
| `measurableT_comp` | discharge measurability of a composition | §43.3 |
| `under eq_integral do …` | rewrite the integrand under `\int[mu]_…` | §43.6 |
| `integralD`, `integralZl`, `integral_cst` | additivity / scaling / constant integral | §43.5 |
| `integral_dirac`, `probability_setT` | dirac integral; `P setT = 1` | §43.5, §43.7 |
| `monotone_convergence`, `dominated_convergence` | limits of integrals, no epsilon-N | §43.5 |
| `setTI` | clean up `setT \`&\` A` after `measurable_fun setT` | §43.9 |

### 43.1 Type structure: from `measurableType d` to `{mfun T >-> R}`

The carrier hierarchy:

```coq
sigmaRingType d  -->  measurableType d
```

Both are parameterised by a `measure_display` `d`, an inhabited
`Inductive measure_display := default_measure_display.` whose only
purpose is canonical-structure disambiguation. Treat `d` like the
order display in §22.4 and §24.4: it is a wildcard, never a value to
be supplied.

```coq
(* WRONG -- spells out the display *)
Lemma foo (T : measurableType default_measure_display) ... .

(* RIGHT *)
Lemma foo d (T : measurableType d) ... .

(* RIGHT, when d is otherwise unused *)
Lemma foo {T : measurableType _} ... .
```

The bundled types follow the §15 / §35 pattern:

| Notation | Definition | Scope |
|----------|------------|-------|
| `measurableType d` | sigma-algebra carrier | (type) |
| `{measure set T -> \bar R}` | bundled measure | `ring_scope` |
| `{mfun aT >-> rT}` | bundled measurable function | `form_scope` |
| `[mfun of f]` | the canonical `{mfun ...}` of `f` | `form_scope` |
| `probability T R` | bundled probability measure | (type) |

There is no `{measurable_fun A >-> R}` notation — the bundled form
quantifies over `setT`. The bare predicate `measurable_fun D f`
takes an explicit domain `D` and is the lemma-side input;
`{mfun ...}` is the term-side container.

### 43.2 Integral notation

`lebesgue_integral_definition.v`:

```coq
\int[mu]_(x in D) f x   ==  integral mu D (fun x => f x)
\int[mu]_x f x          ==  \int[mu]_(x in setT) f x
```

`f` lives in `T -> \bar R` (extended reals) by default; the analogous
real-valued notation `Rintegral` reuses the same syntax in
`lebesgue_Rintegral.v`. Do **not** confuse `\int[mu]_x f x`
(Lebesgue) with `\int_(a <= x <= b) f x dx` (FTC notation in
`ftc.v` / `normedtype.v`); the former takes a *measure*, the latter
lives over an interval and uses `Rintegral` underneath.

Ereal series share the bigop machinery (§34.1, §34.2):

```coq
\sum_(n <oo) u n             == limn (fun N => \sum_(0 <= n < N) u n)
\sum_(m <= i <oo | P i) u i  == filtered ereal series
```

The lemma name `nneseries` (non-negative ereal series) tags lemmas
about `\sum_(n <oo)` whose hypothesis is `forall n, 0 <= u n`:
`is_cvg_nneseries`, `lee_nneseries`, `nneseriesD`, `nneseries_split`,
`nneseriesZl`. The notation is just `\sum_(... <oo)`; `nneseries` is
not itself a notation, only a naming prefix.

### 43.3 The `measurable_fun` predicate family

`measurable_fun D f` unfolds to `measurable D -> forall Y,
measurable Y -> measurable (D `&` f @^-1` Y)`. The lemmas users
actually invoke:

| Lemma | Use case |
|-------|----------|
| `measurable_funPT` (mixin) | Expose the `setT`-domain proof from a bundled `{mfun ...}` |
| `measurable_funP s` | Bundled `{mfun ...}` ⇒ `measurable_fun D s` for any `D` |
| `measurable_funPTI s` | Bundled ⇒ `measurable (s @^-1` Y)` |
| `measurable_id` | `measurable_fun D id` |
| `measurable_comp F` | General composition with explicit codomain |
| `measurableT_comp` | Composition when the outer fun is measurable on `setT` (the workhorse) |
| `measurable_funS E D` | Restrict from a larger domain |
| `measurable_funTS D` | Specialise from `setT` to `D` |
| `eq_measurable_fun` | `{in D, f =1 g}` transports measurability |
| `measurable_funD` | `f \+ g` |
| `measurable_funB` | `f \- g` |
| `measurable_funN` | `\- f` |
| `measurable_funM` | `f \* g` |
| `measurable_funX` | `fun x => f x ^+ n` |
| `measurable_funU` | union of domains |
| `measurable_fun_if` | bool-valued discriminator |

The `measurableT_comp` lemma is the canonical move when the outer
function is something like `EFin`, `normr`, `expR`, `+%R x`,
`Order.max c`: every such function carries a global
`Hint Extern 0 (measurable_fun _ _) => solve [...] : core` so
`exact: measurableT_comp` discharges the goal in one step.

```coq
(* WRONG -- manual, breaks under maintenance *)
move=> mD; rewrite -[f @^-1` _]setTI; apply: (measurable_funPT _ Y mY).

(* RIGHT *)
exact: measurable_funP f.    (* if f : {mfun T >-> R} *)
exact: measurable_funPT.     (* setT-domain shortcut, inside an mfun proof *)
exact: measurableT_comp.     (* outer applied to inner, both measurable *)
```

### 43.4 Bundling and unbundling: `mfun_Sub` / `set_mem`

The pattern is the same sub-type story as §32:

```coq
(* From measurable_fun setT f, build {mfun T >-> R} *)
HB.instance Definition _ := isMeasurableFun.Build _ _ T R f mfP.

(* From f \in mfun, recover the bundled f *)
mfun_Sub fP : {mfun T >-> R}        (* fP : f \in mfun *)

(* From a set-side proof, get the predicate witness *)
mem_set : f \in [set f | measurable_fun setT f]
set_mem : extracts the underlying `measurable_fun`
```

Reviewers reject `[the {mfun _ >-> _} of f]` ascription when an
HB-instance is already attached to `f`'s definition (analysis
PR #786 / §35.5). If you need a `{mfun ...}` for a fresh
function, use `HB.instance Definition _ := isMeasurableFun.Build ...`
once; thereafter the bundled form resolves canonically.

### 43.5 Integral lemma family

| Lemma | What it does |
|-------|--------------|
| `integralE D` | Decomposition `f = f^+ - f^-` |
| `integral_cst` | `\int[mu]_(x in D) cst r = r * mu D` |
| `integral_indic A` | `\int (\1_A x)%:E = mu (A `&` D)` |
| `integral_mkcond D` | Promote `D`-bounded integral to `setT` via restriction |
| `integralD` | `\int (f1 + f2) = \int f1 + \int f2` (both integrable) |
| `integralB` | `\int (f1 \- f2) = \int f1 - \int f2` |
| `integralZl` | `\int (r%:E * f) = r%:E * \int f` |
| `integralZr` | symmetric |
| `integralD_EFin`, `integralB_EFin` | Real-valued operands lifted via `EFin` |
| `integralN` | `\int (- f) = - \int f` |
| `integral_pushforward phi` | Change of variable along measurable `phi` |
| `ge0_integral_pushforward` | Same, `f >= 0` (no integrability hyp) |
| `integral_dirac a` | `\int[\d_a]_(x in D) f = \d_a D * f a` |
| `integral_uniform` | Reduce uniform integral to Lebesgue |
| `integral_nneseries` | Swap `\int` and `\sum_(n <oo)` (Tonelli for series) |
| `null_set_integral` | `mu N = 0 → \int[mu]_(x in N) f = 0` |
| `negligible_integral` | Drop a null set from the domain |
| `ae_eq_integral g` | `ae_eq mu D f g → \int f = \int g` |
| `integral_ae_eq` | Converse: equal integrals on every measurable subset ⇒ `ae_eq` |
| `monotone_convergence` | Beppo Levi |
| `cvg_monotone_convergence` | Limit form |
| `dominated_convergence` | Three-way conjunction: integrability, error → 0, integral → integral |
| `integrable_lty` | `mu.-integrable D f → \int f < +oo` |
| `integrable_fin_num` | `… → \int f \is a fin_num` |
| `measurable_int mu` | Project measurability out of `mu.-integrable` |

The `ge0_*` prefix marks the variant with a non-negativity hypothesis
(`forall x, D x -> 0 <= f x`) replacing the integrability hypothesis.
For non-negative `f`, prefer `ge0_integral_*` — it has fewer side
conditions and works on extended reals where `\int f = +oo` is
allowed.

### 43.6 `under eq_integral do …`

The integral binder is `\int[mu]_(x in D) f x`; rewriting `f` requires
the integral analogue of §34.3's `under eq_bigr`:

```coq
(* WRONG -- per-x rewrite, fragile and ugly *)
apply: eq_integral => x xD; rewrite EFinM mulrC.

(* RIGHT *)
under eq_integral do rewrite EFinM mulrC.
```

Localise like `under eq_bigr`:

```coq
under [LHS]eq_integral do rewrite muleC.
under [RHS]eq_integral do rewrite -EFinM.
under [X in _ - X = _]eq_integral do rewrite funeneg_comp.
```

The bound variable is implicit in the `do tac` form. To split into
two goals (predicate-side and body-side), drop `do`:

```coq
under eq_integral.
  by move=> x /[!inE] Dx; rewrite mulrC.   (* or `over.` *)
```

Adjacent variants:

| Variant | When to use |
|---------|-------------|
| `eq_integral` | Equal integrand pointwise on `D` |
| `ae_eq_integral` | Equal `ae_eq mu D f g` (needs measurability and `ae_eq`) |
| `eq_measure_integral` | Two measures agreeing on the relevant sets |
| `under eq_fun` | Inside a `lim`, `[sequence ...]_n`, or other binder |

### 43.7 Probability measures

```coq
HB.mixin Record isProbability d (T : measurableType d) (R : realType)
    (P : set T -> \bar R) := { probability_setT : P setT = 1%E }.
#[short(type=probability)]
HB.structure Definition Probability d T R :=
  {P of @SubProbability d T R P & isProbability d T R P}.
```

The user-facing type is `probability T R`; the predicate
`probability_setT P : P setT = 1`.

Two factories:

- `Measure_isProbability.Build _ _ _ mu mu_setT_eq_1` — given any
  existing `{measure set T -> \bar R}`, attach the probability axiom
  and obtain a canonical `probability T R`.
- `Subprobability_isProbability.Build` — same from a subprobability.

The dirac measure is canonically a probability:

```coq
HB.instance Definition _ x :=
  Measure_isProbability.Build _ _ _ (@dirac _ T x R) (diracT R x).
```

`\d_a` is the notation, so writing `\d_a` inside `\int[...]` is
shorthand for the canonical probability instance — no explicit
ascription needed.

### 43.8 The "no `[the …]` ascription" rule

Once HB has declared a canonical instance (§15, §35.5,
playbook), `mu` *is* already a `{measure set T -> \bar R}` or a
`probability T R` in the inference graph. Re-ascribing breaks
forgetful inheritance and is rejected on review.

```coq
(* WRONG -- mu already has Measure_isProbability declared *)
Check [the probability T R of mu].

(* RIGHT *)
Check (mu : probability T R).   (* if a constraint is needed at all *)
Check mu.                       (* almost always sufficient *)
```

The exception is when you are *constructing* a fresh probability
locally and have not yet emitted an `HB.instance Definition _ := …`;
in that case use the factory directly (§35.2), not `[the …]`.

### 43.9 Common pitfalls

```coq
(* WRONG -- after `apply: mU` from measurable_fun setT _, the goal
   is `measurable (setT `&` _)`, not `measurable _`. *)
have := mU _ measurable_my_set.
apply: bar.   (* fails: setT `&` X /= X is not definitionally true *)

(* RIGHT *)
have := mU _ measurable_my_set.
rewrite setTI; apply: bar.
```

`setTI : setT `&` A = A` is the standard cleanup after invoking
`measurable_fun [set: T] f`.

```coq
(* WRONG -- spells out epsilon-N for an integral limit *)
apply/cvg_distP => eps eps0; near=> n; rewrite distrC.
have h : `|...| <= integral_of_diff. ...

(* RIGHT -- use the named convergence theorem *)
exact: cvg_dominated_convergence.       (* if dominator exists *)
exact: cvg_monotone_convergence.        (* if monotone *)
```

```coq
(* WRONG -- redundant ascription on a name with a canonical
   probability instance *)
have := probability_setT [the probability T R of \d_a].

(* RIGHT *)
have := probability_setT (\d_a : probability T R).
have := probability_setT \d_a.    (* if context constrains it *)
```

```coq
(* WRONG -- spells out the display *)
Lemma foo (T : measurableType default_measure_display) ... .

(* RIGHT *)
Lemma foo d (T : measurableType d) ... .          (* §22.4, §24.4 *)
```

```coq
(* WRONG -- rewriting under the integral binder by hand *)
apply: eq_integral => x xD; rewrite mulrC.

(* RIGHT *)
under eq_integral do rewrite mulrC.               (* §43.6, cf §34.3 *)
```

```coq
(* WRONG -- conflates Lebesgue and FTC integral notations *)
rewrite (integralE _ _ f).        (* but goal is `\int_(a <= x <= b)` *)

(* RIGHT *)
rewrite RintegralE.               (* or one of the FTC family *)
```

The two notations look similar but the FTC integral is `Rintegral`
over an interval, while `\int[mu]_x f x` is the Lebesgue integral
on `\bar R` — `integralE`, `integralD`, etc. apply only to the
latter. `Search Rintegral` finds the FTC analogues
(`Rintegral_cst`, etc., in `lebesgue_Rintegral.v`).

### 43.10 Quick decision flow

```
Need to prove `measurable_fun D f`?
  - f bundled as {mfun T >-> R}?     -> exact: measurable_funP f
  - f = g \o h with g measurable?    -> exact: measurableT_comp
  - f = g \+ h, g \* h, g \- h?      -> measurable_funD/M/B
  - f = cst c?                       -> exact: measurable_cst
                                       (or just `done` via Hint Extern)
  - f = id?                          -> exact: measurable_id
  - f = restriction of bigger F?     -> exact: measurable_funS or _funTS

Need to manipulate `\int[mu]_(x in D) f x`?
  - rewrite the integrand?           -> under eq_integral do <tac>
  - integrand = f1 + f2?             -> rewrite integralD
  - integrand = r%:E * f?            -> rewrite integralZl
  - integrand = cst c?               -> rewrite integral_cst
  - integrand = \1_A?                -> rewrite integral_indic
  - mu = \d_a?                       -> rewrite integral_dirac
  - need to push mu through phi?     -> rewrite integral_pushforward
  - swap with \sum_(n <oo)?          -> rewrite integral_nneseries
  - swap two integrals?              -> Fubini/Tonelli (lebesgue_integral_fubini.v)

Limit of a sequence of integrals?
  - sup, monotone f_n?               -> monotone_convergence
  - dominated by integrable g?       -> dominated_convergence
  - never roll an epsilon-N proof.

Probability measure?
  - given mu : measure with mu setT = 1?
        HB.instance := Measure_isProbability.Build ... mu mu1.
  - dirac/uniform/bernoulli?         -> instances are pre-declared.
  - `mu setT = 1` in a goal?         -> rewrite probability_setT
                                       (no ascription needed).
```

### 43.11 Sources

- `mathcomp/analysis/measure_theory/measurable_structure.v`
  (`measurable_display`, `measurableType`)
- `mathcomp/analysis/measure_theory/measurable_function.v`
  (`measurable_fun`, `{mfun ...}`, `measurable_funP`,
  `measurableT_comp`)
- `mathcomp/analysis/measurable_realfun.v`
  (arithmetic measurable lemmas)
- `mathcomp/analysis/measure_theory/measure_function.v`
  (`{measure set T -> \bar R}`)
- `mathcomp/analysis/measure_theory/dirac_measure.v` (`\d_`, `diracT`)
- `mathcomp/analysis/measure_theory/probability_measure.v`
  (`isProbability`, `Measure_isProbability`)
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integral_definition.v`
  (`\int[mu]_…` notation, `integralE`, `integral_indic`)
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integrable.v`
  (`integralD`, `integralB`, `integralZl`, `integral_pushforward`,
  `null_set_integral`, `integral_ae_eq`)
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integral_nonneg.v`
  (`integral_cst`, `integral_dirac`, `integral_nneseries`,
  `ae_eq_integral`)
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integral_monotone_convergence.v`
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integral_dominated_convergence.v`
  (Theorem `dominated_convergence`)
- `mathcomp/analysis/lebesgue_integral_theory/lebesgue_integral_fubini.v`
  (Tonelli/Fubini lemmas)
- `mathcomp/analysis/probability_theory/uniform_distribution.v`
  (`integral_uniform`)
- `mathcomp/analysis/charge.v` (Radon-Nikodym; signed measures share
  the `{measure ...}` discipline)

Cross-references: §22.4 and §24.4 (display arguments are wildcards),
§24.1 (do not ascribe canonical types), §29 / §34.3 (`under`
discipline), §35.5 (`[the …]` ascription is forbidden when HB
instances exist), §35 (HB canonical conversion), §44 (filter
combinators / `near=>` for cases not subsumed by
`monotone_convergence` / `dominated_convergence`).

---

