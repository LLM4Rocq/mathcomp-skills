## 44. Topology and Filter Idioms

mathcomp-analysis builds analysis on top of a *filter* layer
(`mathcomp/classical/filter.v`) and a *topology* layer
(`mathcomp/analysis/topology_theory/`), with `normedtype.v` adding
norm-based machinery. §19 and §30 covered scattered conventions;
this section consolidates the API into one reference. The cardinal
rule is the same as §36: **ask for the weakest structure the lemma
actually uses** (`Filter F`, not `ProperFilter F`; `topologicalType`,
not `pseudoMetricType`).

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `nbhs`, `\forall x \near F, P` | the neighborhood filter; near-statements | §44.2 |
| `filterS`, `filterS2`, `filterS3` | lift 1/2/3 near-facts pointwise, one line | §44.4 |
| `near=> x … near: x … end_near` | refine an epsilon / extract a near-witness | §44.5 |
| `F --> x`, `cvg F`, `lim F` | filter convergence; limit value or predicate | §44.6 |
| `cvgD`, `cvgM`, `cvgZ` | arithmetic of limits (`-->` form) | §44.7 |
| `nbhs_ballP`, `nbhs_normP` | view a neighborhood as a ball / norm bound | §44.8 |
| `compact_near_coveringP`, `closure_id` | compactness / closure workhorses | §44.9 |

### 44.1 The filter layer

A filter on `T` is a `set_system T := set (set T)` (alias declared in
`mathcomp/classical/set_interval.v`) that satisfies the `Filter`
typeclass:

```coq
Class Filter {T : Type} (F : set_system T) := {
  filterT : F setT ;
  filterI : setI_closed F ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.

Class ProperFilter {T : Type} (F : set_system T) := {
  filter_not_empty : ~ F set0 ;
  filter_filter : Filter F
}.
```
(`filter.v` lines 430-444.)

The two `Hint Mode` declarations — `Hint Mode Filter - !` and
`Hint Mode ProperFilter - !` (§37.8) — block typeclass search until a
head constructor is known on the filter argument; this is why
`apply: filterS` works on `nbhs x P` but loops on a unification
variable.

`filter_on T` and `pfilter_on T` are the bundled *structures*
(§35) that pair a filter with its proof:

```coq
Structure filter_on T :=
  FilterType { filter :> set_system T; _ : Filter filter }.
Structure pfilter_on T :=
  PFilterPack { pfilter :> _; _ : ProperFilter pfilter }.
```
(`filter.v` 458-475). Use them when a lemma takes a *filter as a
value*; use the `Filter F` / `ProperFilter F` typeclass when a lemma
takes a `set_system T` and *requires* the property.

### 44.2 `nbhs`, `\near`, and the bundled neighborhood filter

Every `filteredType U` provides `nbhs : T -> set_system U`
(`filter.v` 218-224). For a `topologicalType`, `nbhs x` is the
classical neighborhood filter of `x` and is automatically
`ProperFilter` (`topology_structure.v` line 125). The notation
layer provides:

```coq
Notation "{ 'near' x , P }"        := (@prop_near1 _ _ x _ ...).
Notation "'\forall' x '\near' x_0 , P" := {near x_0, forall x, P}.
Notation "'\near' x , P"            := (\forall x \near x, P).
Notation "F --> G"                  := (cvg_to (nbhs F) (nbhs G)).
Notation cvg F                      := (F --> lim F).
```
(`filter.v` 280-328.)

`\forall x \near F, P x` is **definitionally** `F (fun x => P x)`
(`nearE`, line 293). Treat it as the user-facing form: read
`F P` only when actually manipulating filter membership.

### 44.3 Choosing the hypothesis: weakest structure first

Apply §36's rule across the topology stack. The hierarchy
(cross-ref §35):

```text
       nbhsType  (just a `nbhs : T -> set_system T`)
          |
          v   + open / openE_subproof  (interior axioms)
     topologicalType                      (analysis/topology_theory/topology_structure.v 103)
          |
          v   + uniformity entourage / ball
       uniformType   /   pseudoMetricType (pseudometric_structure.v)
                                |
                                v   + norm   pseudoMetricNormedZmodType
                                              (analysis/normedtype_theory/pseudometric_normed_Zmodule.v 141)
                                                          |
                                                          v   + scaling
                                                       normedModType
                                                       (analysis/normedtype_theory/normed_module.v 84)
```

| Lemma uses... | Hypothesis to ask for |
|---------------|-----------------------|
| only `nbhs`, `\near`, `--> ` | `topologicalType` |
| `ball`, `nbhs_ballP` | `pseudoMetricType R` |
| `\| _ \|`, `nbhs_normP` | `pseudoMetricNormedZmodType R` |
| `*:` (scaling), `cvgZ` | `normedModType K` |

Reviewer rule (analysis PRs across the topology
refactor): a lemma proved over `realType` that nowhere uses the
order should be re-stated over `normedModType R` — and one only
using `\near` should drop to `topologicalType`. Generalisation
requests are the second-most-frequent rejection (§21, item 8).

### 44.4 The core filter combinators

Pre-bundled "lift a pointwise fact through a filter" lemmas, all
in `filter.v`:

| Lemma | Statement (informal) | Line |
|-------|----------------------|------|
| `filterT` | `F setT` | 431 |
| `filterI` | `F P -> F Q -> F (P `&` Q)` | 432 |
| `filterS` | `P `<=` Q -> F P -> F Q` | 433 |
| `filterE` | `(forall x, P x) -> F P` (Filter `F`) | 648 |
| `filter_app` | `F (fun x => P x -> Q x) -> F P -> F Q` | 652 |
| `filter_app2` | binary version of `filter_app` | 657 |
| `filterS2` | `(forall x, P x -> Q x -> R x) -> F P -> F Q -> F R` | 667 |
| `filterS3` | ternary version | 672 |
| `nearW` | `(forall x, P x) -> \forall x \near F, P x` | 644 |
| `near_andP` | `\near F, (P /\ Q) <-> \near F, P /\ \near F, Q` | 692 |
| `filter_prod` | product filter `F * G` on `T * U` | 260 |
| `filter_pair` (`filter2P`) | unpack a near in a product | 709 |
| `nearP_dep` | `\near (F, G), P x.1 x.2 -> \near F, \near G, ...` | 700 |

Use combinators when the witness (epsilon, ball radius, ...) does
not need to be refined on each occurrence:

```coq
(* CORRECT -- two near-properties combine pointwise *)
apply: filterS2 fP gQ => x Px Qx; exact: PQR.

(* WRONG -- opening near=> for a purely pointwise step *)
near=> x; have Px := near fP x; have Qx := near gQ x; exact: PQR.
Grab Existential Variables. all: end_near.
```
(§19; §30.3.) Reviewers flag the `near=>` skeleton as overkill
when `filterS` / `filterS2` / `filterS3` would close the goal in
one line.

### 44.5 The `near=>` skeleton (cross-ref §30.3)

When a step *does* need to refine epsilons or extract an arbitrary
near-witness, the canonical shape is:

```coq
Lemma foo (F : set_system R) (FF : Filter F) ... :
    \forall x \near F, P x.
Proof.
near=> x.                       (* introduces x : R and an opaque hypothesis *)
  ...
  by near: x; apply: cvg_dist; rewrite // subr_gt0.
Unshelve. all: end_near.        (* (modern) closes the existentials *)
Qed.
```

Either `Unshelve. all: end_near.` or
`Grab Existential Variables. all: end_near.` works; the latter is
the legacy form still found in `filter.v` line 622 (`Ltac end_near
:= do ?exact: in_filterT.`). Forgetting this trailer is the most
common `near` pitfall — the proof closes locally but the file
fails to compile, with a confusing "uninstantiated existential"
message.

### 44.6 Convergence and limit (`-->`, `cvg`, `lim`)

| Notation / lemma | Meaning | Source |
|------------------|---------|--------|
| `F --> x` | `nbhs x `<=` nbhs F` (filter convergence) | `filter.v` 320 |
| `lim F` | `get (fun l => F --> l)`; `point` if no such `l` | `filter.v` 326 |
| `cvg F` (notation) | `F --> lim F` | `filter.v` 328 |
| `[cvg F in T]` | typed form, `pfilteredType` | `filter.v` 327 |
| `cvgP F l` | `F --> l -> cvg F` | `filter.v` 362 |
| `cvg_ex` | `cvg F <-> exists l, F --> l` | `filter.v` 354 |
| `dvgP` | `~ cvg F -> lim F = point` | `filter.v` 377 |
| `cvg_toP` | `cvg F -> lim F = l -> F --> l` | `filter.v` 369 |
| `cvg_cst` | constant sequences converge | `topology_structure.v` 346 |
| `cvg_id` | `(id : T -> T) @ x --> x` | `topology_structure.v` |

§19 lemma-string rule, recapped: prefer `F --> x` (`cvg`-prefixed
lemmas) over `lim F = x` (`lim`-prefixed lemmas); use
`cvg F` / `is_cvg` (the `is_cvg` family of lemmas in
`pseudometric_normed_Zmodule.v` and `normed_module.v`) only when
the limit's value is irrelevant.

### 44.7 Arithmetic of limits

In `pseudometric_normed_Zmodule.v` (1123-1182) and
`normed_module.v` (516-554):

| Lemma | Statement |
|-------|-----------|
| `cvgN` | `f @ F --> a -> -f @ F --> -a` |
| `cvgD` | `f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b` |
| `cvgB` | analogous for subtraction |
| `cvgM` | `f @ F --> a -> g @ F --> b -> (f \* g) @ F --> a * b` |
| `cvgV` | `a != 0 -> f @ F --> a -> f\^-1 @ F --> a^-1` |
| `cvgZ` | scaling: `s @ F --> k -> f @ F --> a -> s *: f @ F --> k *: a` |
| `cvg_norm` | `f @ F --> a -> \|f x\| @[x --> F] --> \|a\|` |
| `cvgrPdist_lt` | `f @ F --> a <-> \forall e > 0, \forall x \near F, \|f x - a\| < e` |

The `is_cvg*` family (`is_cvgD`, `is_cvgM`, `is_cvgN`, `is_cvgV`,
`is_cvgZ`, ...) drops the limit value. They exist *only* to ride
along in `cvg`-only contexts. Naming follows §10:
`cvg<Symbol>` for the `-->` form, `is_cvg<Symbol>` for the
predicate form.

### 44.8 `nbhs_ballP` and `nbhs_normP`: view-style entry

`nbhs_ballP` (`pseudometric_structure.v` 186) and `nbhs_normP`
(`pseudometric_normed_Zmodule.v` 195) unfold a neighborhood filter
to an explicit ball / norm condition:

```coq
Lemma nbhs_ballP {R : numDomainType} {M : pseudoMetricType R} (x : M) P :
  nbhs x P <-> exists2 e, 0 < e & ball x e `<=` P.

Lemma nbhs_normP (x : V) P :
  (\near x, P x) <-> exists2 e, 0 < e & forall y, `|y - x| < e -> P y.
```

Idiomatic use as views (§30.5):

```coq
move=> /nbhs_ballP[_ /posnumP[eps] subP].   (* hypothesis side *)
apply/nbhs_normP; exists e => // y ye; ...   (* goal side *)
```

`/posnumP[eps]` immediately bundles the positivity into a `{posnum
R}` (§36.6); reviewers reject the unbundled `eps_gt0 : 0 < eps`
when `posnumP` is one symbol away.

### 44.9 Compactness, closure, openness

`mathcomp/analysis/topology_theory/compact.v` 104:
```coq
Definition compact A := forall (F : set_system T),
  ProperFilter F -> F A -> A `&` cluster F !=set0.
```
`closed` and `closure` live in `topology_structure.v` (654, 740):
```coq
Definition closure (A : set T) :=
  [set p : T | forall B, nbhs p B -> A `&` B !=set0].
Definition closed (D : set T) := closure D `<=` D.
```

| Lemma | Use case |
|-------|----------|
| `compact_set1` | singletons are compact |
| `subclosed_compact` | closed subset of a compact is compact |
| `compact_near_coveringP` | reformulate `compact A` via near-covers |
| `closure_id` | `closed E <-> E = closure E` |
| `subset_closure` | `A `<=` closure A` |
| `open_closedC` | `open D -> closed (~` D)` |
| `bigcup_open`, `closed_bigI` | preservation under arbitrary unions / intersections |
| `within_nbhs_proper` | `closure A p -> ProperFilter (within A (nbhs p))` |

The `compactness_filter`-style results are stated as: *every proper
filter on a compact set has a cluster point*. Search for
`compact` in the dedicated file rather than in `topology.v`
(which is just a re-export aggregator).

### 44.10 Common pitfalls

1. **Manually unfolding `--> +oo`**. If you write
   `move=> M; have [N _] := ...`, you are reproving the definition
   of divergence. Use `cvgryPgt`, `cvgryPge`, `cvgrnyPgt` (norm
   variants) or the bundled `cvg_*` lemmas (analysis
   PR #422; §30.6).
2. **`near=>` for one-shot pointwise lifts**. `filterS2` / `filterS3`
   close the goal in one line; `near=>` opens an existential block
   that has to be closed with `Unshelve. all: end_near.` (§44.4-5).
3. **Forgetting `Unshelve. all: end_near.`**. Symptoms: the proof
   closes but compilation fails with
   `Unable to satisfy the following constraints: ?Goal_1 : near_key`.
   Always pair `near=>` with a closer (§30.3, §44.5).
4. **Mixing `lim` and `cvg`**. Lemmas like `lim_eq` need `cvg F`
   as a side condition — without it, `lim F` is `point` (the
   default carrier element) and the goal is silently false.
   Prefer the `--> x` form so the limit value is in the type
   (§19, §44.6).
5. **`finType`-strength on a topological lemma**. Asking for
   `realType` when `topologicalType` (or `pseudoMetricType R`)
   suffices is the topology analogue of §36's "weakest level"
   rule. Reviewers consistently flag this.
6. **`Filter F` vs `ProperFilter F`**. Use `Filter` whenever the
   proof does not need `~ F set0`; reviewers ask
   for the weaker hypothesis. Hands-on test: if your proof
   uses `filter_ex` or instantiates the filter with a witness,
   you need `ProperFilter`; otherwise `Filter` suffices.
7. **Bare `Definition` aliasing a topological type**. Same trap
   as §35.5: a `Definition X := T.` over a `topologicalType`
   breaks forgetful inheritance for `nbhs`, `cvg`, ...
   Use `Notation`, a `Module` wrapper, or `Topological.copy`.
8. **`apply: nbhs_ballP` (forward)** instead of `apply/nbhs_ballP`
   (view) — the boolean view rewrites the goal in place; the raw
   `apply:` leaves a useless implication head. Always use the
   view-application form for `*P` lemmas (§32, §44.8).
9. **`filter_prod` rolled by hand**. `filter_pair` / `filter2P` /
   `nearP_dep` already package the product-filter idioms; do not
   manually destructure `(P, Q) /=[FP GQ] H`.
10. **Not `Typeclasses Opaque nbhs`**. `nbhs` is `Typeclasses
    Opaque` (`topology_structure.v` line 127) so instance search
    does not unfold the filter; if you `Unset Typeclasses Opaque`
    locally, instance loops follow. Don't.

### 44.11 Quick decision flow

```
Goal mentions a filter F.
  Need just `Filter F`?              -> ask for `Filter F` only.
  Need to extract a witness?         -> ask for `ProperFilter F`.

Goal is `\forall x \near F, P x` (i.e. F P).
  P is a pointwise consequence of one near-fact?
                                     -> apply: filterS H.
  Of two / three near-facts?         -> filterS2 / filterS3.
  Need to refine eps / radius?       -> near=> x ... near: x ...
                                        Unshelve. all: end_near.

Goal is `f @ F --> y`.
  Limit value matters?               -> use `cvg<Sym>` family.
  Only convergence matters?          -> use `is_cvg<Sym>` family.
  Topology gives ball / norm?        -> apply/nbhs_ballP, /nbhs_normP.

Goal mentions `compact A` / `closed A`.
  `compact_near_coveringP`, `subclosed_compact`, `closure_id`,
  `bigcup_open`, `closed_bigI` are the workhorses.

Stuck on a `nbhs x P`?
  rewrite nbhsE => -[B [open_nbhs] sBP].   (* topology *)
  /nbhs_ballP[_/posnumP[e] subP].           (* metric *)
  /nbhs_normP[e e0 subP].                   (* normed *)
```

### 44.12 Sources

- `mathcomp/classical/filter.v` (filter typeclass at lines 430-444;
  combinators 644-690; `cvg` / `lim` notation 320-328;
  `\near` / `\forall ... \near` 280-289;
  `Hint Mode` 435, 444; `end_near` 622).
- `mathcomp/analysis/topology_theory/topology_structure.v`
  (`topologicalType` 103-105, `nbhs_pfilter` 125, `closure` 654,
  `closed` 740, `cvg_cst` 346).
- `mathcomp/analysis/topology_theory/compact.v` (`compact` 104,
  `compact_near_coveringP` 193).
- `mathcomp/analysis/topology_theory/pseudometric_structure.v`
  (`nbhs_ballP` 186).
- `mathcomp/analysis/normedtype_theory/pseudometric_normed_Zmodule.v`
  (`nbhs_normP` 195, `cvgN` 1123, `cvgD` 1141, `cvg_norm` 1178).
- `mathcomp/analysis/normedtype_theory/normed_module.v`
  (`normedModType` 84-85, `cvgM` 530, `cvgV` 516, `is_cvgZ` 477).
- The aggregator `mathcomp/analysis/topology_theory/topology.v` and
  `mathcomp/analysis/normedtype_theory/normedtype.v` re-export the
  above; `Search ... inside Topology` and `Search ... inside Normedtype`
  scope queries to the public API.
- analysis PR #283 (`near` skeleton template);
  PR #422 (prefer bundled `cvg_*` over manual
  divergence unfolding); PR #786 (forgetful inheritance via
  `Topological.copy`); PR #1230 (general topology refactor).
- §19 (convergence naming `cvg` / `lim` / `is_cvg`); §30.3-30.6
  (the `near` skeleton, `posnumP`, view applications); §35
  (HB hierarchy and `Topological.copy`); §36 (the
  weakest-hypothesis rule).

---

