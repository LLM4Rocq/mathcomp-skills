## 47. Finite Functions (`{ffun T -> R}`) Idioms

The `finfun` library (`mathcomp/boot/finfun.v`, ~595 lines) is the
plumbing that turns "function from a `finType`" into a piece of
combinatorial data: an `{ffun T -> R}` is a `seq` indexed by
`enum T`, packaged so that `eqType`, `choiceType`, `countType`, and
`finType` structures on `R` lift to it for free. Three things make
finfun proofs distinctive: (1) the underlying `seq` is locked behind
`HB.lock Definition finfun`, so the only way in is the canonical
equation `ffunE`; (2) extensional equality and Leibniz equality
*coincide* (`ffunP`), unlike ordinary CiC functions; and (3) several
of mathcomp's most-used types (`'M[R]_(m, n)`, `{set T}`, `T ^ n`)
are wrappers around `{ffun ...}`, so the same `apply/...P; rewrite
!...E` chord recurs across §38 (matrix), §40 (finset), and here.
Reviewers reject hand-unfolding the `seq` representation; this
section codifies the canonical idioms.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `ffunE` | open any `[ffun x => E]` builder applied to `x` | §47.2, §47.3 |
| `ffunP` | reduce `f1 = f2` to pointwise equality | §47.2, §47.3 |
| `[ffun x => E]`, `finfun` | build an ffun from a function (not `fun x =>`) | §47.1, §47.4 |
| `eq_ffun`, `ffunK` | ffun from `=1`; round-trip the coercion | §47.2 |
| `sum_ffunE` | evaluate a `\sum` of ffuns at a point | §47.6 |
| `card_ffun` | `#\|{ffun T -> R}\| = #\|R\| ^ #\|T\|` | §47.2 |
| `familyP`, `pffun_onP` | reflect family / partial-support membership | §47.2, §47.7 |

### 47.1 Reading the notation

| Notation | Meaning | finfun.v line |
|----------|---------|---------------|
| `{ffun T -> R}` | non-dependent finite function `T : finType -> R` | 117 |
| `{ffun forall x : T, R x}` | dependent finite function | 117 |
| `{dffun forall x : T, R x}` | dep. alias inheriting `eqType`/... on `R x` | 120 |
| `T ^ n` | `{ffun 'I_n -> T}`, structurally positive | 124 |
| `[ffun x : T => E]` | builder with explicit domain | 134 |
| `[ffun x => E]` | builder, `T` inferred (`E` must not depend on `x`) | 137 |
| `[ffun=> E]` | constant builder, `[ffun _ => E]` | 140 |
| `f x` | application, via `fun_of_fin` coercion | 113 |
| `finfun g` | the canonical `[ffun x => g x]` constructor | 129 |
| `ffun0 aT0` | the unique element when `#\|aT\| = 0` | 172 |
| `fgraph f` | the `#\|aT\|.-tuple` of values of `f` (non-dep) | 299 |
| `tfgraph f` | the dep. `#\|aT\|.-tuple` of `Tagged` values | 203 |
| `Finfun G` | the ffun whose simple graph is `G : #\|aT\|.-tuple R` | 301 |
| `f \in family F` | `forall x, f x \in F x` (l. 244) | 222 |
| `f \in ffun_on R` | `forall x, f x \in R` | 342 |
| `y.-support f` | `[pred x \| f x != y]` | 364 |
| `f \in pffun_on y D R` | `y`-partial: support `\subset D`, range `\subset R` | 410 |

The bare-domain form `[ffun x => E]` requires that the type of `E`
not depend on `x` (l. 46-48); for dependent codomains use the
explicit-domain form `[ffun x : T => E]` with a type ascription on
`E`. The double-bracket type form `{ffun T -> R}` and the
single-bracket builder form `[ffun x => E]` are not
interchangeable: the first is a *type*, the second a *term*.

### 47.2 The core lemma family

Verified against `mathcomp/boot/finfun.v` at the line numbers shown
(rocq-9.1 / current `master`).

| Lemma | Line | Statement / use |
|-------|------|-----------------|
| `ffunE` | 175 | `(finfun g : {ffun T -> R}) x = g x` -- the canonical equation |
| `ffunP` | 181 | `(forall x, f1 x = f2 x) <-> f1 = f2` -- extensionality |
| `ffunK` | 194 | `cancel fun_of_fin finfun` (round-trip via the coercion) |
| `eq_ffun` | 322 | `g1 =1 g2 -> finfun g1 = finfun g2` (non-dep) |
| `eq_dffun` | 197 | dep. version of `eq_ffun` |
| `ffun0` | 172 | the trivial ffun when `#\|aT\| = 0` |
| `tnth_fgraph` | 303 | `tnth (fgraph f) i = f (enum_val i)` |
| `nth_fgraph_ord` | 347 | `nth x0 (fgraph f) i = f i` for `i : 'I_n` |
| `FinfunK` | 306 | `cancel Finfun fgraph` |
| `fgraphK` | 311 | `cancel fgraph Finfun` |
| `tuple_of_finfunK` | 286 | `cancel tuple_of_finfun finfun_of_tuple` |
| `finfun_of_tupleK` | 281 | `cancel finfun_of_tuple tuple_of_finfun` |
| `tfgraph_inj` | 220 | `injective tfgraph` (dep. graph identifies ffuns) |
| `codom_ffun` | 317 | `codom f = fgraph f` (definitional, often by `[]`) |
| `familyP` | 229 | reflect `(forall x, f x \in F x) (f \in family F)` |
| `ffun_onP` | 330 | reflect `(forall x, f x \in R) (f \in ffun_on R)` |
| `supportP` | 373 | reflect `(forall x \notin D, g x = y) (y.-support g \subset D)` |
| `pfamilyP` | 382 | reflect partial-family characterization |
| `pffun_onP` | 394 | reflect `pffun_on y D R` |
| `card_ffun` | 484 | `#\|{ffun aT -> rT}\| = #\|rT\| ^ #\|aT\|` |
| `card_dep_ffun` | 454 | `#\|{dffun forall x, rT x}\| = foldr muln 1 ...` |
| `card_family` | 419 | cardinality of a family |
| `card_pfamily` | 465 | cardinality of a partial family |
| `card_ffun_on` | 478 | `#\|ffun_on R\| = #\|R\| ^ #\|aT\|` |
| `card_pffun_on` | 472 | `#\|pffun_on y D R\| = #\|R\| ^ #\|D\|` |
| `sum_ffunE` (`nmodule.v` l. 1293) | -- | `(\sum_(i <- r \| P i) F i) x = \sum_(...) F i x` |
| `sum_ffun` (`nmodule.v` l. 1296) | -- | dual: pull the ffun out of the bigop |

The lemma names follow the §10 / §11 conventions: `E` for "open the
builder" (`ffunE`), `P` for the `reflect` view (`ffunP`,
`familyP`), `K` for cancellation (`ffunK`, `fgraphK`, `FinfunK`).

### 47.3 The `apply/ffunP => x; rewrite ffunE` chord

The recommended extensionality idiom for new code -- the `{ffun T
-> R}` analogue of `apply/matrixP => i j; rewrite !mxE` (§38.3) and
`apply/setP => x; rewrite !inE` (§40.5). Mathcomp upstream code
sometimes uses `apply: val_inj => /=` instead (exposing the
underlying `seq` and finishing by congruence); both are accepted in
review, but `apply/ffunP` is preferred for new code because it
keeps the abstract-function view and avoids leaking the `seq`
representation:

```coq
(* Goal: [ffun x => f x + g x] = [ffun x => g x + f x] *)
apply/ffunP => x.
rewrite !ffunE.
exact: addrC.
```

`ffunP` is the reflection `(forall x, f1 x = f2 x) <-> f1 = f2`; the
view `apply/ffunP` introduces a fresh `x` and leaves a pointwise
goal. After that, `rewrite ffunE` opens any `[ffun x => E]` builder
the new variable is applied to. `!ffunE` is the canonical form
because nested builders fire on each other.

```coq
(* Goal: [ffun x => F (G x)] = [ffun x => F (G x)]  (* trivial *) *)
by [].

(* Goal: [ffun x => f x] = f                        (* ffunK *) *)
exact: ffunK f.

(* Goal: [ffun x => F1 x] = [ffun x => F2 x]
   when you have hypothesis  H : forall x, F1 x = F2 x *)
exact: eq_ffun H.

(* Goal: f = g  with hypothesis H : f =1 g (extensional) *)
by apply/ffunP.
```

Once `apply/ffunP` has fired, you are working with `=` (not `=1`):
prefer Leibniz equality from that point on.

### 47.4 Builder vs. raw function

A persistent reviewer flag: confusing `[ffun x => F x]` (an element
of `{ffun T -> R}`) with `(fun x => F x)` (an element of `T -> R`).
They are *not* interchangeable: the first is locked combinatorial
data, the second is an opaque CiC term.

```coq
(* WRONG -- type mismatch (or worse, silent eta-expansion) *)
Definition foo : {ffun T -> R} := fun x => F x.

(* RIGHT -- explicit builder *)
Definition foo : {ffun T -> R} := [ffun x => F x].

(* RIGHT (alternative) -- the underlying constructor *)
Definition foo : {ffun T -> R} := finfun (fun x => F x).
```

The coercion `fun_of_fin` (l. 113) goes the other way: any `f :
{ffun T -> R}` may be applied as `f x` and the coercion fires
silently. This is one-way: applying an `{ffun}` is free, but to
*construct* one you must use `[ffun x => ...]` or `finfun`.

### 47.5 Where `{ffun}` hides underneath

Three of the most-used mathcomp types are thin wrappers around an
ffun, and the same `apply/...P; rewrite !...E` chord delegates to
`ffunP` / `ffunE` underneath:

| Wrapper type | Definition | Open with |
|--------------|------------|-----------|
| `'M[R]_(m, n)` (algebra/matrix.v l. 283) | `Variant matrix := Matrix of {ffun 'I_m * 'I_n -> R}` | `apply/matrixP => i j; rewrite !mxE` (§38.3) |
| `{set T}` (boot/finset.v l. 136) | `Inductive set_type := FinSet of {ffun pred T}` | `apply/setP => x; rewrite !inE` (§40.5) |
| `T ^ n` (finfun.v l. 124) | `{ffun 'I_n -> T}` directly | `apply/ffunP => i; rewrite !ffunE` |
| `n.-tuple T` | NOT an ffun (sized seq); use `eq_from_tnth` | `apply: eq_from_tnth => i` |

The `T ^ n` form is structurally positive (l. 14-18), so it can
appear in inductive type definitions where `n.-tuple T` cannot:

```coq
Inductive tree := node (n : nat) of tree ^ n.    (* finfun.v l. 148 *)
```

The bijections `tuple_of_finfun` / `finfun_of_tuple` (l. 277-289)
move between `T ^ n` and `n.-tuple T` when both forms are
convenient -- not when neither is.

### 47.6 Group / ring / module instances

When `R` carries an algebraic structure, `{ffun aT -> R}` inherits
it pointwise. The instances live in `mathcomp/boot/nmodule.v`
(zmodType / nmodType) and `mathcomp/algebra/ssralg.v` (ring /
module / etc.); all of them collapse to `ffunE` at the entry level:

| Section | Lines | Inherits |
|---------|-------|----------|
| `FinFunBaseAddMagma` ... `FinFunNmod` (nmodule.v) | 1214-1302 | `+`, `0`, `*+` |
| `FinFunZmod` (nmodule.v) | 1304-1318 | `-`, `addNr` |
| `FinFunSemiRing` (ssralg.v) | 7282-7327 | `*`, `1` (when `R : semiRingType`) |
| `FinFunRing` (ssralg.v) | 7337-7347 | `*`, `1` (when `R : ringType`) |

Two especially useful lemmas in this layer:

```coq
Lemma ffunMnE (f : {ffun aT -> rT}) n x : (f *+ n) x = f x *+ n.
                                     (* boot/nmodule.v l. 1283 *)

Lemma sum_ffunE (F : I -> {ffun aT -> rT}) x :
  (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
                                     (* boot/nmodule.v l. 1293 *)
```

`sum_ffunE` is the §34 chord for "evaluate a `\sum` of ffuns at a
point", and is what you reach for when a goal mixes `\sum_i F i`
with `(_ : {ffun _ -> _}) x` -- *not* `unlock`, *not* `apply/ffunP`
followed by manual induction.

### 47.7 `support` and partial-function families

`y.-support f` (l. 364) is `[pred x \| f x != y]` -- the indices
where `f` differs from the constant value `y`. `support` (the
zero-`y` case) is established in `ssralg.v`:

```coq
Notation support := 0.-support.    (* ssralg.v *)
```

Two predicate families on top of `support`:

```coq
y.-support f \subset D                (* f has y-support D *)
f \in pffun_on y D R                  (* support \subset D, range \subset R *)
f \in pfamily y D F                   (* support \subset D, f x \in F x for x \in D *)
```

Back in `mathcomp/boot/finfun.v`, the `P` views (l. 373, 382, 394)
are how you prove or destruct membership; `card_pffun_on` (l. 472)
gives the cardinality `#\|R\| ^ #\|D\|`. These are the canonical
primitives behind finitely-supported sums.

### 47.8 Common pitfalls

```coq
(* WRONG -- type ascription onto a raw function *)
Definition f : {ffun T -> R} := fun x => F x.
(* RIGHT *)
Definition f : {ffun T -> R} := [ffun x => F x].

(* WRONG -- entered a builder without ffunE *)
have : [ffun x => g x] x = g x by [].
(* RIGHT *)
have : [ffun x => g x] x = g x by rewrite ffunE.

(* WRONG -- funext / FunctionalExtensionality *)
apply: funext => x; rewrite ...
(* DISCOURAGED -- val_inj works (mathcomp upstream uses it) but
   exposes the underlying seq representation; prefer ffunP. *)
apply: val_inj => /=; rewrite ...
(* RIGHT *)
apply/ffunP => x; rewrite !ffunE.

(* WRONG -- treating the post-ffunP goal as boolean *)
apply/ffunP => x; apply/eqP.            (* goal is Leibniz =, not == *)
(* RIGHT -- after apply/ffunP the goal is f1 x = f2 x, stay in = *)
apply/ffunP => x; rewrite !ffunE; ring. (* assumes a comRingType carrier *)

(* WRONG -- unfolding the underlying seq *)
rewrite /finfun /fun_of_fin unlock /=.
(* RIGHT *)
rewrite ffunE.

(* WRONG -- evaluating a \sum of ffuns by hand *)
elim/big_rec2: _ => // i _ y _ <-; rewrite !ffunE.
(* RIGHT *)
rewrite sum_ffunE.

(* WRONG -- expecting eq_ffun to fire on extensionally equal terms *)
rewrite (eq_ffun (fun x => addrC _ _)).   (* eq_ffun is not setoid-rewritable *)
(* RIGHT -- go through ffunP *)
apply/ffunP => x; rewrite !ffunE addrC.

(* WRONG -- writing T ^ n then treating it as a tuple *)
Definition g (t : T ^ n) := tnth t i.                      (* tnth wants n.-tuple *)
(* RIGHT -- T ^ n is an ffun, apply directly *)
Definition g (t : T ^ n) := t i.
(* or, if you really want the tuple *)
Definition g (t : T ^ n) := tnth (tuple_of_finfun t) i.

(* WRONG -- recomputing the cardinality of {ffun T -> R} *)
Lemma my_lemma : #|{ffun T -> R}| = #|R| ^ #|T|.
Proof. (* manual induction on enum T *) ...
(* RIGHT *)
Proof. exact: card_ffun. Qed.
```

### 47.9 Quick decision flow

```
Goal involves {ffun T -> R}, [ffun x => ...], or an ffun-wrapped type.

  Equality of two ffuns?
    -> apply/ffunP => x; rewrite !ffunE        (pointwise)
    -> exact: eq_ffun H                         (when H : f1 =1 f2 already)
    -> exact: ffunK f                           (round-trip)

  Application of a builder?
    -> rewrite ffunE                            (one builder)
    -> rewrite !ffunE                           (nested)

  Goal is `(_ : {ffun _ -> _}) x` where the ffun is a sum / scaled?
    -> rewrite sum_ffunE / ffunMnE              (don't unlock)

  Constructing an ffun from a function f : T -> R?
    -> [ffun x => f x]                          (in terms / Definitions)
    -> finfun f                                 (when type-checking is fragile)

  Cardinality?
    -> card_ffun         (#|R| ^ #|T|)
    -> card_ffun_on      (#|R| ^ #|T|, range-restricted)
    -> card_pffun_on     (#|R| ^ #|D|, support-restricted)
    -> card_dep_ffun     (foldr muln 1 ...)

  Family / support / partial function?
    -> familyP   (forall x, f x \in F x)
    -> supportP  (forall x \notin D, g x = y)
    -> pfamilyP / pffun_onP

  Working with T ^ n vs. n.-tuple T?
    -> tuple_of_finfun / finfun_of_tuple        (the bijections)
    -> nth_fgraph_ord / tnth_fgraph             (drop into seq form)

  The wrapper case (matrix / set)?
    -> apply/matrixP; rewrite !mxE              (§38.3)
    -> apply/setP; rewrite !inE                 (§40.5)
    -> apply/ffunP; rewrite !ffunE              (raw {ffun})
```

### 47.10 Sources

`mathcomp/boot/finfun.v` (file header lines 7-79; non-dep theory in
`Section FunPlainTheory` l. 293-333; dep. theory in
`Section DepPlainTheory` l. 167-232; cardinality in
`Section FinFunTheory` l. 459-487; the `ffunE` / `ffunP` pair l. 175-192
is the file's first theorem). The bigop-over-ffun lemmas
`sum_ffunE` / `sum_ffun` are in `mathcomp/boot/nmodule.v` l. 1276-1302;
semiring instances in `mathcomp/algebra/ssralg.v` `Section
FinFunSemiRing` l. 7282-7327; ring instances in `Section FinFunRing`
l. 7337-7347.

Wrapper types: `'M[R]_(m, n)` is `Variant matrix := Matrix of {ffun 'I_m * 'I_n -> R}`
(`mathcomp/algebra/matrix.v` l. 283); `{set T}` is
`Inductive set_type := FinSet of {ffun pred T}`
(`mathcomp/boot/finset.v` l. 136); `T ^ n` is `{ffun 'I_n -> T}`
directly (boot/finfun.v l. 124). All three delegate the canonical-equation
proof to `ffunE`.

Cross-ref §10 (E / K / P naming), §11 (suffixes), §28 (reflection),
§34 (bigops, `sum_ffunE` is the canonical chord), §38 (matrix uses
`{ffun}` underneath), §40 (finset uses `{ffun}` underneath), §36
(`finType` HB hierarchy). MathComp Book chapter 7 ("Finite Sets")
discusses the `{ffun}`-as-data perspective in passing.

---

