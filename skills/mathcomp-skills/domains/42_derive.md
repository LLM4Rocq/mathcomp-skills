## 42. Derivative and `is_derive` Idioms

mathcomp-analysis provides three layered notions of differentiation in
`mathcomp/analysis/derive.v` (~2330 lines): the **Fréchet differential**
`'d f x`, the **directional derivative** `'D_v f x`, and the
**typeclass-driven** `is_derive x v f df` predicate. New users
routinely conflate them or fall back on Coq stdlib `Derive`. Two
upstream-canonical paths coexist: for **computing a derivative as a
value** (`f^`() x = ?`), declare `is_derive` instances and extract
with `derive_val`; for **establishing derivability before MVT/Rolle**
(`derivable f x v`), `derivable<op>` chains (`derivableD`,
`derivableM`, ...) remain idiomatic. mathcomp-analysis source uses
both. This section codifies when each path applies.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `is_derive x v f df` | pack derivability + value as a typeclass | §42.1, §42.2 |
| `derive_val` | extract `'D_v f a = df` from a resolved instance | §42.2, §42.3 |
| `ex_derive` | get `derivable f a v` from any `is_derive` premise | §42.2, §42.8 |
| `is_derive_eq` | adjust the derivative value to the goal's shape | §42.4 |
| `is_deriveD`, `is_deriveM`, `is_deriveX` | sum / product / power instances | §42.2 |
| `derivable1_diffP`, `diff_derivable` | bridge `derivable` and `differentiable` | §42.2, §42.5 |
| `MVT`, `Rolle` | mean-value / Rolle witnesses on an interval | §42.7 |

### 42.1 Reading the notation

`mathcomp/analysis/derive.v` defines four user-facing concepts; only
the last two are routine in proof scripts.

| Notation | Definition | Meaning |
|----------|-----------|---------|
| `'d f x` | `diff` (l. 72), `Notation` (l. 166) | Fréchet differential, a `{linear V -> W}` continuous map |
| `differentiable f x` | l. 84-85 | predicate: `'d f x` exists |
| `'D_v f x` | `derive` (l. 240); `Notation` (l. 327) | directional derivative of `f` at `x` along `v` |
| `derivable f a v` | l. 246 | predicate: the directional limit at `a` along `v` exists |
| `f^`()` | `derive1` (l. 379) | one-dimensional derivative for `f : R -> V`; defined as `'D_1 f` |
| `f^`(n)` | `derive1n` (l. 395) | `iter n derive1 f` |
| `'J f p` | `jacobian` (l. 180) | Jacobian matrix for `'rV[R]_n -> 'rV[R]_m` |
| `is_derive a v f df` | `Class`, l. 249 | `derivable f a v /\ 'D_v f a = df` packed as a typeclass |

The sole "computational" derivative is `'D_v f x`. `'d f x` is the
linear map; one usually moves between them with `deriveE` (l. 334)
`: differentiable f a -> 'D_v f a = 'd f a v`.

`derive1` lives in `classical_set_scope` — a stray `f^`()` in
`ring_scope` does not parse. Open `Local Open Scope classical_set_scope.`
(§6) at section start, or write `(f^`())%classic`.

A subtle but load-bearing fact: **`is_derive` is directional** even on
`R^o`. The "ordinary" derivative of `f : R -> R` at `x` is
`is_derive x 1 f (f^`() x)` — the `1` is the direction in `R^o`, not
a placeholder. Forgetting it is the most common newcomer error.

### 42.2 The `is_derive` typeclass

`is_derive` is declared as a `Class` with two fields:

```coq
Class is_derive (a v : V) (f : V -> W) (df : W) := DeriveDef {
  ex_derive : derivable f a v ;
  derive_val : 'D_v f a = df
}.
```
(`derive.v` l. 249-252)

Every algebraic operation has an associated `Global Instance`.
Resolution picks them up automatically when the goal is
`is_derive _ _ _ ?df`. `derive.v` does not declare an explicit
`Hint Mode is_derive`, so resolution uses the default ("any
position is unconstrained"); in practice the head of `f` drives
lookup via canonical-instance unification on each `is_derive_<op>`
instance's right-hand side:

| Instance | File:line | Direction & operation |
|----------|-----------|-----------------------|
| `is_derive_cst` | derive.v 1122 | `is_derive x v (cst a) 0` |
| `is_derive_id` | derive.v 1268 | `is_derive x v id v` |
| `is_deriveNid` | derive.v 1275 | `is_derive x v -%R (- v)` |
| `is_deriveD` | derive.v 1164 | sum: `df + dg` |
| `is_deriveB` | derive.v 1218 | difference: `df - dg` |
| `is_deriveN` | derive.v 1211 | negation |
| `is_deriveZ` | derive.v 1250 | scalar multiple `k *: f` |
| `is_deriveM` | derive.v 1335 | product (Leibniz): `f x *: dg + g x *: df` |
| `is_deriveX` | derive.v 1343 | power: `(n%:R * f x ^+ n.-1) *: df` |
| `is_derive_sum` | derive.v 1171 | `\sum_(i < n) h i` (cf. §34) |
| `is_derive_shift` | derive.v 1409 | `is_derive x v (shift k) v` |
| `is_diff_comp` | derive.v 775 | composition (Fréchet level, priority 99) |
| `is_derive_expR` | exp.v 356 | `is_derive x 1 expR (expR x)` |
| `is_derive1_ln` | exp.v 799 | `0 < x -> is_derive x 1 ln x^-1` |
| `is_derive1_powR` | exp.v 1121 | `0 < x -> is_derive x 1 (powR ^~ a) (a * x `^ (a - 1))` |
| `is_derive_sin` | trigo.v 274 | `is_derive x 1 sin (cos x)` |
| `is_derive_cos` | trigo.v 300 | `is_derive x 1 cos (- sin x)` |
| `is_derive1_sqrt` | realfun.v 1926 | `0 < x -> is_derive x 1 sqrt (2 * sqrt x)^-1` |

`is_deriveV` (realfun.v 1885) is a *lemma*, not an instance — `f x != 0`
is a side condition resolution cannot guess; supply it manually.

The bridging projections are first-class lemmas:

| Lemma | Statement |
|-------|-----------|
| `derive_val` | `'D_v f a = df` (the `is_derive` field, used as a rewrite) |
| `ex_derive` | `derivable f a v` (the other field) |
| `derivableP` (l. 1113) | `derivable f x v -> is_derive x v f ('D_v f x)` |
| `derivable1P` (l. 1105) | `derivable f x 1 <-> derivable (fun h => f (h *: v + x)) 0 1` |
| `derivable1_diffP` (l. 1080) | `derivable f x 1 <-> differentiable f x` |
| `diff_derivable` (l. 1116) | `differentiable f a -> derivable f a v` |

A `#[global] Hint Extern 0 (derivable _ _ _) => solve[apply: ex_derive] : core`
(l. 329) makes `done` discharge `derivable f a v` whenever an
`is_derive` instance is in scope — keep this in mind when a side
condition closes "magically."

### 42.3 The canonical workflow: `derive_val` extraction

The key idiom: state the derivative value, then extract it from the
typeclass-resolved instance.

```coq
(* WRONG -- manual chain of derivability lemmas, the apply tower *)
Lemma deriv_polyExample x : ((fun y => y ^+ 2)^`())%classic x = 2 * x.
Proof.
rewrite derive1E.
have d_id : derivable (id : R -> R) x 1 := derivable_id _ _.
rewrite (deriveX d_id) derive_id.
(* tedious bookkeeping ... *)
Abort.

(* RIGHT -- declare the value, let the typeclass mechanism find it *)
Lemma deriv_polyExample x : ((fun y => y ^+ 2)^`())%classic x = 2 * x.
Proof.
rewrite derive1E.
rewrite (@derive_val _ _ _ _ _ _ _ (is_deriveX 2 (is_derive_id x 1))).
by rewrite expr1 mulr1.
Qed.
```

Read this as: *"the derivative of `id ^+ 2` at `x` along `1`, by
`is_deriveX` applied to `is_derive_id`, has value
`(2%:R * x ^+ 1) *: 1`; project that out with `derive_val`."*

The seven leading underscores are not a code smell — they correspond
to `R V W f n x v` (the parameters of `is_deriveX`) which Rocq cannot
infer without telling it which instance to pick. With a
`Global Instance` declaration the eight-arg `@derive_val` can be
replaced by:

```coq
have D := @is_deriveX _ _ _ _ 2 x 1 _ (is_derive_id _ _).
by rewrite (derive_val D) /= ...
```

or, in a goal where the head is *directly* `'D_v f x`:

```coq
by rewrite [in 'D__ _ _]derive_val.
```

### 42.4 The `is_derive_eq` rewrite-time variant

`is_derive_eq` (derive.v 1131) lets you *adjust* the derivative value
after the typeclass has produced one:

```coq
Lemma is_derive_eq f (x v : V) (df f' : W) :
  is_derive x v f f' -> f' = df -> is_derive x v f df.
```

Use case: the typeclass produces
`is_derive x v (f * g) (f x *: dg + g x *: df)`, but the goal asked
for `(df * g x + f x * dg)` (re-shuffled). Instead of fighting the
typeclass:

```coq
(* RIGHT *)
apply: is_derive_eq.
  by [].             (* resolution finds the instance *)
by rewrite /GRing.scale /= mulrC addrC.
```

The companion lemma `trigger_derive` (derive.v 2207) plays the same
role for `realType`:

```coq
Lemma trigger_derive (R : realType) (f : R -> R) x x1 y1 :
  is_derive x (1 : R) f x1 -> x1 = y1 -> is_derive x 1 f y1.
```

The literal docstring in the file is **"Trick to trigger type class
resolution"** — i.e. when typeclass resolution fails to fire because
the goal's `df` is not in normal form, `apply: trigger_derive` forces
the search and leaves the simplification as a side goal.

### 42.5 `derivable` vs `is_derive`: when to use which

Three regimes, three predicates:

| Goal shape | Use | Why |
|------------|-----|-----|
| Hypothesis: "the limit exists" | `derivable f x v` | weakest predicate; `MVT`, `Rolle`, `derivable_within_continuous` take this |
| Need to compute the value | `is_derive x v f df` | typeclass mechanism produces `df` definitionally |
| Statement of an elementary lemma | `is_derive` instance | composes downstream by typeclass resolution |
| Multivariate Fréchet calculus | `differentiable f x` / `'d f x` | linear-map-level reasoning, `diff_comp`, Jacobian |

Convert with the bridges in §42.2: `derivableP`, `derivable1_diffP`,
`diff_derivable`, `is_derive_eq`. Reviewers reject statements of the
form `derivable f x v /\ 'D_v f x = df` — that is exactly what
`is_derive` packs.

### 42.6 Composition

Two composition lemmas, at different layers:

```coq
(* Fréchet level (derive.v 762, l. 775 instance) *)
Lemma diff_comp f g x :
  differentiable f x -> differentiable g (f x) ->
  'd (g \o f) x = 'd g (f x) \o 'd f x.

Global Instance is_diff_comp f df g dg x :
  is_diff x f df -> is_diff (f x) g dg ->
  is_diff x (g \o f) (dg \o df) | 99.

(* One-dimensional, the chain rule (derive.v 2061) *)
Lemma derive1_comp (R : realFieldType) (f g : R -> R) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  (g \o f)^`() x = g^`()%classic (f x) * f^`()%classic x.
```

There is **no** `is_derive_comp` for the directional case at general
`v` — when you need it, go via `is_diff_comp` (priority 99 keeps it
out of the way of unification) or use `derive1_comp` after reducing
to dimension one with `derivable1P`. For inverse functions, use
`is_derive_inverse` (`realfun.v` l. 1894) — it is what powers
`is_derive1_ln`, `is_derive_acos`, `is_derive_atan`, etc.

### 42.7 `derivable_within_continuous` and `MVT`/`Rolle`

For derivatives on a subset, the canonical lemma is:

```coq
Lemma derivable_within_continuous f (i : interval R) :
  {in i, forall x, derivable f x 1} -> {within [set` i], continuous f}.
```
(derive.v l. 1091)

Mean Value Theorem and Rolle (derive.v l. 1584-1647):

```coq
Lemma Rolle (R : realType) (f : R -> R) (a b : R) :
  a < b -> (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  {within `[a, b], continuous f} -> f a = f b ->
  exists2 c, c \in `]a, b[%R & is_derive c 1 f 0.

Lemma MVT (R : realType) (f df : R -> R) (a b : R) :
  a < b -> (forall x, x \in `]a, b[%R -> is_derive x 1 f (df x)) ->
  {within `[a, b], continuous f} ->
  exists2 c, c \in `]a, b[%R & f b - f a = df c * (b - a).
```

Note the asymmetry: Rolle's *conclusion* uses `is_derive c 1 f 0`
(typeclass-shape), MVT's *hypothesis* takes `is_derive x 1 f (df x)`
(parametric, lets you pass any `df`). The `df` argument is a function
the user supplies — `MVT` does not synthesize it.

For monotonicity on intervals there are eight named variants
`{ger0,ler0,gtr0,ltr0}_derive1_le_{cc,co,oc,oo}` (derive.v
l. 1675-1832) — pick the closure pattern matching the side conditions
you actually have.

### 42.8 Common pitfalls

1. **Forgetting that `is_derive` is directional.** `is_derive x f df`
   does not parse — the direction `v` is mandatory. On `R^o` the
   "ordinary" derivative is `is_derive x 1 f df`.

2. **Manual `apply: deriveD; apply: deriveM; ...` chains.** Reviewers
   flag these as "don't fight the typeclass." Declare a value, let
   `is_derive*` instances resolve, project with `derive_val`.

3. **Coq stdlib `Derive` / `is_derive`** (Coquelicot / `Reals`) is
   *not* mathcomp-analysis. They share the name but the carriers
   (`R` vs `realType`), the directionality, and the typeclass
   protocol all differ. `Search is_derive inside derive.` to confirm
   you are in the right namespace.

4. **`is_derive` vs `is_derive_eq` confusion.** Plain `is_derive` is
   the typeclass; `is_derive_eq` is the *rewrite-time adapter* that
   lets you produce `is_derive x v f df` from `is_derive x v f f'`
   plus a side equation `f' = df`.

5. **`apply: deriveE` to convert `'D_v` to `'d`.** Often what you
   want is the *reverse* direction — `'d f a v -> 'D_v f a` — for
   which you also use `deriveE` (it is an equation, rewritable both
   ways).

6. **Stray `derive1` outside `classical_set_scope`.** `f^`()` and
   `f^`(n)` only parse with that scope open. The `%classic` postfix
   exists for a reason.

7. **`Global Instance` declarations of *user* derivatives without a
   `Hint Mode`.** If your `is_derive` instance has a flexible head
   (e.g. `is_derive x v (myFun _) _`), declare
   `Hint Mode is_derive ! ! ! - : typeclass_instances` (cf. §36, §37.8)
   to prevent unification loops on partially-applied goals.

8. **Re-proving `derivable f x 1` when an `is_derive` instance
   exists.** `apply: ex_derive` (or just `done`, via the `Hint
   Extern` at derive.v l. 329) discharges the goal from any
   `is_derive` premise in context.

9. **Bigop derivatives by hand.** Use `is_derive_sum` (derive.v
   l. 1171) for `\sum_(i < n) h i`. The instance fires whenever each
   summand has an `is_derive` instance — no manual `big_ind2`
   induction required (cf. §34.5).

10. **`MVT` with a non-explicit `df`.** `MVT`'s second argument
    *names* the derivative function; passing
    `(fun x _ => is_derive_expR x)` (as in `exp.v` l. 488) is the
    idiom. Do not try to leave `df` as an evar.

### 42.9 Quick decision flow

```
Goal involves a derivative.

  Computing 'D_v f x or f^`() x explicitly?
    -> rewrite (derive_val (is_derive_<op> ...))
       -- or: apply: derive_val; <typeclass resolution>

  Need to *establish* derivability for downstream MVT/Rolle?
    -> apply: derivable<op>            (derivableD, derivableM, ...)
       -- or: apply: ex_derive          (from any is_derive instance)

  Goal is is_derive x v f df with df not in normal form?
    -> apply: is_derive_eq             (or: trigger_derive on R)
       -- typeclass resolves to f', side goal: f' = df

  Multivariate Fréchet derivative (linear map)?
    -> diffE / diff_comp / is_diff_comp
       (use derivable1_diffP to drop to derivable for f : R -> V)

  Chain rule on R -> R?
    -> derive1_comp     (rewrites (g \o f)^`() x)

  Need a witness in the open interval?
    -> MVT, Rolle, MVT_segment
       (supply df explicitly; use is_derive_<op> for hypotheses)

  Monotonicity from the sign of f^`()?
    -> {ger0,ler0,gtr0,ltr0}_derive1_<incr|decr|le|lt>_<cc|co|oc|oo>
```

### 42.10 Sources

`mathcomp/analysis/derive.v` (file header l. 11-44 for the naming
convention; `is_derive` class l. 249; `is_derive_eq` l. 1131;
`derive_val` projection l. 251; the instance family l. 1122, 1164,
1171, 1211, 1218, 1250, 1268, 1335, 1343, 1409; composition l. 762,
775, 2061; `MVT` l. 1614, `Rolle` l. 1584, `MVT_segment` l. 1639;
`trigger_derive` l. 2207; `derivable_within_continuous` l. 1091;
hint at l. 329); `mathcomp/analysis/exp.v` (`is_derive_expR` l. 356,
`is_derive1_ln` l. 799, `is_derive1_powR` l. 1121);
`mathcomp/analysis/trigo.v` (`is_derive_sin` l. 274,
`is_derive_cos` l. 300); `mathcomp/analysis/realfun.v` (`is_deriveV`
l. 1885, `is_derive_inverse` l. 1894, `is_derive1_sqrt` l. 1926).
The "Trick to trigger type class resolution" comment is verbatim
from derive.v l. 2206. Cross-ref §15/§35 (HB and `Hint Mode`),
§34 (`is_derive_sum` for bigop derivatives), §36 (typeclass / choice
resolution), §37 (search via `is_derive_<head_symbol>` naming
convention).

---

