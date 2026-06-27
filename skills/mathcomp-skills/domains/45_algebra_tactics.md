## 45. Algebra Tactics

The `mathcomp.algebra_tactics` package (*Reflexive
tactics for algebra, revisited*, ITP 2022) provides reflexive
decision procedures — `ring`, `field`, `lra`, `nra`, `psatz` — that
work directly on the math-comp algebraic hierarchy (`comRingType`,
`fieldType`, `realDomainType`, `realFieldType`) without `Add Ring` /
`Add Field` declarations. The companion `mathcomp.zify` package
extends Coq stdlib's `lia`/`nia` so they accept goals stated with
`nat`/`int`/`bool` and the `divn`/`modn`/`dvdn`/`gcdn`/`absz`/`Posz`
families. Reviewers consistently reject (i) hand-rolled polynomial
identities that `ring` would close in a line, (ii) `lia` on a `nat`
goal without `From mathcomp Require Import zify`, and (iii) `lra` on
a `realType` expression with a `^-1` over a possibly-zero
denominator. This section codifies the four-tactic decision tree.

### Essential lemmas (start here)

| Tactic / notation | Use it to… | § / cite |
|-------------------|------------|----------|
| `ring`, `ring: H` | close a polynomial identity `p = q :> R` | §45.2, §45.3 |
| `field`, `field: H` | close `p = q` with `^-1`; emits `_ != 0` | §45.2, §45.3 |
| `lra` | linear (in)equalities over an ordered field | §45.2, §45.4 |
| `nra` | nonlinear via Positivstellensatz (slow) | §45.2, §45.4 |
| `lia` / `nia` (after `zify`) | `nat`/`int`/`bool`, `divn`/`modn`/`dvdn` | §45.5 |
| `From … algebra_tactics Require Import ring` | shadow stdlib `ring`/`field` | §45.1, §45.9 |
| `From mathcomp Require Import zify` | enable `lia`/`nia` on mathcomp types | §45.1, §45.9 |

### 45.1 Reading the package

Two packages, four import clauses:

```coq
From mathcomp.algebra_tactics Require Import ring.   (* ring + field    *)
From mathcomp.algebra_tactics Require Import lra.    (* lra + nra + psatz *)
From mathcomp Require Import zify.                   (* zify => lia/nia *)
From mathcomp Require Import ssrZ.                   (* int <-> Z bridge  *)
```

The two `algebra_tactics` files re-bind the corresponding tactic
names (`ring.v` l. 443 / 453 for `ring` / `field`; `lra.v` l. 403 /
404 / 407 for `lra` / `nra` / `psatz`) so the math-comp versions
shadow stdlib `ring` / `field` / `lra` / `nra`. The mathcomp zify
add-on (`mathcomp/zify/zify.v`) re-exports stdlib `Lia` and registers
mathcomp-specific `Zify*Op` instances — once it is in scope, plain
`lia` / `nia` accept goals over `nat`, `int`, and `bool`. There is
no separate `lqa` / `nqa` tactic in `algebra_tactics`: rationals are
handled uniformly by `lra` / `nra` because `rat : realFieldType`.

**Naming note (mathcomp 2.5+):** the canonical HB short names for
the carrier structures are `comPzSemiRingType` and `comPzRingType`
(the `Pz` = "possibly-zero characteristic"). The legacy
`comSemiRingType` / `comRingType` are aliases and still resolve;
this section uses the legacy names for prose readability, but
either form is correct in code. The same `Pz` distinction appears
for `nmodType` / `pzNmodType`, `zmodType` / `pzZmodType`, etc.

### 45.2 The five tactics at a glance

| Tactic | Carrier (minimum) | Decides | Side conditions | Source |
|--------|-------------------|---------|-----------------|--------|
| `ring` | `comPzSemiRingType` (alias: `comSemiRingType`) — `comPzRingType` (alias: `comRingType`) when subtraction is involved | polynomial equalities `p = q :> R` | none | `ring.v` l. 443 |
| `field` | `fieldType` | rational equalities `p = q :> F` | "denominator `!= 0`"; `numFieldType` discharges integer constants | `ring.v` l. 453 |
| `lra` | `realDomainType` (no `^-1`) / `realFieldType` (with `^-1`) | linear arithmetic over total order | none (constants only) | `lra.v` l. 403 |
| `nra` | same as `lra` | nonlinear arithmetic via Positivstellensatz, complete only on small problems | none | `lra.v` l. 404 |
| `psatz n` | same as `lra` | Positivstellensatz at degree `n`; needs CSDP installed | none | `lra.v` l. 405-407 |

Reviewers' rule (algebra-tactics PR thread #94): pick the
*weakest* tactic that closes the goal. `ring` is fastest; `field`
adds the side-condition machinery; `lra` adds the order; `nra` adds
the existential search; `psatz` shells out to a SDP solver.

### 45.3 `ring` and `field`: when each fits

`ring` closes any polynomial identity over a `comRingType` /
`comSemiRingType` (or any structure that bundles one — `int`, `rat`,
`nat`, `Z`, abstract `R : comRingType`, products, polynomials). It
*does not* know about `^-1`:

```coq
(* RIGHT -- pure polynomial identity *)
Goal forall (R : comRingType) (a b : R),
    (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2%:R * a * b.
Proof. by move=> R a b; ring. Qed.

(* WRONG -- ring rejects: x^-1 is not a ring operation *)
Goal forall (F : fieldType) (x : F), x != 0 -> x * x^-1 = 1.
Proof. move=> F x x_neq0; Fail ring. Abort.

(* RIGHT -- field handles ^-1 and emits the nonzero side condition *)
Goal forall (F : fieldType) (x : F), x != 0 -> x * x^-1 = 1.
Proof. by move=> F x x_neq0; field. Qed.
```

`field` collects a single conjunction of "denominator `!= 0`"
obligations after `vm_compute`-normalising the equation. When the
field is a `numFieldType`, integer-constant denominators
(`2%:R != 0`, `n%:R != 0` for a numeral `n`) are discharged
automatically (`ring.v` l. 356-360 — the `Pcond_simpl_complete`
machinery); only abstract denominators survive. The `field: H1 H2`
form uses each `H : monomial = polynomial` as an oriented rewrite,
the same way `ring: H` does.

Hypothesis form (matches §34's bigops convention of single-rewrite
fold):

```coq
(* ring: t1 ... tn -- prove a polynomial identity modulo monomial eqs *)
Goal forall (R : comRingType) (a b : R),
    2%:R * a * b = 30%:R -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30%:R.
Proof. by move=> R a b H; ring: H. Qed.
```

### 45.4 `lra` / `nra` / `psatz`: ordered-arithmetic solvers

`lra` solves *linear* (in)equalities and equalities over a totally
ordered field (`realFieldType`) or domain (`realDomainType`):

```coq
Lemma test (F : realFieldType) (x y : F) :
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof. lra. Qed.
```

(adapted from `algebra-tactics/examples/lra_examples.v` l. 6-10).
The carrier hypothesis is *as weak as possible*: `realDomainType`
suffices when the goal contains no `^-1`; `realFieldType` is needed
once `^-1` appears (`lra.v` l. 235-237). Reviewers reject a stated
`realType` hypothesis when the proof only uses `lra` (compare §44.10
on the weakest-structure rule).

`nra` is the nonlinear extension; it searches a Positivstellensatz
witness up to a bounded degree. Useful but *expensive* and
*incomplete*:

```coq
Goal forall (F : realFieldType) (x y : F), x = 0 -> x * y = 0.
Proof. move=> *; nra. Qed.

Goal forall (F : realFieldType) (x : F), x * x >= 0.
Proof. move=> *; nra. Qed.
```

`psatz n` invokes an external SDP solver (`csdp`) at maximum search
degree `n`; without CSDP installed it falls back to `wsos_Q` (`lra.v`
l. 358). For mathcomp upstream contributions the convention is "no
`psatz`": rewrite by hand or strengthen with a lemma.

Booleans, `andb` / `orb` / `~~` / `==`, `<->`, `/\`, `\/`, and `~`
are all reified: `lra` will close a goal stated as
`(x <= 2%:R) && (x <= 4%:R)` or `~~ (x > 2%:R)` directly
(`lra_examples.v` l. 113-141). Hypotheses of arbitrary `Prop`
shape (`C : Prop`) are skipped, so `lra` can run inside a goal that
mentions non-arithmetic facts (`lra_examples.v` l. 87-91).

### 45.5 `Zify`: lifting `nat`/`int` to `Z` for `lia`/`nia`

`mathcomp.zify` registers `ZifyClasses` instances so that stdlib
`lia` / `nia` accept goals over `nat`, `int`, `bool`, `divn`,
`modn`, `dvdn`, `gcdn`, `absz`, `Posz`, `Negz`, and the
`Order.le` / `Order.lt` / `eq_op` boolean order on those types
(`zify_ssreflect.v` instance blocks throughout, l. 20-400;
`zify_algebra.v` for the algebraic `int` operations). `zify` does
**not** reify `\big[+/0]_(...)` bigops, function-typed indices, or
`'I_n` ordinals — fold or destruct those before `lia`.

```coq
From mathcomp Require Import all_ssreflect zify.

Lemma odd_add (n m : nat) : odd (m + n) = odd m (+) odd n.
Proof. lia. Qed.

Lemma dvdz_lcm_6_4 (m : int) : (6 %| m -> 4 %| m -> 12 %| m)%Z.
Proof. lia. Qed.

Lemma divzMA_ge0 (m n p : int) :
  (0 <= n)%R -> (m %/ (n * p))%Z = ((m %/ n) %/ p)%Z.
Proof. nia. Qed.
```

(from `mczify/examples/boolean.v`, `divmod.v`). The `ssrZ` add-on
(`mathcomp/zify/ssrZ.v`) provides the `Z`/`int` bridge needed when
the goal mixes both — rare in mathcomp code, common when interfacing
with VST or stdlib `ZArith`.

What `zify` does *not* cover: `rat` (use `lra` instead, `rat` is a
`realFieldType`), `realType`, `R : ringType` for abstract `R`, and
finite types `'I_n`. For `ordinal` arithmetic, lift through
`val : 'I_n -> nat` first and then `lia` (compare §40.7 on
cardinality lemmas).

### 45.6 Workflow patterns

```
Goal head is `_ = _` or `_ != _` (no order).

  Carrier is a comRingType / comSemiRingType (no `^-1`)?
    -> ring                                      (45.3)
  Carrier is a fieldType, has `^-1`?
    -> field                                     (45.3)
    -> remaining "denominator != 0" obligations:
         try lra | rewrite ... | hand off

Goal head is `_ <= _`, `_ < _`, `_ >= _`, `_ > _`,
or a Boolean / Prop combination thereof.

  Carrier is realDomainType / realFieldType?
    Linear in the unknowns?            -> lra
    Otherwise (nonlinear)?             -> nra (slow, incomplete)
    Need an SDP certificate?           -> psatz n  (requires CSDP)

  Carrier is nat / int / bool?
    From mathcomp Require Import zify.
    -> lia / nia
    Goal includes divn / modn / dvdn?  -> lia (zify reifies these)
    Nonlinear over ints?               -> nia

  Carrier is rat?
    rat : realFieldType                -> lra / nra
    rat as a Q-coefficient?            -> ratr ... ; lra  (45.4)

  Carrier is an abstract ringType (not com)?
    -> no decision procedure: rewrite by hand or strengthen
       the hypothesis to comRingType.
```

### 45.7 Side conditions and preprocessing

`field` emits its denominator-nonzero obligation as a conjunction
that is automatically split (`ring.v` l. 356-360). Each conjunct is
then either (a) discharged by the `Pcond_simpl_complete` pass
(integer-constant denominators in a `numFieldType`), or (b) left for
the caller. Two idioms close the residual:

```coq
(* RIGHT -- nontrivial denominator, discharged by hand *)
Goal forall (F : numFieldType) (n : nat),
  n != 1%N -> ((n ^ 2)%:R - 1) / (n%:R - 1) = (n%:R + 1) :> F.
Proof.
by move=> F n n_neq1; field; rewrite subr_eq0 pnatr_eq1.
Qed.

(* RIGHT -- when the denominator condition is itself linear over R *)
Goal forall (F : realFieldType) (x : F), 1 < x -> x / (x - 1) > 0.
Proof. by move=> F x hx; rewrite divr_gt0 // ?subr_gt0 //; lra. Qed.
```

(field example adapted from `field_examples.v` l. 49-51.) Mathcomp
algebra-tactics does **not** export stdlib's `ring_simplify` /
`field_simplify` / `lra_simplify`: the package is a closed
"prove-or-fail" set of tactics, not a normalisation toolkit. To
preprocess, use `rewrite` with the polynomial-identity lemmas in
`ssralg.v` (`mulrDl`, `mulrDr`, `expr2`, `mulrA`, etc.) or fall back
to `ring`'s own `ring: H1 H2` form, which folds the rewriting and
the closing into one step.

### 45.8 Failure modes

1. **`Tactic failure: ... is not a polynomial`** — the goal contains
   a non-reified head symbol. Common offenders: `Num.norm` (`` `|x| ``),
   `Num.sqrt`, `expR`, `sin`/`cos`. Reduce them before `ring` /
   `lra`. For `Num.norm` over a `realDomainType`, case-split on
   sign (`ger0_norm` / `ler0_norm`).
2. **`lra` reports "no certificate"** on what looks like a linear
   goal — typically a hypothesis is an *equation* on a non-linear
   subterm (`x * y = 0`) that the user expected `lra` to use
   linearly. Promote to `nra`.
3. **`field` succeeds but leaves a hard `_ != 0` obligation** — the
   denominator depends on a section variable `R : fieldType`
   without an order. If the caller can refine to `numFieldType`,
   `field` itself absorbs integer-constant nonzero conditions; if
   not, the only escape is `apply: contra (...) => ...` plus a
   manual proof.
4. **Performance cliff on `nra`** — the search is exponential in
   the degree bound. A goal that takes 20s with `nra` usually has
   a Positivstellensatz proof at low degree; refactor to expose it
   (e.g. complete the square *by hand*, then `lra`).
5. **`lia` fails on `'I_n`** — `zify` does not reify ordinals.
   `case: i => i hi` to expose the underlying `nat` and the bound,
   then `lia`.
6. **`ring` on a `seq T` or any non-ring** — error
   `"Unable to unify ... with comSemiRingType"`. This is the §35
   forgetful-inheritance trap: a `Definition X := T.` over a
   `comRingType` *breaks* the canonical structure. Use `Notation`
   or `HB.instance Definition _ := X.copy ...`.

### 45.9 Common pitfalls

1. **Forgetting the import.** `From mathcomp.algebra_tactics
   Require Import ring.` shadows stdlib `ring` with the math-comp
   one; without it, `ring` falls back to stdlib's, which does not
   know `Posz` / `_%:R` / `_%:~R` and rejects most mathcomp goals.
2. **`lia` on `nat` without `From mathcomp Require Import zify`.**
   Stdlib `lia` accepts `nat` natively, but it does *not* know
   `divn` / `modn` / `dvdn` / `\big[addn/0]_...` constants /
   `Order.le` over `nat`. Reviewers reject hand-rolled bool-to-Prop
   reflections that `zify` would close.
3. **`Posz_inj` does not exist (cf. §41.7).** Inside `lia`, this is
   moot — `zify` reifies `Posz n` as `Z.of_nat n`. Outside,
   `case`/`congr` are the right tools.
4. **Calling `field` when the goal has only `+` / `*` / `-` / `^+`.**
   `field` works, but it does extra normalization and emits a
   trivially-`true` side condition. Use `ring` — same answer,
   faster, no obligation.
5. **`lra` on `realType` lemmas reused at `R := rat` confused with
   `R := R` (the analysis real).** `rat` is `realFieldType`
   (decidable, countable); the analysis `realType` is uncountable.
   Both satisfy `lra`'s signature, so the tactic works on either —
   but the *lemma signature* may force `realType`, in which case
   you must `apply: ratr_inj` or move to `R : realType` in the
   statement.
6. **`field` after a `set y := _` that hides the denominator.**
   The reflective preprocessor sees `y`, not the original
   expression, and so does not know `y != 0`. Either avoid `set`
   on a denominator, or pass the equation to `field: H` so the
   rewriting fires after reification.
7. **`nra` as a first-line tactic.** Reviewers (on the
   algebra-tactics tracker) ask: *try `lra` first*. A goal that
   was secretly linear should not be closed with the heavier
   tactic, both for performance and for proof readability.
8. **Mixing `Z` (stdlib) and `int` (mathcomp) in the same goal.**
   `lia` after `zify` works on either, but reviewers (cf. §41.7)
   prefer mathcomp-pure goals. If you need both, `ssrZ.v` provides
   `int_of_Z` / `Z_of_int` and the relevant cancellation lemmas.

### 45.10 Quick decision flow

```
What does the goal say?

  p = q  (no order, no inverse)              -> ring
  p = q  with `^-1` over a fieldType         -> field
                                                discharge `_ != 0`
  p R q  (R is <=, <, =, !=, /\, \/, ~, ==)
    over a realDomainType / realFieldType
      linear?                                -> lra
      nonlinear?                             -> nra
      nonlinear, need SDP certificate?       -> psatz n
    over nat / int / bool
      From mathcomp Require Import zify.
        linear?                              -> lia
        nonlinear?                           -> nia

What is the import line?

  ring + field                               From mathcomp.algebra_tactics
                                             Require Import ring.
  lra + nra + psatz                          From mathcomp.algebra_tactics
                                             Require Import lra.
  lia / nia on nat / int / bool              From mathcomp Require Import zify.
  Z <-> int bridge                           From mathcomp Require Import ssrZ.

Is the carrier hypothesis the weakest one?

  ring    <- comSemiRingType (or comRingType for subtraction)
  field   <- fieldType (numFieldType to drop integer obligations)
  lra     <- realDomainType (no ^-1) | realFieldType (with ^-1)
  nra     <- same as lra
  lia     <- after `Require Import zify`, no further structure
```

### 45.11 Sources

- `mathcomp/algebra_tactics/ring.v` (`ring` tactic l. 443; `field`
  tactic l. 453; `field_normalization` l. 368; `Pcond_simpl_complete`
  call site l. 356-360; ring/field reflection lemmas l. 405-430;
  Elpi entry points l. 439-451).
- `mathcomp/algebra_tactics/lra.v` (`lra` l. 403, `nra` l. 404,
  `psatz` l. 405-407; `RTautoChecker_sound` l. 136 / `realDomainType`
  branch (`Section RealDomain`, `Variable R : realDomainType` at
  l. 114-116); `FTautoChecker_sound` l. 245 / `realFieldType` branch
  (`Section RealField`, `Variable F : realFieldType` at l. 235-237);
  preprocessor `Lra.Rnorm` l. 180; witness Ltac l. 355-358).
- `mathcomp/algebra_tactics/ring.v` (`target_comSemiRing` Variant
  l. 32, `target_comSemiRingType` l. 37, `target_comRing` l. 52,
  `target_comRingType` l. 57 — these wrap `int`/`Z`/`nat`/`N` as
  a com(Semi)Ring for morphism normalisation).
- `mathcomp/algebra_tactics/common.v` (RExpr / Reval reflexive
  layer l. 252-298 — the term-reflection plumbing shared between
  `ring` and `lra`).
- `mathcomp/zify/zify_ssreflect.v` (Zify hooks l. 13, 430;
  `Op_nat_inj` l. 25; ssrbool / ssrnat / div / order
  instances l. 32-400).
- `mathcomp/zify/zify_algebra.v` and `mathcomp/zify/zify.v`
  (re-exports `Lia`, registers `int` / `Posz` / `Negz` / `absz` /
  `intdiv` instances).
- `mathcomp/zify/ssrZ.v` (`Z_of_int`, `int_of_Z`, mutual
  cancellation lemmas).
- algebra-tactics package, examples directory:
  `examples/ring_examples.v`, `examples/field_examples.v`,
  `examples/lra_examples.v`, `examples/from_sander.v`.
- mczify package, `examples/boolean.v` (one-liner `lia`),
  `examples/divmod.v` (`dvdz_lcm_6_4`, `divzMA_ge0`),
  `examples/zagier.v` (case-split + `lia`).
- *Reflexive tactics for algebra, revisited*,
  ITP 2022 (LIPIcs vol. 237). algebra-tactics
  README §"The `lra`, `nra`, and `psatz` tactics" notes that these
  three are *experimental* and subject to change.
- Coq stdlib `Stdlib.micromega.Lqa` (l. 52-53 — the rational
  `psatz`); algebra-tactics' `lra` subsumes it for `rat` because
  `rat : realFieldType`, so `lqa` does not appear in mathcomp code.
- §11 (the `n` / `z` / `q` carrier-suffix convention),
  §34 (bigops — `ring` plays the same role for polynomial
  identities that `big_morph` plays for sums),
  §35 (forgetful inheritance — bare `Definition` over a `ringType`
  breaks `ring`/`field`/`lra` instance resolution exactly as it
  breaks `nbhs`),
  §36 (weakest-structure rule — `realDomainType` over `realFieldType`
  over `realType` whenever each suffices),
  §41 (`int` / `rat` — the carrier types most often combined with
  `zify` and `lra`),
  §44.10 #5 (the `realType`-overuse anti-pattern).

---

