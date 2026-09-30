# Errors — Rocq / coqc message → cause → mathcomp fix

> A lookup table from the **error message you see** to its **likely
> cause** and a **concrete ssreflect/mathcomp fix**. This is the
> reusable debugging asset: when `coqc` (or `rocq_compile_file`) prints
> something, find the row, apply the fix, re-check.
>
> Read-only guidance. It tells *you* what to try; it does not auto-fix.
> Seeded from `reference.md` §35.10 (HB/canonical-structure errors) and
> expanded with the unification, rewrite, application, scope,
> universe, bookkeeping, definition-time and warning / Qed-time
> families.

## How to use this file

1. Match the error to a **family** (section heading) by its keyword:
   *infer placeholder*, *unify*, *not a subterm*, *illegal
   application*, *scope / notation*, *HB / universe*, *used in
   hypothesis / pattern not instantiated* (§7), *ill-formed / non
   exhaustive / positive* (§8), *Warning / deprecated / incomplete
   proof* (§9).
2. Read the row: **message (abbreviated) → likely cause → fix →
   cross-ref** (§9 warnings: **warning → benign? → action → ref**).
3. Follow the `(§N)` for the full rule (`N ≤ 37` or `N = 48` →
   `reference.md`; `38 ≤ N ≤ 47` or `N = 49` →
   `domains/<N>_<topic>.md`; `templates.md §k` spelled out).

When rocq-mcp is available, `rocq_compile_file` returns a structured
`errors` list plus a reusable `state_id` + goals at the error position
— inspect that state (read the goal, `rocq_query` the offending symbol)
before editing. All idioms below are current mathcomp 2.5 /
analysis 1.16.

A general first move for *any* inference/unification failure: turn on
implicits to see what Rocq actually wrote (more inspection commands:
§37.12).

```coq
Set Printing All.            (* or: Set Printing Coercions. *)
About <symbol>.  Check <term>.  Locate "<notation>".
```

---

## 1. "Cannot infer this placeholder" / canonical-structure / HB

The unifier could not fill a `_` — usually a **missing instance** so
the canonical-structure / HB resolution found nothing to plug in.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Cannot infer this placeholder of type "T"` | No canonical instance makes the carrier a `<Struct>Type` | Declare the missing `HB.instance Definition _ := …Build T …` *before* the use site; confirm with `HB.about T` / `HB.howto T <Struct>` | §15, §35.7 |
| `Cannot infer the implicit parameter X` | Implicit not determined by the explicit args; structure not in scope | Make the arg explicit at the call, or supply `(T : X)` / `[the X of T : Type]` / `@lemma` (plain `[the X of T]` fails for `T : Set` and for structure variables, §48); or `Import` the module providing the instance (import order) | §3, §24.1, §25.2 |
| `Could not unify "Foo X" and "Bar Y"` inside `HB.instance` | Missing **parent** instance for the carrier | Provide the parent instance first, or pick the factory whose `of`-context matches what is already declared | §15, §35.1 |
| `ambiguous canonical projection` | A diamond is unresolved at the join | Add an explicit combined `HB.instance Definition _ : <Mixin> … := …`; if a parent was enriched after descendants, `HB.saturate` | §35.4, §35.7 |
| `abbreviation "Foo.Build" is not applied enough` | A factory/mixin `Build` needs more positional `of`-context args | `HB.about Foo` / `Print Foo.Build` to see the arity; supply the `of`-context explicitly when invoked outside a builders block | §15, §35.2 |
| `The term "x" has type "T" while it is expected to have type "Equality.sort ?s"` (other `<Struct>.sort ?s`: decoder below) | `T` has no canonical instance of that structure: never declared, declared after the use, or in a module not imported (MCB §6.3) | `HB.about T` (`HB: uninteresting constant` = no instance at all), `HB.howto T eqType`; then declare it: `hasDecEq.Build T eqTP` (`eqTP : Equality.axiom eqT`, not the library `eqP`), `Equality.copy T (pcan_type fK)`, or `[Equality of T by <:]` on a sub-type | §36.12, §36.13 |
| `Cannot infer the implicit parameter pT of mem whose type is "predType T"`; element also unannotated: `… T of in_mem whose type is "Type"` | The right side of `\in` (or the element) has an uninferred type, e.g. an unannotated `Lemma` binder | Annotate the binder: `(s : seq T)`, `(A : {set T})`, `(x : T)` | §24.5, §49.6 |
| `The term "T" has type "Set" while it is expected to have type "pred_sort ?pT"` on `#\|T\|` / `x \in T` | `T` is a plain `Inductive`, not a `predArgType`, so it cannot stand for "all of `T`". A finType instance does not help: the error persists after `Finite.copy` (MCB §8.5) | At the use site: `#\|{: T}\|`, `x \in [set: T]`, `x \in {: T}`. When you own the declaration: `Inductive T : predArgType := …` (as `ordinal`). Never add a coercion by hand. The same message on `x \in s` with `s : seq T` means `T` has no eqType (row above) | §36.12 |
| `Found type "T" where "Finite.sort ?T" was expected` on `\sum_(x : T)`; `"Phant (nat -> nat)" … expected … "phant (forall x : ?aT, ?rT x)"` on `{ffun nat -> _}`; `mem {: T} has type mem_pred T while … expected mem_pred (Finite.sort ?T)` | The index/domain type has no finType instance (`nat`, or a fresh inductive) (MCB §7.5) | Index by a finite type: `'I_n`, or `{: T}` once `T` has `Finite.copy T (can_type fK)`; over `nat` use `\sum_(i < n)` or `\sum_(i <- s)` | §36.12, §47 |
| `Definition illtyped: … has type "Equality.axioms_ <known>" while it is expected to have type "Equality.axioms_ T"` on `Equality.copy T (can_type fK)` | The cancel lemma goes the wrong way: in `fK : cancel f g`, `f` must map the **new** type `T` into the known eqType | Prove `cancel f g` with `f : T -> known` (for a constructor `C : S -> T`: `cancel unC C`, not `cancel C unC`); `pcan_type` for a partial inverse | §36.12 |
| `non forgetful inheritance detected` then `HB: no new instance is generated` after `CanIsFinite fK` / `PCanIsFinite fK`; on a fresh type instead `Definition illtyped: … expected to have type "@cancel (Finite.sort ?t0) (Countable.sort ?t) ?s ?s0"` | On a fresh type they are ill-typed (they need a countType). Unascribed, HB types the instance on `Countable.sort _`, not on `T`, so nothing is added and `#\|{: T}\|` still fails | One line: `HB.instance Definition _ := Finite.copy T (can_type fK).` (`pcan_type` for `pcancel`); it registers eq/choice/count/fin at once. Its `redundant-canonical-projection` warnings are harmless (this file's §9). On a type that is already a countType, `HB.instance Definition _ : isFinite T := CanIsFinite fK.` also works (finmap.v:2275, qpoly.v:130) | §36.12 |
| `HB: no new instance is generated` `[HB.no-new-instance]` after `HB.instance Definition _ := isFinite.Build T eP`, then `mem {: T} … expected mem_pred (Finite.sort ?T)` on `#\|{: T}\|` | `isFinite` needs a countType; `T` is only an eqType, so no finType instance is created | One line: `HB.instance Definition _ := Finite.copy T (fin_type eP).`; or copy `Countable` first (`Countable.copy T (pcan_type fK)`) | §36.12 |
| `The term "id_phant" has type "phantom Type T -> phantom Type T" while it is expected to have type "unify Type Type T ?cT nomsg"` on `X.clone T _` | No `X` instance on `T` (for `lmodType R`-style clones: on the scalar ring `R`) (MCB §8.4) | `HB.about T`, then declare the instance. Never hand-write `phant` / `phant_id` / `Phant` arguments | §35.7, §36.12 |
| `s : finType The term "s" has type "finType" while it is expected to have type "Set"` on `[the finType of T]` | **Not** a missing instance: the notation needs `T : Type` literally, and here `T : Set` (every plain inductive, `nat`, `bool`, `seq nat`); a section variable `T : finType` fails the same way (`… "eqType" while … expected … "finType"` for `[the eqType of T]`). It fails even when the instance exists | Write `(T : finType)` or `[the finType of T : Type]`. With `: Type`, a real missing instance shows as `TheCanonical.put … (Finite.sort ?s0) …` | §24.1, §48 |

**Decoding `<Struct>.sort ?s` in the expected type** (mathcomp 2.5 names):

| Expected type mentions | Asked by | Missing |
|---|---|---|
| `Equality.sort ?s` | `==`, `eq_op` | eqType |
| `Finite.sort ?T` | `[set _]`, `\sum_(x : T)`, `#\|{: T}\|` | finType |
| `Order.Preorder.sort ?s` | `<=%O`, `<%O` | preorderType (or above) |
| `Algebra.BaseAddMagma.sort ?s` | `+` in `ring_scope` | nmodType / zmodType |
| `Algebra.BaseZmodule.sort ?s` | unary `-` | zmodType |
| `GRing.PzSemiRing.sort ?s` | `*` | pzSemiRingType (or above) |
| `<Struct>.sort R` (no `?`), e.g. `Algebra.BaseAddMagma.sort R`, `GRing.PzSemiRing.sort R` | an argument next to an `R` value | nothing: the *argument* is mistyped (§2 below) |
| `pred_sort ?pT` | `#\|T\|`, `x \in T` | nothing: `T` is not a `predArgType` |
| `pred_sort ?pT` on `s : seq T` | `x \in s` | eqType on `T` |

What to check, in order, when a placeholder won't infer:

1. Is the instance **declared** at all? `HB.about T`. If not, build it
   (§15). If yes but unreachable, check **import order** (§3) — the
   `HB.instance` lives in a module you forgot to `Import`.
2. Is a **parent** missing? `HB.howto T <Struct>` prints the factory
   chain that closes the gap (§35.7). (With `all_algebra` loaded,
   `HB.howto` fails with `… isDuallyPreorder.axioms_ is not a factory …`:
   a mathcomp 2.5 / HB limitation, not your code; use `HB.about T` and
   §36.12.)
3. Is it a **diamond**? `ambiguous canonical projection` ⇒ add the
   explicit join (§35.4).
4. Only as a last resort, annotate with `(T : X)` or
   `[the X of T : Type]` (§24.1, §48; plain `[the X of T]` fails for
   `T : Set` such as `nat`, even with the instance) — and
   delete it again once the instance is in place; the annotation is
   noise when resolution works (§24.1, §22.4).

---

## 2. "Unable to unify "X" with "Y""

The two sides are *almost* the same — the mismatch is usually a
**display / scope** difference or an **implicit-argument** difference,
not a real type error. `Set Printing All` makes it visible.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Unable to unify "x%R" with "x%:E"` (or `…%E`) | Ring vs extended-real scope: an `R` value where an `\bar R` is expected (or vice versa) | Insert / drop the coercion: `x%:E` to lift `R`→`\bar R`; keep one scope open and let `%:E` mark the boundary (don't sprinkle `%R`/`%E`) | §6.2, §19, §22.3 |
| `Unable to unify` where the terms print identically | Hidden implicit / display arg differs | `Set Printing All`; pin the differing implicit (`@lemma …` or `(x : R)`), or pass the display as `_` rather than a named display | §24.4, §25.2 |
| `Unable to unify` after a `rewrite` | The lemma's LHS instantiates a *different* occurrence than intended | Pin the spot with `[in RHS]` / `[LHS]` / `[in X in _]` (see §3 below) | §29.2 |
| `Unable to unify "0" with "0%:R"` (numerals) | A literal `0`/`1` parsed in the wrong scope | Disambiguate with `0 :> R` (the one annotation §24.5 keeps), or open the right `ring_scope` locally | §24.5, §6 |
| `The term "t" has type "T1" while it is expected to have type "T2"` | An argument of the wrong type. `T2` often prints as a projection: `<Struct>.sort R` / `Equality.sort T` = the carrier of `R` / `T` (MCB §6.4) | Classify by `T1`/`T2` with the four rows below; if both print identically, use the `Set Printing All` row above | §37.12 |
| `… has type "nat" while … expected … "Algebra.BaseAddMagma.sort R"` (any `<Struct>.sort R`; or `int`, `\bar R`) | A `nat` where a ring element is expected; no implicit cast is inserted | Insert the cast: `n%:R`, `n%:Z` (`Posz`), `x%:E` for `\bar R` | §41.1, §19 |
| `… has type "Prop" while … expected … "bool"` | A `Prop` used as a `bool`; the coercion only goes `bool` → `Prop` (`is_true`) | Use a reflect view (`/andP`, `/eqP`) or `` `[< P >] `` (analysis `boolp`) | §36.4, §36.7 |
| `… has type "nat" while … expected … "is_true (?m <= ?n)"` (e.g. `leq_trans m n`) | Wrong argument order or count: an index passed where a hypothesis is expected | `About lem` to see which arguments are implicit; pass the hypotheses only (`leq_trans lemn lenp`), or `@lem` for all | §37.12, §31 |
| `… has type "{set T}" while … expected … "seq ?T"` | A wrapped value where the underlying type is expected | `enum A` for a set as a seq; `val x` for a sub-type element | §36.13 |
| `In environment b : Type … The term "b" has type "Type" while it is expected to have type "bool"` on a `Lemma` statement | An unannotated binder first used as `b -> …` is elaborated as a sort | Annotate `(b : bool)`, or `Implicit Types b : bool.` in the section | §16, §24.5 |

Rule of thumb: if the two terms *look* identical, it is implicits or
scope (§24.4); if they look different in a `%R`/`%E`/`%:E` way, it is
the ereal boundary (§19).

---

## 3. "not a subterm of the goal" (failed `rewrite`)

The rewrite pattern did not match where you expected — either the
**occurrence** is wrong, or the term lives **under a binder** the bare
`rewrite` can't reach.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `The LHS of … is not a subterm of the goal` | Pattern matches a *different* occurrence, or none | Pin the location: `rewrite [in RHS]L`, `rewrite [LHS]L`, `rewrite [in X in _ + X]L` | §29.2 |
| `not a subterm` on a `\sum` / `\prod` / `\int` / `lim` | The redex is **under a binder**; bare `rewrite` won't enter it | Use `under eq_bigr => i Pi do rewrite L` (or `eq_integral` / `eq_cvg`); close with `over.` if no `do` | §29.1, §34.3, §43.6 |
| `rewrite … found nothing` / `nothing to rewrite` | Wrong direction, or the redex is already gone | Try `-L`, pin the occurrence, or inspect the goal. Do **not** add `?` to hide the failure: that moves the breakage to a later line (§29.3). Never use `inE` with `-` | §29.3, §29.4 |
| `not a subterm` after `Set`-rewriting by hand | Hand-rolled set equality | Prefer `rewrite predeqE` for `setX = setY`, or `apply/seteqP; split=> x` | §29.5, templates.md §9 |
| `The LHS of L (…) does not match any subterm of the goal` although the goal equals the LHS by computation | `rewrite` matches the head symbol literally (keyed matching); here the head is hidden behind a definition (`dbl n` for `n + n`) (MCB §2.4.1) | Expose it: `rewrite -[dbl n]/(n + n) L` or `rewrite /dbl L`; or `exact: L` / `apply: L`, which unify up to conversion; `Set Printing All` shows the real head | §29.2, §29.8 |
| `The LHS of IHm (m + 0) does not match any subterm of the goal` after `elim: m => [\|m IHm] //=` | `/=` does not unfold `addn` (`simpl never`); the goal is still `m.+1 + 0 = m.+1` | Move the successor out first: `rewrite addSn IHm` | §49.4, templates.md §21 |
| `The LHS of addnC (_ + _) does not match any subterm` right after `big_cat` / `big_split` / `bigID`; the goal shows `ssrnat_addn__canonical__Monoid_Law …` | The monoid-law projection was not reduced back to `addn` (MCB §6.9); the rewrite failure itself is mathcomp 2.5 behaviour, not from the book | `/=` right after the bigop rewrite (`rewrite big_cat /= addnC`), or pin the occurrence: `rewrite [LHS]addnC` | §34.8 |
| `The LHS of size_tuple (size _) does not match any subterm` on `size (op t)` | `op` has no canonical tuple instance: `Check [tuple of op t]` fails (MCB §7.1) | Rewrite with the `size_<op>` lemma first, or declare `Lemma op_tupleP n (t : n.-tuple T) : size (op t) == n.` and `Canonical op_tuple n t := Tuple (op_tupleP n t).` | §46.2 |
| `Dependent type error in rewrite of (fun _pattern_value_ => …)` … `should be a subtype of "'M_(_pattern_value_, n)"` when rewriting a size index (`rewrite addn0` with `A : 'M_(m + 0, n)`) | The size lives in the *type* of `A`; abstracting it is ill-typed. The uncast statement `row_mx A1 (row_mx A2 A3) = row_mx (row_mx A1 A2) A3` fails earlier: `has type "'M_(m, n1 + n2 + n3)" while … expected "'M_(m, n1 + (n2 + n3))"` (MCB §7.8.3) | Never rewrite the index: state with `castmx (erefl m, esym (addnA n1 n2 n3))` (as `row_mxA` does); prove entrywise with `apply/matrixP => i j; rewrite castmxE !mxE` | §38.10 |

Keyed matching vs conversion, and the two `simpl`-related failures:

```coq
From mathcomp Require Import all_boot.

Definition dbl n := n + n.

Lemma dbl_ex n : dbl n = n.*2.
Proof.
Fail rewrite addnn.                 (* head is dbl, not addn *)
by rewrite -[dbl n]/(n + n) addnn.  (* or: exact: addnn *)
Qed.

Lemma addn0' m : m + 0 = m.
Proof.
elim: m => [|m IHm] //=.
Fail rewrite IHm.                   (* goal: m.+1 + 0 = m.+1 *)
by rewrite addSn IHm.
Qed.

Lemma sum_catC (s1 s2 : seq nat) F :
  \sum_(i <- s1 ++ s2) F i = \sum_(i <- s2 ++ s1) F i.
Proof.
rewrite big_cat.
Fail rewrite addnC.                 (* goal: ssrnat_addn__canonical__... *)
by rewrite /= addnC -big_cat.       (* or: rewrite [LHS]addnC -big_cat *)
Qed.
```

If the redex appears several times and you want one of them, *always*
pin with a pattern rather than relying on default selection — explicit
patterns also document intent and parse faster (§29.2).

---

## 4. "Illegal application (Non-functional construction)"

You applied something that is **not a function** to an argument —
typically an **over- or under-applied** term, or a **missing
coercion** so a structure was used where its carrier was meant.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Illegal application (Non-functional construction)` | Term over-applied: extra argument past its arity | `About f` / `Check f` to see the real arity; drop the surplus arg | §16, §31 |
| `Illegal application … expected N arguments` | Under-applied lemma fed to `apply:`/`exact:` | Supply the missing args, or let `apply:` unify them (often the explicit args are useless — §22.2) | §22.2, §26.2 |
| `… is not a function; it cannot be applied` | A structure used where its **carrier** (the coercion target) was meant | Rely on the coercion (write `T`, not `[the … of T]`); if the coercion is missing on a legacy export, add it | §35.10 (Coercion), §24.1 |
| `Non-functional construction` after `@` | `@` forced *all* args explicit, mis-counting the `of`-context | Drop `@` and let HB infer the `of`-context positions; keep `@` only where one position is truly ambiguous | §25.1, §35.11 |

---

## 5. Scope / notation: "Unknown interpretation", "not found in scope"

A notation didn't parse, or printed back oddly, because the **scope**
isn't open or the **module** providing it isn't imported.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Unknown interpretation for notation "…"` | The notation's scope is not open here | Add the matching `Local Open Scope` (e.g. `ring_scope`, `ereal_scope`, `classical_set_scope`); never plain `Open Scope` | §6 |
| `The reference X was not found in the current environment` | The module defining `X` is not imported | `From mathcomp Require Import <module>` in the correct group/order; avoid path-qualified names like `mathcomp.classical` | §3, §23 |
| `Syntax error` / notation parses wrong | Scope precedence or ordering changed a parse tree | Restore the established scope ordering; tweak `Bind Scope` / precedence only with care and a full re-test | §6.2, §6.3 |
| `X is not a head symbol` / `Search` returns nothing | Wrong scope ⇒ wrong head symbol in your query | Open the scope first; then `Search` by the head symbol of the LHS | §6, §37.2 |
| convergence notation prints unexpanded / won't parse | Missing the bundled `--> ` import or wrong scope | Import the `topology` / `normedtype` layer; use the bundled `_ --> _` form, not hand-unfolded filters | §3, §23.4, §30.6 |

Diagnostic: `Locate "notation".` shows which scope a notation lives in;
`Print Scopes.` lists what is open. If a name resolves only when
fully-qualified, the real fix is an `Import` (§23), not the qualifier.

---

## 6. HB `_subproof` / anomaly / "Universe inconsistency"

Lower-frequency, higher-confusion. Usually a structural problem, not a
typo — read where it points before editing.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Anomaly … HB …` / error citing a `_subproof` / `_mixin_` name | HB elaboration failed on a generated obligation | Re-run the `HB.instance` with `#[verbose]` (or `#[log]`) to see what HB elaborated; usually a missing parent or a wrong `Build` arity upstream | §35.2, §35.7 |
| `Universe inconsistency … cannot enforce …` | A definition forced a universe ordering that clashes (often `Type`-level data stored where `Prop` / a lower universe was expected) | Lower the offending field's universe (store `bool`/`Prop` content, not `Type`); avoid packing large `Type`s into a mixin; sometimes an explicit `: Type@{i}` annotation, but prefer restructuring | §36.7, §35.1 |
| `HB.howto` finds no chain / "missing instance" though mixins present | A join was declared after its descendants and not recomputed | `HB.saturate.` (use sparingly — slow), or add the explicit join `HB.instance` | §35.7, §35.11 |
| reviewer flag: "this breaks forgetful inheritance" | A `Definition` aliased an HB-equipped type | Replace the alias by `Notation`, wrap in a `Module`, or use `<Struct>.copy` | §35.5, §35.10 |
| `… is not applied enough` from a builders block | A reusable lemma was put *inside* `HB.builders` (anonymous, uncallable) | Factor the lemma out *before* `HB.builders` and call it from inside | §35.11 |

For HB specifically: `HB.about <name>` (what's attached + where),
`HB.locate <name>` (which file generated a synthesized constant), and
`HB.graph "out.dot"` (visualize missing joins) localize the problem
fast (§35.7).

---

## 7. ssreflect bookkeeping: case / elim / generalization / clears

The lemma is fine; a `:` push, an intro pattern or a clear does not fit
the goal stack (`:` pushes onto the goal, `=>` pops) (MCB §4.1).

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `y is used in hypothesis odd_y.` on `move: y` / `case: y` / `elim: y` | A context hypothesis mentions `y`, so `y` cannot be generalized alone | Push it too, variable first: `case: y odd_y`; or clear it: `case: y {odd_y}` | §27.10 |
| `Pattern (leP _ _) was not completely instantiated and one of its variables occurs in the type of another non-instantiated pattern variable` | Spec lemma whose indices the goal does not determine: Order's `leP` on a nat goal (it shadows `ssrnat.leP` under `Import Order.TTheory`), or `insubP` when `insub x` is not in the goal | nat: `case: leqP` / `case: (leqP m n)`; sub-type: `case: (@insubP _ _ S x)` | §28.1, §36.13 |
| `The variable IHm was not found in the current environment` on `elim: m IHm` | Names after `:` are **pushed** (must already exist), not bound | `elim: m => [\|m IHm]` | templates.md §21 |
| `No assumption in (…)` on `move=> {}h` | `{}h` pops the goal's first premise and reuses the name `h`; the goal has no premise | Clear: `move=> {h}`; refine in place: `have {}h : … by …` | §27.11 |
| `Syntax error: '*' or [ssrrwargs] or [oriented_rewriter] expected after 'rewrite'` on `rewrite: h` | Not ssreflect syntax | Rewrite then clear: `rewrite {}h` | §27.11 |

```coq
From mathcomp Require Import all_boot.

Lemma push y (odd_y : odd y) : 0 < y.
Proof.
Fail case: y.          (* y is used in hypothesis odd_y. *)
by case: y odd_y.      (* variable first, then the hypotheses on it *)
Qed.

Lemma cl a b (E : a = b) : a + 0 = b.
Proof.
Fail move=> {}E.       (* No assumption in (a + 0 = b) *)
(* rewrite: E.            Syntax error: ... expected after 'rewrite' *)
by rewrite {}E addn0.  (* rewrite with E, then clear it *)
Qed.

Lemma pin m : m <= maxn m m.+1.
Proof.
(* case: leqP.  splits on `m <= maxn m m.+1` itself: the wrong subterm *)
by case: (leqP m m.+1).
Qed.
```

**Silent failures (no message, wrong result).**

- A bare `case: specP` splits on the **first** subterm matching the
  spec's indices. The branches then show `-> true` / `-> false` on the
  wrong term. Pass the arguments: `case: (leqP m n)` (§28.1, MCB §5.2.1).
- `case: leqP` leaves a context hypothesis `h : a <= b` untouched. Push
  it first: `move: h; case: leqP` or `case: leqP h` (§28.1).
- Bullets do not check that the previous branch is closed (mathcomp sets
  Bullet Behavior "None"). The next bullet silently works on the leftover
  goal, and the error surfaces later, often only at `Qed`. End every
  branch with `by`/`done` (§26.5, §9 below).
- `;` after a conditional rewrite also runs on its side goals
  (`rewrite subnK; tac` runs `tac` on `m <= n` too; MCB §2.3.3,
  footnote 2). Under `Unset SsrOldRewriteGoalsOrder` the side goal
  comes **first** (not from the book, whose MCB §2.4 puts the main goal
  first), so `first`/`last` after the rewrite target the other goal
  (§27.9; reordering with `first`/`last`: MCB §2.2.2).

---

## 8. Definition-time errors: `Fixpoint` / `match` / positivity

Raised by `Fixpoint` / `Definition` / `Inductive`, not by a tactic:
the §3 rewrite fixes do not apply. Redesign the definition; never bypass
the check (MCB §1.2.2-§1.2.3, §3.5, §3.7).

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Recursive definition of f is ill-formed. … Recursive call to f has principal argument equal to "n.-1" instead of a subterm of "n".` | The recursive call is not on a strict syntactic subterm of the matched argument (`n.-1`, `n - 1`, `n./2`, `n` itself) | Recurse on the pattern variable: `if n is p.+1 then … f p … else …`. For measure recursion, add a fuel argument bounded by the input and prove it sufficient (`logn_rec` (boot/prime.v:623) is called as `logn_rec p m m`). First check whether `iter`, `foldr` or a bigop already expresses the function. Never `Unset Guard Checking` or `Admitted` | §32.5 |
| `Cannot guess decreasing argument of fix` | Several arguments, and none is structurally decreasing | Add `{struct x}` on the intended argument: the error becomes the row above and names the bad call; then fix it as above | §32.5 |
| `Non exhaustive pattern-matching: no clause found for pattern _.+1` | A `match` misses a constructor (the pattern prints in mathcomp notation) | Add the branch or a `_ =>` catch-all, or use `if n is p.+1 then … else …`; branches are tried top to bottom | §32.5 |
| `Non strictly positive occurrence of "T" in "(T -> False) -> T"` | `T` occurs in a function domain of its own constructor | Redesign the type. Nesting through `seq T`, `option T`, `{ffun I -> T}` (= `T ^ n`) or `A -> T` is accepted; `n.-tuple T` is rejected with this same message: use `{ffun 'I_n -> T}`, or `seq T` plus a size invariant | §47.5 |

- `Datatypes_nat__canonical__eqtype_Equality` in the environment is
  just `nat` (HB display noise after `==`), not the cause.
- No `Program Fixpoint`, `Function` or `Equations` in mathcomp-upstream
  code (Equations is not a dependency): structural or fuel recursion,
  then properties as lemmas proved by `elim`.
- `Fail Fixpoint …` / `Fail Inductive …` belong in test files only, to
  pin an intended rejection.
- `scripts/parse-coqc-errors.py` classifies these as `ill_formed_fix` /
  `non_exhaustive` / `non_positive`, not as the rewrite `not_subterm`.

```coq
From mathcomp Require Import all_boot.

(* WRONG: n.-1 and n are not subterms of n (row 1); missing _.+1 (row 3) *)
Fail Fixpoint bad n := if n == 0 then 0 else bad n.-1.
Fail Fixpoint loop (n : nat) : nat := if n is 0 then loop n else 0.
Fail Definition wrong (n : nat) := match n with 0 => true end.
(* RIGHT: recurse on the pattern variable; ssrnat's half is taken *)
Fixpoint half' n := if n is n'.+2 then (half' n').+1 else 0.
Lemma half'_double n : half' n.*2 = n.
Proof. by elim: n => // n IHn; rewrite doubleS /= IHn. Qed.
Fixpoint sum_to (n : nat) : nat := if n is p.+1 then n + sum_to p else 0.

(* RIGHT, measure recursion: fuel k bounds the steps (cf. logn_rec) *)
Fixpoint log2_rec k n :=
  if k is k'.+1 then (if 1 < n then (log2_rec k' n./2).+1 else 0) else 0.
Definition log2 n := log2_rec n n.
Lemma log2_8 : log2 8 = 3. Proof. by []. Qed.

(* Positivity (row 4) *)
Fail Inductive hidden := Hide of hidden -> False.
Fail Inductive ttree := TNode of 3.-tuple ttree.
Inductive tree := Node of seq tree.
Inductive ftree := FNode of {ffun 'I_3 -> ftree}.
```

---

## 9. Warnings and Qed-time failures

A `Warning:` never stops compilation. Classify it by the bracketed
category (last line of the warning) before touching the file; "fixing"
benign noise breaks working imports.

| Warning (category) | Benign? | Action | Ref |
|---|---|---|---|
| `Notation "_ + _" was already used in scope nat_scope` (also `_ - _`, `_ * _`, `_ <= _`, `_ < _`, …) `[notation-overridden]`; 11 on a bare `all_boot` import | benign: ssrnat redefines the Corelib prelude nat notations | ignore; optionally silence with `-w -notation-overridden` (`-arg -w -arg -notation-overridden` in `_CoqProject`); never change imports to avoid it | §3 |
| `New coercion path [GRing.subring_closedM; …] : … is ambiguous with existing …` `[ambiguous-paths]` (9 on `all_algebra`) | benign | ignore | — |
| `Projection value has no head constant … of isSub.Sub_rect, ignoring it` `[projection-no-head-constant]`; `Ignoring canonical projection to eq_op … redundant with …` `[redundant-canonical-projection]` after `[isSub for …]`, `[Equality of S by <:]`, `X.copy` | benign HB noise | ignore | §36.12, §36.13 |
| `Library File mathcomp.ssreflect.all_ssreflect is deprecated since mathcomp 2.5.0. Use 'all_boot' and/or 'all_order' instead.` `[deprecated-library-file-since-mathcomp-2.5.0]` | actionable in new code | switch to `all_boot` (+ `all_order`); exceptions (upstream analysis ≥ 1.16, files that must also build on mathcomp 2.4) in the §3 umbrella table | §3 |
| `Notation ringType is deprecated since mathcomp 2.4.0. Try pzRingType (the potentially-zero counterpart) first, or use nzRingType instead.` `[deprecated-syntactic-definition-since-mathcomp-2.4.0]` (same for `semiRingType`, `comRingType`, `comSemiRingType`, `subRingType`, …) | actionable | rename to the `Pz` form unless `1 != 0` is needed, else `Nz` | §36.2, §48 |
| `Notation leq_trunc_div is deprecated since mathcomp 2.4.0. Renamed to leq_divM.` `[deprecated-since-mathcomp-X]` on a lemma name | actionable | apply the note's replacement verbatim | §48 |
| `Duplicate clear of H. Use {}H instead of {H}H` `[duplicate-clear,ssr]` | actionable | `have {}H : …` | §27.11 |
| `Adding and removing hints in the core database implicitly is deprecated. Please specify a hint database.` `[implicit-core-hint-db,deprecated-since-8.10]` (the book's `Hint Resolve leqnn.`, MCB §2.3.3) | actionable | `#[export] Hint Resolve leqnn : core.` (`#[local]` for file-local use) | §37.9 |
| `HB: no new instance is generated` `[HB.no-new-instance]`; `non forgetful inheritance detected` `[HB.non-forgetful-inheritance]` | NOT benign: the declared instance is missing | fix the declaration (§1 rows above) | §35.5, §36.12 |

Rule: a `deprecated` category is actionable in new code (import
exceptions: §3); categories `notation-overridden` (from a `Require
Import`; on your own `Notation` line it is a real clash, §32.6),
`ambiguous-paths`, `projection-no-head-constant` and
`redundant-canonical-projection` are never the cause of a failure. Look
for the `Error:` line instead.

Qed-time failure (no tactic failed, but goals were still open at `Qed`,
so the error points at `Qed`, far from the faulty step):

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `(in proof t3): Attempt to save an incomplete proof (there are remaining open goals).` | a branch ended without `by` (its last `rewrite` left a goal such as `m = m`); or an unclosed bullet: bullets are inert under ssreflect (Bullet Behavior "None"), so the leftover goal reaches `Qed` or the next bullet runs on the wrong goal | put `by` on the last step of every branch; step with `rocq_check` (or read the goals at the returned `state_id`) to find the open goal | §26.5 |

```coq
From mathcomp Require Import all_boot.

(* WRONG: the last rewrite leaves `m = m` open; the error shows at Qed *)
Lemma t3 m d : 0 < d -> (m * d + 0) %/ d = m.
Proof. move=> d0; rewrite divnMDl // div0n addn0.
Fail Qed.  (* Attempt to save an incomplete proof (...open goals) *)
Abort.

(* RIGHT: `by` on the last step of every branch *)
Lemma t3' m d : 0 < d -> (m * d + 0) %/ d = m.
Proof. by move=> d0; rewrite divnMDl // div0n addn0. Qed.
```

---

## Quick triage

| The message mentions… | Go to | First check |
|---|---|---|
| infer / placeholder / canonical / `id_phant` / non forgetful inheritance | §1 | `HB.about T`; import order (§3) |
| `Equality.sort ?s` / `pred_sort ?pT` / `pT of mem` | §1 | `HB.about T`; `predArgType` / `{: T}` |
| unify "X" with "Y" | §2 | `Set Printing All`; `%R`/`%E` (§19) |
| has type … while it is expected to have type | §2 | cast (`%:R`, `%:E`); `About lem` |
| not a subterm / does not match any subterm / Dependent type error (rewrite) | §3 | pattern / `under` (§29); size index: `castmx` (§38.10) |
| Illegal / Non-functional | §4 | `About f` arity; coercion |
| Unknown / not found / scope | §5 | `Local Open Scope`; `Import` (§3) |
| anomaly / `_subproof` / universe | §6 | `#[verbose] HB.instance`; `HB.howto` |
| used in hypothesis / Pattern … not completely instantiated / variable … not found | §7 | push deps (`case: y h`); `leqP`; bind with `=>` |
| ill-formed / Non exhaustive / positive | §8 | recurse on the pattern variable |
| Warning / deprecated | §9 | benign vs actionable category |
| incomplete proof (at `Qed`) | §9 | `by` on each branch |

When in doubt, inspect the live state at the error with
`rocq_compile_file` (it hands back goals + a `state_id` at the error
position) and read the goal before changing the script.
