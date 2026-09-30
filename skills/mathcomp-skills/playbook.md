# mathcomp-analysis cleanup playbook

Concrete, validated cleanup patterns for math-comp / mathcomp-analysis
Rocq codebases. Each pattern below has been **tested on a real
codebase**; the "Confirmed working" patterns build clean, the "False
positives" build-broke when applied blindly and need per-site
judgment.

The pattern numbering tracks the sections of `reference.md` so you
can follow the trail of reasoning.

---

## Confirmed working (apply mechanically, then build to verify)

### Risk-tiered summary (quick index)

At-a-glance index into the patterns documented below. Tiers mirror the
confidence ranking the prose already uses: Tier 1 is mechanical and
near-safe; Tier 2 needs a per-site glance; Tier 3 is verify-every-site
or a known false positive (see "Audit recommendations that don't pan
out"). The detailed prose remains authoritative — this is just a map.

| Pattern | Typical savings | Risk / false-positive | How to verify |
|---------|-----------------|-----------------------|---------------|
| **Tier 1 — mechanical, near-safe** | | | |
| §23.1 lowercase `order.Order.X` in Import lines | 0-1 lines | leave Import lines as-is; only fix body uses | build |
| §23.2 add `From mathcomp Require Import` clause | ~20-30 findings/5 edits | `Local Lemma` names need a `Local Notation` | build |
| §24.1 drop `[the X of T]` over canonical HB instance | 1 line each | leaked HB-internal names need user-facing form | build |
| §22.3 drop `%R`/`%E`/`%N` inside an open scope | per occurrence | keep delimiter only when *switching* scopes | build |
| §27.8 no bullets for 2-subgoal splits | 1-2 lines | none (pure mechanical) | build |
| §32.1 rename `_is_pdf` → `fooE` (is_ is predicate-only) | rename | global rename; audit external uses | `grep -lw`, build |
| §3 `all_ssreflect` → `all_boot all_order` | 1 warning | not in analysis ≥ 1.16 files (they use `all_ssreflect_compat`) | build |
| §27.11 `have {H}H` → `have {}H` | 1 warning each | none | build |
| §37.9 `Hint Resolve l.` → `#[export] Hint Resolve l : core.` | 1 warning each | delete instead if `l` is already a hint | build |
| **Tier 2 — per-site glance** | | | |
| §22.1 drop `have -> : E by [].` at defeq | 2 lines each | only if next tactic alone still compiles | replace + build |
| §27.1/§27.4 hypothesis bookkeeping (`exact`, inline) | 1 line each | name may be reused later | build |
| §27.5 combine intro + destructure (`have [a b] :=`) | 1 line | none typical | build |
| §25 keyed-implicit form replaces `@` in signatures | per signature | only in lemma *signatures*, not Builder calls | build |
| §27.6 front-load anonymous `have ? :` positivity | several lines | parser: single-tactic subproof only | build |
| §29 `(_ : EXPR = VAL)` rewrite-with-equation | named `have`+line | use only when 1 consumer | build |
| §18 mark HB-helper lemmas `Local` | namespace hygiene | break if used in other files | `grep -lw`, build |
| §36.2 deprecated ring names → `Nz` (safe) / `Pz` (check) | 1 warning each | `Pz` loses `1 != 0` (`oner_neq0`, units, degree) | build per site |
| §28.1 `case: leP` on nat → `case: leqP` | 0-2 lines | stdlib bridge: `move/ssrnat.leP` under `Order.TTheory` | build |
| §27.10 `move: H; rewrite E => H` → `rewrite E in H` | 1 line | `in H *` also rewrites the goal | build |
| §30.7 `have h : A && B` + `move/andP: h` → `have /andP[..] :` | 1 line | none typical | build |
| §29.3 `rewrite l1 ?l2 ?l3 //` → `rewrite l1 ?l2 // l3` | 0 lines | may now fail at the broken line (intended) | build |
| §22.5 `destruct b; auto` → `by case: b` | 0-1 lines | `congruence` is a review point, not banned | build |
| §27.5 ill-typed `/eqP/andP[..]` → `/andP[/eqP-> ..]` | 0 lines | none | build |
| **Tier 3 — verify every site / known FP** | | | |
| §27.6 extract reusable identity / `have step U` | big-proof shrink | wrong extraction boundary won't reduce cleanly | build |
| Strip `@` from HB `.Build` calls | — | FP: HB needs explicit struct params | build (will fail) |
| Inline `mfun_Sub (mem_set h)` chains | — | FP: elaborator needs typed `\in` bridge | build (will fail) |
| Move section `Arguments` post-`End` | — | FP: changes implicit→explicit, breaks callers | comment out + build |
| Inline type-anchoring wrappers / `exact:` arg-strip | — | FP: elaborator can't recover numeral/projector | per-site build |
| Delete "dead" `have` | — | FP: may feed unifier / hint resolution | delete + build |
| §48 `EqMixin` / `Canonical` / `[eqType of T]` → HB | 1-2 lines each | book (1.x) syntax: no longer exists | build |
| §36.12 hand-proved `Equality.axiom` with a `pcancel` at hand → `X.copy T (pcan_type fK)` | proof + lines | cancel direction: `f` maps the new type into the old | per-site build |

### §23.1 Import convention: lowercase `order.Order.X`

The `order.v` file in `math-comp` exposes a `Module Order` whose
contents (e.g. `TTheory`, `TotalTheory`, `POrderTheory`) are reached
via `Import order.Order.X` (lowercase `order.` is the file path).
**This form is correct in Import lines** — what's wrong is using
`order.Order.X.lemma` as a fully-qualified *use* in source body.

If you see `order.Order.POrderTheory` in an Import line, leave it.
If you see `order.Order.TotalTheory.ltNge` in source, fix the import
(add `Import order.Order.TotalTheory.` or `Import order.Order.TTheory.`)
and drop the prefix at the use site.

### §23.2 Add missing `From mathcomp Require Import` clauses

When you see source like `derive.derivableM`, `charge.X.f`,
`trigo.pi`, `exp.expRD`, `ftc.continuous_FTC2`: add the file to the
`From mathcomp Require Import` list at the top, then drop the
qualifier at use sites.

```coq
(* Before *)
From mathcomp Require Import all_boot all_algebra reals.
...
have hpi : 0 <= trigo.pi := trigo.pi_ge0 R.

(* After *)
From mathcomp Require Import all_boot all_algebra reals trigo.
...
have hpi : 0 <= pi := pi_ge0 R.
```

**Caveat**: some names are `Local Lemma` inside the upstream file
(e.g. `archimedean.Num.Theory.truncnP`). For those, keep a
`Local Notation truncnP := archimedean.Num.Theory.truncnP.` —
that's the canonical workaround.

### §24.1 Drop `[the X of T]` over already-canonical HB instances

When `T` already has an `HB.instance Definition _ := …Build … T …`
declaration above, the `[the probability M R of T]` ascription is
noise. Drop it.

```coq
(* Before *)
Definition normalize_mu : probability mR R :=
  [the probability mR R of norm_mu].

(* After *)
Definition normalize_mu : probability mR R := norm_mu.
```

Special case: leaked HB-internal canonical names like
`Datatypes_prod__canonical__measurable_structure_Measurable mR mR` →
replace with the user-facing form `[set: mR * mR]`.

### §22.1 Drop useless `have -> : E by [].` at definitional equalities

```coq
(* Before -- both sides are defeq, the rewrite does nothing *)
move=> alpha f [h1 h2]; split.
- have -> : (fun r => ((alpha \o f) r).1) =
            (fun r => (alpha r).1) \o f by [].
  exact: pred_comp h1.
- have -> : ... by [].
  exact: pred_comp h2.

(* After *)
move=> alpha f [h1 h2]; split.
  exact: pred_comp h1.
exact: pred_comp h2.
```

**Test**: the `have -> : E by [].` is removable iff replacing the
whole line with the next tactic alone still compiles. If the next
tactic is an `exact:` and the goal shape after the rewrite is
defeq to before, the rewrite was load-bearing only for the eye.

### §27.1, §27.4 Hypothesis bookkeeping

```coq
(* Anti-pattern — name then immediately consume *)
Proof. by move=> halpha U hU; exact: hU. Qed.

(* Idiom *)
Proof. by move=> halpha U; exact. Qed.
```

```coq
(* Anti-pattern — `have hX := f r` then `case: ifPn hX => ...` *)
have hTP := truncnP r.
case: ifPn hTP => [h0 /andP [_ hr2] | hlt0 /eqP hn0].

(* Idiom *)
case: ifPn (truncnP r) => [h0 /andP [_ hr2] | hlt0 /eqP hn0].
```

### §27.5 Combine intro and destructure

```coq
(* Anti-pattern *)
have := @choice _ _ _ hX; move=> [a b].

(* Idiom *)
have [a b] := choice hX.
```

### §27.8 No bullets for 2-subgoal splits

```coq
(* Anti-pattern *)
split.
- by exact: foo.
- by exact: bar.

(* Idiom *)
by split; [exact: foo | exact: bar].
(* OR *)
split.
  exact: foo.
exact: bar.
```

### §32.1 Drop `_is_pdf` etc.: `is_` prefix is for predicates

A lemma `Lemma foo_is_pdf : … = …` (an equation) violates the
naming convention. Rename to `fooE` (cancel/equation suffix) or just
`foo`. The `is_`/`has_` prefix is reserved for predicate / structure
factories.

### §22.3 Drop `%R`/`%E`/`%N` inside an open scope

If `Local Open Scope ring_scope.` is in effect, every `(x + 0)%R`
becomes `x + 0`. If `Local Open Scope ereal_scope.` is in effect,
every `(\int[mu]_x f)%E` becomes `\int[mu]_x f`. Only retain the
delimiter when **switching** scopes.

### §25 keyed-implicit form replaces `@` in lemma signatures

```coq
(* Before *)
Lemma foo (T : someType R) ... :
  G `<=` @predX R (generated T G).

(* After *)
Lemma foo (T : someType R) ... :
  G `<=` predX (s := generated T G).
```

The keyed-implicit form survives upstream parameter renames; bare
`@` does not.

### §27.6 Front-load anonymous `have ?` for positivity / non-zeroness

When several rewrite steps later in a proof discharge their side
conditions via `//`, hoist the positivity / non-zero facts to the top
of the proof as anonymous `have ? : …` lines. Subsequent steps that
previously re-derived these inline collapse to a single `rewrite`.

```coq
(* Before -- named, with inline derivation of each positivity *)
have sigma0_2pos : 0 < sigma0 ^+ 2 by rewrite exprn_even_gt0.
have sigma_2pos : 0 < sigma ^+ 2 by rewrite exprn_even_gt0.
have sumpos : 0 < sigma0 ^+ 2 + sigma ^+ 2 by apply: addr_gt0.
have sum_neq0 : sigma0 ^+ 2 + sigma ^+ 2 != 0 by rewrite lt0r_neq0.
have sqrt_sum_neq0 : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0
  by rewrite sqrtr_eq0 -ltNge.
have sigma_post_pos : 0 < sigma_post sigma0 sigma.
  rewrite /sigma_post sqrtr_gt0; apply: divr_gt0 => //.
  by apply: mulr_gt0.
have sigma_post_neq0 : sigma_post sigma0 sigma != 0 by rewrite lt0r_neq0.

(* After -- anonymous; each line either inlines `by` or has a single
   indented `by` closing line; later rewrites discharge via assumption *)
have ? : 0 < sigma0 ^+ 2 by rewrite exprn_even_gt0.
have ? : 0 < sigma ^+ 2 by rewrite exprn_even_gt0.
have ? : 0 < sigma0 ^+ 2 + sigma ^+ 2 by apply: addr_gt0.
have ? : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0 by rewrite sqrtr_eq0 -ltNge.
have ? : 0 < stddev_post sigma0 sigma
  by rewrite /stddev_post sqrtr_gt0 divr_gt0// mulr_gt0.
have ? := stddev_post_neq0 _ _ sigma0_neq0 sigma_neq0.
```

The second block is what an audited mathcomp-analysis proof looks
like. `have ? := lemma args.` is the canonical way to surface a
top-level lemma's conclusion into the assumption pool for later `//`
discharges.

**Parser limitation**: `have ? : T.` only accepts a single-tactic
sub-proof. Multi-line sub-proofs (e.g., after `apply: mulr_gt0` opens
two subgoals) must keep a name. Example: a `0 < K` derivation that
needs `rewrite /K normal_pdfE //; apply: mulr_gt0.` followed by two
indented `by …` lines closing each subgoal stays as `have Kpos : …`,
not `have ? : …`. See `reference.md` §27.6.

### §29 The `(_ : EXPR = VAL)` rewrite-with-equation pattern

When the next rewrite chain would benefit from substituting a concrete
value into a complex subterm, package the value as a one-shot
equation inside `rewrite`. The side goal `EXPR = VAL` is closed by the
immediately following indented `by …`:

```coq
(* Before -- a `have` introduces a name used exactly once in the next line *)
have sqsum_eq :
  Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) ^+ 2 = sigma0 ^+ 2 + sigma ^+ 2
  by rewrite sqr_sqrtr // ltW.
have sqpost_eq : sigma_post sigma0 sigma ^+ 2
  = sigma0 ^+ 2 * sigma ^+ 2 / (sigma0 ^+ 2 + sigma ^+ 2).
  rewrite /sigma_post sqr_sqrtr //.
  apply: divr_ge0; first by apply: mulr_ge0; exact: ltW.
  exact: ltW.
rewrite /normal_peak sqsum_eq sqpost_eq -invfM ...

(* After -- the equations are inlined into the next rewrite *)
rewrite /normal_peak (_ : Num.sqrt _ ^+ 2 = sigma0 ^+ 2 + sigma ^+ 2).
  by rewrite sqr_sqrtr// ltW.
rewrite (_ : stddev_post sigma0 sigma ^+ 2
  = sigma0 ^+ 2 * sigma ^+ 2 / (sigma0 ^+ 2 + sigma ^+ 2)).
  by rewrite /stddev_post sqr_sqrtr// divr_ge0// ?addr_ge0 ?ltW// mulr_gt0.
rewrite -invfM ...
```

The `(_ : E = V)` form opens a subgoal `E = V` (closed by the next
indented `by`) and rewrites the *main* goal with the proven equation.
Use when the named intermediate has exactly one consumer. Saves a
named `have`, a name, and a `rewrite name` line per substitution.

### §27.6 Extract a reusable algebraic identity to a top-level lemma

When a "complete the square"-style polynomial identity sits inside a
big proof and could be reused (or just reads more cleanly in
isolation), extract it. The original proof shrinks to one line via
`exact: extracted_lemma`. Only when it is self-contained; an identity
tied to the proof's local context stays local (`set`/`pose`/`have`,
reference §30.8). Common shape:

```coq
(* Before -- a 20-line algebraic identity nested mid-proof *)
congr (_ * _); first last.
  rewrite /normal_fun -2!expRD; congr (expR _).
  rewrite sqr_sqrtr; last exact: ltW sumpos.
  rewrite /sigma_post sqr_sqrtr; first last.
    apply: divr_ge0; first by apply: mulr_ge0; exact: ltW.
    exact: ltW.
  rewrite /mu_post; field.
  by apply/and3P; split.

(* After -- the same identity stated and proven as its own lemma *)
Lemma normal_fun_conjugate (mu0 sigma0 sigma x theta : R) :
  sigma0 != 0 -> sigma != 0 ->
  normal_fun theta sigma x * normal_fun mu0 sigma0 theta
  = normal_fun mu0 (Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2)) x
    * normal_fun (mean_post mu0 sigma0 x sigma)
                 (stddev_post sigma0 sigma) theta.
Proof. (* the original 8-line algebra block, now standalone *) Qed.

(* ...and the original proof becomes: *)
congr (_ * _); first last.
  exact: normal_fun_conjugate.
```

Heuristics:

- The identity is *purely* about ground algebra (no measure-theoretic
  baggage) — a sign that other developments may want it.
- It is closed by a `field`/`ring`/`lra` after a fixed setup
  (`expRD`, `sqr_sqrtr`, …) — extraction makes the setup reusable.
- The enclosing lemma cleanly reduces to `exact: extracted` or
  `rewrite extracted` after extraction; if not, the extraction
  boundary was wrong.

### §27.6 Factor structurally-duplicated obligations into `have step U`

When two sibling subgoals are *the same lemma at different arguments*
— e.g., the numerator and denominator of a Bayes quotient are the
same integral identity instantiated at `V` and `setT` — factor them
as a single parameterised local lemma rather than copying the proof.

```coq
(* Before -- `num_eq` and `denom_eq` differ only by domain (V vs setT) *)
have num_eq :
  (\int[normal_prob mu0 sigma0]_(theta in V) (normal_pdf theta sigma x)%:E
   = K%:E * P)%E.
  rewrite integral_normal_prob //;
    last exact: integrable_normal_pdf_likelihood.
  under eq_integral => theta _ do
    rewrite -EFinM (normal_pdf_conjugate mu0 x theta ...) EFinM.
  rewrite -/K ge0_integralZl_EFin //=; first last.
  - exact: ltW.
  - apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - by move=> theta _; rewrite lee_fin; exact: normal_pdf_ge0.
have denom_eq :
  (\int[normal_prob mu0 sigma0]_theta (normal_pdf theta sigma x)%:E
   = K%:E)%E.
  rewrite integral_normal_prob //;
    last exact: integrable_normal_pdf_likelihood.
  under eq_integral => theta _ do
    rewrite -EFinM (normal_pdf_conjugate mu0 x theta ...) EFinM.
  rewrite -/K ge0_integralZl_EFin //=; first last.
  - exact: ltW.
  - apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - by move=> theta _; rewrite lee_fin; exact: normal_pdf_ge0.
  by rewrite integral_normal_pdf // mule1.
by rewrite num_eq denom_eq muleAC divee // mul1e.

(* After -- one parameterised local lemma, applied twice *)
have step U : measurable U ->
  (\int[normal_prob mu0 sigma0]_(theta in U) (normal_pdf theta sigma x)%:E
   = K%:E * normal_prob (mean_post ..) (stddev_post ..) U)%E.
  move=> mU.
  rewrite integral_normal_prob //;
    first exact: integrable_normal_pdf_likelihood.
  under eq_integral => theta _ do
    rewrite -EFinM (normal_pdf_conjugate mu0 x theta ...) EFinM.
  rewrite -/K ge0_integralZl_EFin //=; first last.
  - exact: ltW.
  - apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - by move=> theta _; rewrite lee_fin; exact: normal_pdf_ge0.
rewrite (step _ mV) (step _ measurableT) probability_setT mule1.
by rewrite muleAC divee // mul1e.
```

This is the in-proof analogue of "extract a reusable lemma" — the
`have step U : T` mini-lemma is local to the enclosing proof but
abstracts the structural duplication. Heuristic: if you find yourself
copy-pasting a `rewrite` chain with one variable substituted, the
factor is `step`.

### §18 Mark HB-instance helper lemmas `Local`

```coq
(* If a lemma is used only to feed isFoo.Build, make it Local *)
Local Lemma my_struct_ax1 ... := ...
Local Lemma my_struct_ax2 ... := ...
HB.instance Definition _ := isFoo.Build _ ...
  (@my_struct_ax1 X Y) (@my_struct_ax2 X Y) (@my_struct_ax3 X Y).
```

Reviewers flag globally-exported helpers as namespace
pollution.

**Always check external uses first**: `grep -lw "lemma_name" *.v`.
If non-zero in other files, keep it `Lemma`.

### Book-era idioms (MCB, mathcomp 1.x) → mathcomp 2.5

These translate idioms from the Mathematical Components book and from
agents trained on it. Each block compiles on Rocq 9.1 + mathcomp 2.5
(Before forms as comments or `Fail`); still build the real site. Full
old → new map: §48.

### §3 Import swap: `all_ssreflect` → `all_boot all_order`

`all_ssreflect` is deprecated since mathcomp 2.5.0 and only re-exports
`all_boot` + `preorder` + `order` (`mathcomp/ssreflect/all_ssreflect.v`).
Import the two umbrellas directly (tiers in §3).

```coq
(* Before -- warns: deprecated since mathcomp 2.5.0 *)
(* From mathcomp Require Import all_ssreflect. *)
(* After *)
From mathcomp Require Import all_boot all_order.
Import Order.TTheory.
Check le_trans.   (* order.v lemmas still in scope *)
```

**Caveat**: `all_boot` alone drops `order` (FP 8).

### §27.11 `have {H}H` → `have {}H`

Rocq 9.1 warns `Duplicate clear of H. Use {}H instead of {H}H`; `{}H`
refines `H` in place (MCB §4.3.3). Find sites with
`grep -nE 'have \{([A-Za-z_][A-Za-z_0-9]*)\}\1' *.v`.

```coq
From mathcomp Require Import all_boot.
Lemma mul_succ_gt0 n (H : 0 < n) : 0 < n.+1 * n.
Proof.
(* Before (warns): have {H}H : 0 < n.+1 * n by rewrite muln_gt0 H. *)
have {}H : 0 < n.+1 * n by rewrite muln_gt0 H.
exact: H.
Qed.
```

### §37.9 `Hint Resolve l.` → `#[export] Hint Resolve l : core.`

A hint without a database, such as the book's bare `Hint Resolve
leqnn.` (MCB §2.3.3), now warns `[implicit-core-hint-db]`.
Use `#[export]` for importers, `#[local]` for this file only. The
book's `Hint Resolve leqnn.` is redundant (boot/ssrnat.v:333 already
declares it `#[global]`): delete such lines.

```coq
From mathcomp Require Import all_boot.
Lemma leq_double n : n <= n.*2.
Proof. by rewrite -addnn leq_addr. Qed.
(* Before -- warns [implicit-core-hint-db]: Hint Resolve leq_double. *)
#[export] Hint Resolve leq_double : core.

Lemma leq_double_ex n : n <= n.*2. Proof. by []. Qed.
```

### §36.2 Deprecated ring structure names → `Nz` (safe) or `Pz` (check)

In `mathcomp/algebra/ssralg.v`, `semiRingType`, `ringType` (l. 7081),
`comSemiRingType`, `comRingType` (l. 7087), `subSemiRingType`,
`subComSemiRingType` and `subRingType` are `(only parsing)` notations
deprecated since 2.4.0. Each means its `Nz` counterpart, so
`comRingType` → `comNzRingType` is semantics-preserving (the book's
ring structures are nontrivial by construction, MCB §8.1). `Pz` is more
general but loses `1 != 0`: try it per site and revert where the proof
uses `oner_neq0`, unit theory or polynomial degree (FP 9).

```coq
From mathcomp Require Import all_boot all_order all_algebra.
Import GRing.Theory.
Local Open Scope ring_scope.
(* Before (warns): Lemma one_neq0 (R : comRingType) : ... *)
Lemma one_neq0 (R : comNzRingType) : (1 : R) != 0.
Proof. exact: oner_neq0. Qed.

Section Pz.   (* Pz generalizes, but 1 != 0 is gone *)
Variable R : comPzRingType.
Fail Check oner_neq0 R.
End Pz.
```

### §28.1 `case: leP` on nat → `case: leqP`

On nat, split with `leqP`/`ltnP`/`ltngtP` (§28.1; MCB §5.2.1). Under
`Import Order.TTheory`, `case: leP` is Order's lemma and fails
(`Pattern (leP _ _) was not completely instantiated`). Without it,
ssrnat's `leP` only adds `%coq_nat` hypotheses.

```coq
From mathcomp Require Import all_boot all_order.
Import Order.TTheory.
Lemma leq_or_gt m n : (m <= n) || (n < m).
Proof. by case: leqP. Qed.   (* not: case: leP *)

Lemma to_coq m n : m <= n -> (m <= n)%coq_nat.
Proof. by move/ssrnat.leP. Qed.   (* bare leP is Order's here *)
```

### §27.10 `move: H; rewrite E => H` → `rewrite E in H`

No round-trip through the goal. `rewrite E; rewrite E in H` becomes
`rewrite E in H *` (MCB §7.2).

```coq
From mathcomp Require Import all_boot.
Lemma rw_hyp (a b : nat) (h : a = b) (p : a < 3) : b < 3.
Proof. rewrite h in p. exact: p. Qed.   (* not: move: p; rewrite h => p *)

Lemma rw_both (a b : nat) (h : a = b) (p : a < 3) : a < 4.
Proof. rewrite h in p *. exact: leq_trans p _. Qed.
```

### §30.7 `have h : A && B` + `move/andP: h` → `have /andP[..] :`

`have` takes an intro pattern with views; the named intermediate goes
away (MCB Part III, cheat sheet).

```coq
From mathcomp Require Import all_boot.
Lemma hv (a b c : nat) (P : pred nat) (h : P a && (b == c)) : b = c.
Proof.
(* Before: have h' : P a && (b == c) by [].                  *)
(*         move/andP: h' => [_ /eqP->].                      *)
by have /andP[_ /eqP->] : P a && (b == c) by [].
Qed.
```

### §29.3 Fail early: `rewrite l1 ?l2 ?l3 //` → `rewrite l1 ?l2 // l3`

Put `?` only on rules that close side conditions. If `l3` targets the
main goal, a `?l3` that stops matching after an upstream change fails
silently and the error surfaces later, or never. A strict `l3` makes
the build fail on the line that broke; that is the point (MCB §4.3.2).

```coq
From mathcomp Require Import all_boot.
Lemma mulK_sq m n : 0 < n -> (m * (n * n)) %/ (n * n) + 0 = m.
Proof.
move=> n_gt0.
(* Before: rewrite mulnK ?muln_gt0 ?n_gt0 ?addn0 //. *)
by rewrite mulnK ?muln_gt0 ?n_gt0 // addn0.
Qed.
```

### §22.5 `destruct b; auto` → `by case: b`

Black-box closers (`auto`, `eauto`, `intuition`, `firstorder`, `tauto`)
hide which step works and break without a location (MCB §4.3.2,
fail early and locally); use `case:`, views and `//`. Find them with
`grep -nwE 'auto|eauto|intuition|firstorder|tauto' *.v`. `congruence`
is rare but used upstream (mathcomp-finmap `finperm.v`): flag it, do
not ban it.

```coq
From mathcomp Require Import all_boot.
Lemma orbN_ex (b : bool) : b || ~~ b.
Proof. by case: b. Qed.   (* not: destruct b; auto.  / intuition. *)
```

### §27.5 Nest views inside the destructuring brackets

`/v1/v2` feeds `v1`'s output to `v2`, so in `/eqP/andP[h1 h2]` `andP`
receives an equation: ill-typed. Put the view on the component inside
the brackets (MCB §5.1.3; phrasebook §2b).

```coq
From mathcomp Require Import all_boot.
Lemma chain (x y : nat) (b : bool) : (x == y) && b -> y = x.
Proof.
Fail move=> /eqP/andP[h1 h2].   (* Before: eqP's output is no && *)
by move=> /andP[/eqP-> _].      (* After: nest the view *)
Qed.
```

### §48 / §36.12 Instance declarations: mixins → HB

`EqMixin`, `EqType`, the `Pcan*Mixin`s and `[eqType of T]` no longer
exist (MCB §6.3–§6.5, §6.10.2, §8.1, §8.5 predate HB). `Canonical T_eqType := EqType T
(EqMixin p)` becomes `HB.instance Definition _ := hasDecEq.Build T p.`
With a cancel lemma, one `copy` gives every structure up to `finType`,
with no hand-proved `Equality.axiom` (§36.12).

```coq
From HB Require Import structures.
From mathcomp Require Import all_boot.
Inductive tri := T0 | T1 | T2.
Definition enc t := match t with T0 => (false, false)
  | T1 => (false, true) | T2 => (true, false) end.
Definition dec p := match p with (false, false) => Some T0
  | (false, true) => Some T1 | (true, false) => Some T2 | _ => None end.
Lemma encK : pcancel enc dec. Proof. by case. Qed.
(* Before (1.x): Pcan{Eq,Choice,Count,Fin}Mixin encK + 4 Canonicals *)
HB.instance Definition _ := Finite.copy tri (pcan_type encK).
Check (tri : finType).
```

**Caveat**: tier 3. In `pcan_type fK` / `can_type fK`, `f` maps the
new type into the existing one; the reversed lemma fails to elaborate.
`copy` prints harmless `redundant-canonical-projection` warnings.

---

## Audit recommendations that DON'T pan out

These patterns sound right but break when applied. Don't trust an
LLM-generated audit that recommends them without verifying.

### 1. Stripping `@` from HB Builder calls

```coq
(* Audit says: drop @ *)
HB.instance Definition _ := isFooMorphism.Build f hf.
(* Reality: HB needs the structure params explicit *)
HB.instance Definition _ := @isFooMorphism.Build R X Y f hf.
```

The `@` is required because HB's `.Build` uses positional arguments
where the structure params (here `R X Y`) must be supplied. This is
universal across HB-instance contexts.

### 2. Inlining `mfun_Sub (mem_set h)` chains

```coq
(* Audit says: inline *)
exact: {| field1 := wrapped_Sub (mem_set h_meas) ; ... |}.
(* Reality: elaborator can't unify without the bridging `\in P` *)
have h : f \in P by apply: mem_set; exact: h_meas.
exact: {| field1 := wrapped_Sub h ; ... |}.
```

Keep the typed bridge `have h : f \in P. by …`. The pattern shows up
whenever a record-builder or `_Sub` function expects an `\in`-typed
argument; the elaborator needs the named term to anchor unification.

### 3. Moving section-local `Arguments` declarations post-`End`

```coq
(* Inside Section foo *)
Arguments my_def : clear implicits.

(* Audit says: also add this AFTER End foo. *)
End foo.
Arguments my_def : clear implicits.   (* DON'T *)
```

Inside-section `Arguments : clear implicits` already does the right
thing (the section variable, e.g., `R`, is added as an implicit
parameter at section close). Repeating it post-`End` actually
CHANGES the behavior — forcing the section variable from
implicit-by-default to explicit, which breaks downstream call sites.

**Always test**: comment out the post-section declaration and see if
the build still passes. If yes, you didn't need it.

### 4. Inlining type-inference-anchoring wrappers

```coq
(* Generic shape: a wrapper specializing a parametric lemma to a
   concrete numeral / instance, used as an argument to a higher-arity
   lemma where the elaborator can't recover that numeral *)
Lemma my_specific_neq0 : sqrtr (9%:R / 37%:R) != (0 : R).
Proof. exact: my_generic_neq0. Qed.

(* In use site: this works *)
rewrite (some_chain _ _ _ _ my_specific_neq0 other_arg).

(* Replacing with `(my_generic_neq0 _ isT)`: doesn't elaborate
   because the nat (37) is underdetermined at the call position *)
```

The wrapper anchors the parameter for type inference. Inlining
forces the elaborator to guess; it can't. Keep the wrapper.

### 5. "Dead" `have` statements that are actually load-bearing

```coq
have hp : 0 <= p := some_positivity_lemma _.
have hap : 0 <= a * p := mulr_ge0 _ hp.   (* "audit says dead" *)
rewrite some_morph.   (* needs hap to match the unifier *)
```

Some `have` proofs feed implicit unification or hint resolution.
Names that look unused often contribute their typed term to the
elaborator's pool (e.g., `mulr_ge0`'s output unblocks a side
condition in the next `rewrite`). Test by deleting and checking the
build, never delete on inspection alone.

### 6. Stripping `@dirac _ _ x R U`

```coq
(* Audit says: drop @ *)
exact: dirac (R := R) (T := M) x U.
(* Reality: more verbose than the original *)
exact: @dirac _ _ x R U.
```

When `R` (the realType) needs to be supplied and isn't recoverable
from local context, `@dirac _ _ x R U` is the most concise form.
Keyed-implicit `(R := R) (T := M)` is more characters.

### 7. Audit-suggested `exact:` arg-stripping that breaks unification

```coq
(* Audit says: drop arguments *)
exact: measurableT_comp.

(* Reality (in some sites): elaborator can't recover the projector *)
exact: measurableT_comp (measurable_funP f1) measurable_fst.
```

Test per site. The audit's "useless arguments" claim is correct only
when the elaborator can solve unification from the goal alone.

### 8. "Replace `all_ssreflect` by `all_boot` everywhere"

`all_boot` does not load `preorder`/`order`: files using `%O`
notations or `Order.TTheory` lemmas break. Use `all_boot all_order`.
Keep `all_ssreflect` for mathcomp 2.4 builds and `all_ssreflect_compat`
in analysis ≥ 1.16 upstream files (§3).

### 9. "Replace `comRingType` by `comPzRingType` everywhere"

The deprecation note says "Try `comPzRingType` first", but
`comRingType` means `comNzRingType`. Proofs using `1 != 0`
(`oner_neq0`, unit theory, polynomial degree) stop compiling: rename
to `comNzRingType` there, generalize to `Pz` only where it builds.

### 10. "Flip `Set SsrOldRewriteGoalsOrder` to `Unset`" while porting

Upstream analysis 1.16 comments say to flip it when porting a file.
The flip puts the side goals of a conditional `rewrite` first, so
every `rewrite lem; first/last …` now targets the other goal, and
bullets do not catch it (§26.5). First convert those sites to in-chain
`//`, `?lem` or an explicit proof argument (§27.9), then flip.

```coq
From mathcomp Require Import all_boot.
Unset SsrOldRewriteGoalsOrder.
Lemma t4 m d : 0 < d -> (m * d + 0) %/ d = m.
Proof.
move=> d0.
Fail rewrite divnMDl; last by [].   (* passes under Set; now hits main *)
by rewrite (divnMDl _ _ d0) div0n addn0.   (* robust under both orders *)
Qed.
```

---

## Multi-agent audit workflow

For a thorough style audit of a mathcomp Rocq codebase, launch
parallel agents — one per file or per small file-group. Use this
prompt template:

```
You are an extra-critical mathcomp-analysis reviewer auditing
{file_paths}. The style guide is
~/.claude/skills/mathcomp-skills/reference.md (read sections
22-33 in particular for fresh maintainer feedback).

Produce a structured punch list of every style violation. For each
finding: `[§N.X] file:LINE — short description — suggested fix
(1 line max)`.

Categories to enumerate:
- §1, §6, §22.3 — line length, scope delimiters
- §3, §23 — fully-qualified module names
- §8, §26 — proof terminator hygiene
- §9 — tactic spacing
- §10-§14 — naming
- §16, §31 — Arguments / implicits
- §22.1-22.4 — concision / triviality
- §24 — type constraint hygiene
- §25 — `@` discipline
- §27 — bookkeeping idioms
- §28 — case analysis
- §29 — rewriting idioms
- §32 — Definition vs. Notation, is_ prefix on operators

Group findings by section number ascending. After the per-finding
list, give:
- "Top 10 worst offenses"
- Density estimate (X violations across N lines)

Be specific. No vague feedback. Cap response at 6000 words.
```

For very large files split per-section. For broader coverage,
launch 5-7 agents in parallel via the parent's Agent tool, then
consolidate.

After consolidation, **always**:
1. Apply cross-cutting fixes first (§23.1, §23.2, §24.1 — these
   resolve dozens of findings each)
2. Test build after every commit
3. Use the "Audit recommendations that don't pan out" checklist
   above to filter false positives
4. Per-site verify any change beyond the cross-cutting set

---

## Order of operations for a cleanup pass

1. **Imports** (§23) — usually ~20-30 findings resolved
   with ~5 line edits.
2. **`[the X of T]` removal** (§24.1) — trivial.
3. **`Local` / `Fact` reclassification** (§18) — verify external use
   first, then mark.
4. **`@`-stripping in lemma signatures** (§25) — keyed-implicit form
   where it cleans up.
5. **Two-subgoal-bullet removal** (§27.8) — pure mechanical.
6. **Concision passes** (§22.1, §22.2, §27.1, §27.4) — per-site
   verify.
7. **Naming** (§10, §32.1) — global rename, audit external uses.
8. **Header documentation** (§4) — last, after API is stable.

Skip these without a strong reason:
- Splitting big sections (mostly a wash; risk > benefit unless the
  section is actually broken)
- Big-file splits (the ~3000-line file cap aside, only split when
  the split itself improves discoverability)
- Convert thin `Definition` to `Notation` (§32) — works case-by-case
  but most aren't worth the call-site churn

---

## When a cleanup commit breaks something

Pattern: small change → build fails → revert → re-test.

```sh
# After staging the failing change:
git reset --hard HEAD              # if not yet committed
# or, if committed:
git revert HEAD~1                  # creates a revert commit
# then mark in playbook.md why the audit recommendation was wrong
```

The audit is a checklist of *plausible* issues. The build is the
oracle.
