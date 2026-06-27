## 46. Tuple, Permutation, and Binomial Idioms

Three small but pervasive combinatorial structures sit at the
boundary between `mathcomp/boot` and the algebraic hierarchy:
`n.-tuple T` (sized sequences, `boot/tuple.v`, ~691 lines),
`{perm T}` together with its `'S_n` alias (`fingroup/perm.v`,
~727 lines), and `'C(n, m)` (`boot/binomial.v`, ~573 lines). All
three appear in core mathcomp lemma statements that the
domain-specific files (matrix determinants, finset cardinality,
analysis power-series) inherit; reviewer feedback on these
constructs is dominated by **using the wrong representation**
(e.g. a plain `seq` where a `tuple` would dispense with default
elements, a hand-rolled product where `'S_n`'s group structure
is on hand, a manual recursion on Pascal's triangle where one
`bin_fact` rewrite would close the goal). This section
codifies the canonical idioms.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `tnth t i`, `tnth_nth` | access a tuple at `i : 'I_n`; drop into `seq` | §46.2 |
| `eq_from_tnth` | prove tuple equality pointwise on `'I_n` | §46.2, §46.5 |
| `card_tuple` | `#\|{:n.-tuple T}\| = #\|T\| ^ n` for bigops | §46.2, §46.6 |
| `permP`, `permM` | permutation extensionality; `(s * t) x = t (s x)` | §46.3 |
| `tperm`, `odd_perm` | transpositions and parity | §46.3 |
| `card_Sn` | `#\|'S_n\| = n\`!` | §46.3 |
| `binS`, `bin_fact`, `expnDn` | Pascal; clear binomials; binomial theorem | §46.4 |

### 46.1 Reading the notation

**Tuple.** `n.-tuple T` is `Structure tuple_of := Tuple { tval :> seq T; _ : size tval == n }` (`tuple.v` l. 61), an HB sub-type of `seq T`. The coercion `tval` makes every tuple usable wherever a `seq T` is expected.

| Notation | Meaning | Site |
|----------|---------|------|
| `n.-tuple T` | the type of size-`n` tuples | l. 109 |
| `[tuple of s]` | the tuple whose underlying `seq` is `s` (size inferred via `Canonical`) | l. 114 |
| `[tuple]` | the empty (`0.-tuple`) | l. 127 |
| `[tuple x1; ...; xn]` | explicit `n.-tuple` literal | l. 124 |
| `[tuple E \| i < n]` | `mktuple (fun i : 'I_n => E)` | l. 467 |
| `tnth t i` | element access at `i : 'I_n`, no default needed | l. 75 |
| `[tnth t i]` | element access at `i : nat` with `i < n` convertible to `true` | l. 117 |
| `thead t` | first element of an `n.+1`-tuple | l. 239 |
| `tval t`, `t : seq _` | underlying sequence (coercion) | l. 61 |
| `in_tuple s` | the `(size s).-tuple` value `s` | l. 133 |
| `tcast E t` | rebrand an `m.-tuple` as an `n.-tuple` along `E : m = n` | l. 135 |
| `ord_tuple n` | the `n.-tuple 'I_n` enumerating `'I_n` | l. 429 |

**Permutation.** `{perm T}` is `Inductive perm_type := Perm (pval : {ffun T -> T}) & injectiveb pval` (`perm.v` l. 49). The whole thing is a `finGroupType`, with `1`, `*`, `^-1`, `^+ n`, `^` and `commute` from `fingroup.v`.

| Notation | Meaning | Site |
|----------|---------|------|
| `{perm T}` | bundled permutation type | `perm.v` l. 66 |
| `'S_n` | abbreviation for `{perm 'I_n}` | l. 73 |
| `s x` | application of `s : {perm T}` (coercion) | l. 81 |
| `pval s` | underlying `{ffun T -> T}` | l. 51 |
| `1`, `s * t`, `s^-1`, `s ^+ n`, `s ^ t` | group operations (notations from `fingroup.v`) | l. 122 |
| `tperm x y` | the transposition swapping `x` and `y` | l. 221 |
| `aperm x s := s x` | action notation | l. 342 |
| `porbit s x`, `porbits s` | orbit set / set of orbits | l. 345, 348 |
| `(s : bool)`, `odd_perm s` | parity (coerces to `bool`) | l. 356, l. 569 |
| `lift_perm i j s` | lift an `'S_n.-1` over `(i \mapsto j)` | l. 615 |
| `cast_perm E s` | rebrand an `'S_m` as an `'S_n` along `E : m = n` | l. 681 |

**Binomial.** `'C(n, m) := binomial n m` (`binomial.v` l. 174-180, `Arguments binomial : simpl never`). The recursive definition uses Pascal's rule directly:
```
'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m)
```
and is total (`'C(0, k.+1) = 0`). A companion definition `n ^_ m` (l. 124, `Notation` l. 127) gives the falling factorial, with `bin_ffact : 'C(n, m) * m`! = n ^_ m` (l. 237) bridging the two.

| Notation | Meaning | Site |
|----------|---------|------|
| `'C(n, m)` | binomial coefficient `n` choose `m` (in `nat_scope`) | `binomial.v` l. 182 |
| `n ^_ m` | falling factorial `n * (n-1) * ... * (n-m+1)` | l. 127 |
| ``n`!`` | factorial (defined in `ssrnat`) | -- |

### 46.2 Tuple core lemma family

`tuple.v` provides one critical convenience: `tnth` requires no default value. Internally `tnth_default` (l. 72) extracts a default from the size proof; the public face is `tnth_nth` (l. 77) `: tnth t i = nth x t i` (rewritable in either direction with any user-supplied `x`).

| Lemma | Site | Statement |
|-------|------|-----------|
| `size_tuple` | l. 69 | `size t = n` |
| `tnth_nth x` | l. 77 | `tnth t i = nth x t i` (`x` is any default) |
| `tnth_onth` | l. 80 | `tnth t i = x <-> onth t i = Some x` |
| `eq_from_tnth` | l. 96 | `(forall i, tnth t1 i = tnth t2 i) -> t1 = t2` |
| `map_tnth_enum` | l. 86 | `map (tnth t) (enum 'I_n) = t` |
| `tnth0`, `tnthS` | l. 241, 244 | head / tail destruct on `[tuple of x :: t]` |
| `theadE` | l. 247 | `thead [tuple of x :: t] = x` |
| `tuple0` | l. 250 | `[tuple]` is the only `0.-tuple` |
| `tupleP` | l. 256 | `n.+1.-tuple` elimination view (cons-shape) |
| `tnth_map` | l. 262 | `tnth [tuple of map f t] i = f (tnth t i)` |
| `tnth_nseq` | l. 265 | `tnth [tuple of nseq n x] i = x` |
| `tuple_eta` | l. 276 | `t = [tuple of thead t :: behead t]` (for `n.+1`-tuples) |
| `tnth_lshift`, `tnth_rshift` | l. 282, 288 | `tnth [tuple of t1 ++ t2]` on `lshift`/`rshift` |
| `forallb_tnth`, `existsb_tnth` | l. 300, 309 | `[forall i, a (tnth t i)] = all a t` |
| `all_tnthP`, `has_tnthP` | l. 312, 315 | `reflect`-views of those |
| `eqEtuple` | l. 331 | `(t1 == t2) = [forall i, tnth t1 i == tnth t2 i]` |
| `tnthP` | l. 344 | `reflect (exists i, x = tnth t i) (x \in t)` |
| `tuple_uniqP` | l. 356 | `reflect (injective (tnth t)) (uniq t)` |
| `tnth_mktuple` | l. 453 | `tnth (mktuple f) i = f i` |
| `tnth_ord_tuple` | l. 435 | `tnth (ord_tuple n) i = i` |
| `card_tuple` | l. 422 | `#\|{:n.-tuple T}\| = #\|T\| ^ n` |

The two lemmas reviewers reach for over and over are
`tnth_nth` (to drop into `seq`) and `eq_from_tnth` (to prove
tuple equality pointwise on `'I_n`). The first takes any
default, the second collapses extensionality:

```coq
apply: eq_from_tnth => i.
rewrite !tnth_mktuple ...     (* both sides built with mktuple *)

(* OR drop into seq and use the named seq lemma: *)
rewrite (tnth_nth x0) (tnth_nth x0).
```

### 46.3 Permutation core lemma family

`perm.v` lines 88-150 sets up the ssreflect entry points for working on `{perm T}`:

| Lemma | Site | Statement |
|-------|------|-----------|
| `permP` | l. 88 | `s =1 t <-> s = t` (extensionality on the function) |
| `permE` | l. 94 | `@perm T f f_inj =1 f` (compute on a built permutation) |
| `pvalE` | l. 91 | `pval s = s :> (T -> T)` |
| `perm_inj` | l. 97 | `injective s` (resolved as `Hint Resolve`) |
| `perm_onto` | l. 101 | `codom s =i predT` |
| `perm1` | l. 125 | `(1 : {perm T}) x = x` |
| `permM` | l. 128 | `(s * t) x = t (s x)` (note the order!) |
| `permK`, `permKV` | l. 131, 134 | `cancel s s^-1`, `cancel s^-1 s` |
| `permJ` | l. 137 | `(s ^ t) (t x) = t (s x)` |
| `permX` | l. 140 | `(s ^+ n) x = iter n s x` |
| `tpermL`, `tpermR`, `tpermD` | l. 231, 234, 237 | `tperm x y` cases |
| `tpermC` | l. 240 | `tperm x y = tperm y x` |
| `tperm1` | l. 243 | `tperm x x = 1` |
| `tpermK`, `tpermV`, `tperm2` | l. 246, 252, 255 | involutivity / inverse / square |
| `tperm_on` | l. 258 | `perm_on [set x; y] (tperm x y)` |
| `card_perm` | l. 263 | `#\|perm_on A\| = (#\|A\|)`!` |
| `tpermJ` | l. 304 | `(tperm x y) ^ s = tperm (s x) (s y)` |
| `tuple_permP` | l. 315 | `reflect (exists p : 'S_n, s = [tuple ...]) (perm_eq s t)` |
| `prod_tpermP` | l. 521 | every permutation is a product of transpositions |
| `odd_perm1` | l. 503 | `odd_perm 1 = false` |
| `odd_tperm` | l. 515 | `odd_perm (tperm x y) = (x != y)` |
| `odd_permM` | l. 545 | `{morph odd_perm : s t / s * t >-> s (+) t}` |
| `odd_permV`, `odd_permJ` | l. 552, 555 | parity is invariant under inverse / conjugation |
| `card_Sn` | l. 597 | ``#\|'S_n\| = n`!`` |
| `lift_perm_id`, `lift_perm_lift` | l. 617, 620 | how `lift_perm` acts on `i` and on `lift i k'` |
| `permS0`, `permS1`, `permS01` | l. 670-677 | `'S_0`, `'S_1` are trivial |
| `cast_permE` | l. 691 | how `cast_perm` acts |

**Group operation order is reversed** in `permM` (l. 128) compared to functional composition: `(s * t) x = t (s x)`, so `*` reads left-to-right as "do `s` first, then `t`". Reviewers flag the inversed reading.

`reindex_perm s` (l. 294) is the canonical bigop reindexer:
```coq
Notation reindex_perm s := (reindex_inj (@perm_inj _ s)).
```
Use it as `rewrite (reindex_perm s)` to replace `\sum_i F i` by
`\sum_i F (s i)` whenever the underlying index is a `finType` (§34.7).

### 46.4 Binomial core lemma family

| Lemma | Site | Statement |
|-------|------|-----------|
| `bin0` | l. 192 | `'C(n, 0) = 1` |
| `bin0n` | l. 194 | `'C(0, m) = (m == 0)` |
| `binS` | l. 196 | `'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m)` (Pascal) |
| `bin1` | l. 198 | `'C(n, 1) = n` |
| `binn` | l. 214 | `'C(n, n) = 1` |
| `binSn` | l. 263 | `'C(n.+1, n) = n.+1` |
| `bin_gt0` | l. 201 | `(0 < 'C(n, m)) = (m <= n)` |
| `bin_small` | l. 211 | `n < m -> 'C(n, m) = 0` |
| `bin_sub` | l. 246 | `m <= n -> 'C(n, n - m) = 'C(n, m)` (symmetry) |
| `leq_bin2l` | l. 206 | `n1 <= n2 -> 'C(n1, m) <= 'C(n2, m)` |
| `bin_fact` | l. 224 | ``m <= n -> 'C(n, m) * (m`! * (n - m)`!) = n`!`` |
| `bin_factd` | l. 231 | ``0 < n -> 'C(n, m) = n`! %/ (m`! * (n - m)`!)`` |
| `bin_ffact` | l. 237 | `'C(n, m) * m`! = n ^_ m` |
| `bin_ffactd` | l. 243 | `'C(n, m) = n ^_ m %/ m`!` |
| `mul_bin_diag` | l. 218 | `n * 'C(n.-1, m) = m.+1 * 'C(n, m.+1)` |
| `mul_bin_down` | l. 252 | `n * 'C(n.-1, m) = (n - m) * 'C(n, m)` |
| `mul_bin_left` | l. 260 | `m.+1 * 'C(n, m.+1) = (n - m) * 'C(n, m)` |
| `bin2`, `bin2odd` | l. 266, 269 | `'C(n, 2) = (n * n.-1)./2` |
| `bin2_sum` | l. 279 | `\sum_(0 <= i < n) i = 'C(n, 2)` |
| `prime_dvd_bin` | l. 272 | `prime p -> 0 < k < p -> p %\| 'C(p, k)` |
| `expnDn` | l. 298 | binomial theorem: `(a + b) ^ n = \sum_(i < n.+1) 'C(n, i) * (a^(n-i) * b^i)` |
| `Vandermonde` | l. 312 | `\sum_(j < i.+1) 'C(k, j) * 'C(l, i - j) = 'C(k + l, i)` |

`Pascal` (l. 310) is *deprecated* (since mathcomp 2.3.0); it is a notation-only alias of `expnDn` and reviewers flag any new use. `triangular_sum` (l. 286) is similarly deprecated for `bin2_sum`.

The combinatorial characterizations near the bottom of the file
(`card_uniq_tuples` l. 372, `cards_draws` l. 407, `card_draws`
l. 452, `card_ltn_sorted_tuples` l. 457, `card_sorted_tuples`
l. 484, `card_ord_partitions` l. 560) are the canonical entry
points for "count finset configurations" goals — see §40 for the
finset side.

### 46.5 View-application patterns

The three `*P` views you reach for repeatedly:

```coq
(* Tuple membership:                                           *)
move=> /tnthP[i ->].             (* x \in t  ->  x = tnth t i *)
apply/tnthP; exists (Ordinal H). (* exists i, x = tnth t i    *)

(* Tuple uniqueness via tnth-injectivity:                      *)
move=> /tuple_uniqP tnth_inj.    (* uniq t  ->  injective (tnth t) *)
apply/tuple_uniqP => i j eq_ij.  (* injective (tnth t)  ->  uniq t *)

(* Permutation extensionality:                                 *)
apply/permP => x.                (* s = t  reduced to  s x = t x  *)

(* Tuple equality pointwise on 'I_n:                           *)
apply: eq_from_tnth => i.

(* Tuple-as-permutation reflection:                            *)
move=> /tuple_permP[p t_eq].     (* perm_eq s t  ->  exists p, ... *)

(* Permutation parity from tperm decomposition:                *)
case: prod_tpermP => ts -> ne_ts; rewrite odd_perm_prod //.
```

There is no `tnth_inj` or `bin_inj` lemma in mathcomp; the
intended idioms are `tuple_uniqP` (for `tnth`-injectivity from
`uniq`) and `bin_fact` / `bin_ffact` (for binomial identities,
multiplied through to factorials). Searches like `Search bin
"_inj"` return nothing — that is the design.

### 46.6 Bigop interactions

**Tuples as bigop indices.** Because `n.-tuple T` is a `finType`
when `T` is (l. 420), bigops can range over them:

```coq
\sum_(t : n.-tuple T) F t                  (* whole finite type *)
\sum_(t : n.-tuple T | P t) F t            (* predicate filter  *)
```

The cardinality identity `card_tuple : #\|{:n.-tuple T}\| = #\|T\| ^ n` (l. 422) gives the analogue of `card_ord` (§40) for tuple-indexed bigops. To convert between a tuple-bigop and a nested ordinal-bigop, use `mktuple` (l. 451) and `tnth_mktuple` (l. 453):

```coq
\sum_(t : n.-tuple T) F t
  = \sum_(t : n.-tuple T) F [tuple of map (tnth t) (ord_tuple n)]
  (* via tuple_map_ord, l. 432 *)
```

**Permutations in determinants.** The Leibniz formula (matrix.v
`\det`, §38.7) sums over `'S_n`:
```coq
\det A = \sum_(s : 'S_n) (-1) ^+ s * \prod_(i < n) A i (s i).
```
Idioms specific to det proofs:
```coq
rewrite (reindex_perm s).        (* reindex by a fixed permutation s *)
rewrite (bigD1 (1 : 'S_n)) //.   (* split off the identity     *)
rewrite -[s in odd_perm s]invgK. (* parity is invariant under  *)
                                  (* inversion; odd_permV       *)
```
The `(-1) ^+ s` exponentiation hides a `bool -> nat` coercion through `odd_perm` (l. 569). Searches:
```coq
Search odd_perm.                 (* parity lemmas              *)
Search (\det _) "perm".          (* det-of-perm-matrix family  *)
```

**Binomial inside `\sum`.** `expnDn` is *the* go-to for
binomial expansions, and `Vandermonde` for the convolution
identity. When the binomial sits under a `\prod` rather than a
`\sum`, factor through `bin_ffact` / `bin_fact` to turn it into
a factorial product first.

### 46.7 Three-way representation choice: tuple vs `'rV` vs `seq`

When does a sized collection get which type?

| Use case | Right type | Why |
|----------|-----------|-----|
| Mathematical vector with arithmetic (`+`, `*m`, scalar `*:`) | `'rV[R]_n` (§38) | inherits `lmodType`, `algebraType`; entry access is `M 0 i` |
| Indexed family with no arithmetic, just bookkeeping (e.g. an `n`-sample) | `n.-tuple T` | no default needed; `tnth t i` for `i : 'I_n` |
| Variable-length list, permutations, sorting, induction | `seq T` | `nth x s i` requires a default |
| Probability / measure on `T^n` with `\sum_(t : T^n)` | `n.-tuple T` | `card_tuple` gives `#\|T\| ^ n` for free |
| Linear algebra, determinants, eigenvalues | `'M[R]_n` / `'rV[R]_n` | every `matrix.v` lemma keys on `M i j` |
| Permutation-as-data | `'S_n` | get `*`, `^-1`, `^+ n`, `^`, parity, orbits, `card_Sn` |

Conversions:
- `tuple` → `seq`: built-in coercion via `tval`.
- `seq` (with size proof) → `tuple`: `Tuple p` or `[tuple of s]` (the second form requires a `Canonical` projection — every standard seq builder has one, see `tuple.v` l. 173-237).
- `tuple` → `'rV`: `\row_i tnth t i`.
- `'rV` → `tuple`: `[tuple of [seq M 0 i | i <- enum 'I_n]]` (rare; usually a sign that the algorithm should stay in matrix form).
- `'S_n` → `n.-tuple 'I_n`: `[tuple s i | i < n]` via `tuple_permP` (l. 315).

### 46.8 Common pitfalls

1. **Reaching for `nth x t i` instead of `tnth t i`.** A tuple
   carries its size proof; `tnth` is total without a default
   (`tuple.v` l. 75). The standard idiom is `tnth t i` with
   `i : 'I_n`; rewrite to `nth` only when an external lemma
   (e.g. `nth_iota`, `nth_map`) demands it, and supply *any*
   convenient default — `tnth_nth` (l. 77) holds for every `x`.

2. **Using `apply: tnth_inj`.** No such lemma exists. The
   intended idiom is `apply/tuple_uniqP` (l. 356), which
   produces `injective (tnth t)` from `uniq t` and conversely.

3. **`'S_n` confused with the symmetric *set*.** `'S_n` is the
   `finGroupType`, *not* `Sym setT`. `Sym S` (l. 577) is a
   `{set {perm T}}`; `'S_n` is the type whose every term is a
   group element. Use `card_Sn` (l. 597) for `#\|'S_n\|`, *not*
   `cardsT` on `Sym setT`.

4. **`(s * t) x = s (t x)` (reversed).** `permM` (l. 128) is
   `(s * t) x = t (s x)`. `*` reads left-to-right as "do `s`
   first". When porting from textbooks that compose
   right-to-left, swap arguments before invoking `permM`.

5. **`perm` instead of `tperm` for transpositions.** `perm` (l. 76)
   is the *constructor* `(f, injf) -> {perm T}`; `tperm x y`
   (l. 221) is the *transposition*. Use `tperm` directly; it
   already comes with `tpermL`, `tpermR`, `tpermD`, `tpermK`,
   `tperm2`, `tperm_on`, `tpermJ`, `odd_tperm`.

6. **`'C(n, k)` for `k > n`.** Returns `0`, by definition
   (`bin_small`, l. 211). Do *not* add `m <= n` as a side
   condition unless the lemma actually demands it; many of the
   identities (`bin_sub`, l. 246; `bin_fact`, l. 224) do, but
   `binS`, `bin0`, `binn`, `expnDn`, `Vandermonde` do not.

7. **Reproving `expnDn` by induction on `n`.** Reviewers reject
   any new proof of the binomial theorem; rewrite by `expnDn`
   (l. 298) and proceed. Likewise `Vandermonde` (l. 312) for the
   convolution `'C(k, _) * 'C(l, _) = 'C(k+l, _)`.

8. **`Pascal` and `triangular_sum`.** Both are deprecated
   (mathcomp 2.3.0; `binomial.v` l. 286, l. 309). New code uses
   `expnDn` and `bin2_sum`.

9. **Hand-written `seq T` proofs of `card_uniq_tuples`-style
   facts.** The combinatorial characterizations in
   `binomial.v` 372-571 (`card_uniq_tuples`, `cards_draws`,
   `card_draws`, `card_ltn_sorted_tuples`, `card_sorted_tuples`,
   `card_ord_partitions`) cover most "count me a configuration"
   goals. Search before re-proving.

10. **`permE` to compute on `1` or `tperm`.** `permE` (l. 94) is
    a rewrite that requires the head to be `@perm T f f_inj`.
    For `1`, use `perm1` (l. 125); for `s * t`, use `permM`
    (l. 128); for `s^-1 (s x)`, use `permK` / `permKV` (l. 131,
    134); for `tperm x y z`, `case: tpermP` (l. 228) gives the
    three-way case-split. `rewrite permE` succeeds only when
    the goal still mentions a literal `perm f f_inj`.

### 46.9 Quick decision flow

```
Sized collection of T's, no arithmetic
    -> n.-tuple T;  access tnth t i, no default

Sized vector, want * : R / +%R / lmodType
    -> 'rV[R]_n;  access M 0 i, see §38

Sized list, induction over the size, varying length
    -> seq T;  use nth with a default, prove size by induction

Tuple equality
    -> apply: eq_from_tnth => i.    (* pointwise on 'I_n *)
    -> apply/eqP; rewrite eqEtuple. (* boolean form     *)

Tuple membership
    -> apply/tnthP; exists i.       (* x \in t  <-  x = tnth t i *)

Tuple uniqueness <-> tnth injectivity
    -> apply/tuple_uniqP.

Tuple as bigop index
    -> \sum_(t : n.-tuple T) F t;  card_tuple  -> #|T|^n

Permutation extensionality
    -> apply/permP => x.

Permutation parity
    -> rewrite odd_perm1 / odd_tperm / odd_permM / odd_permV / odd_permJ
    -> case: prod_tpermP for the "every perm is a product of tperms" form

Permutation in determinant
    -> reindex_perm s;  bigD1 (1 : 'S_n);  see §38.7

Permutation cardinality
    -> card_Sn  : #|'S_n| = n`!
    -> card_perm : #|perm_on A| = (#|A|)`!

Binomial identity
    head is 'C(_, 0), 'C(0, _), 'C(_, _) with args equal
        -> bin0 / bin0n / binn / bin1 / binSn
    head is 'C(n.+1, m.+1)
        -> binS  (Pascal recurrence)
    multiplicative, want to clear binomials
        -> bin_fact / bin_ffact / bin_factd / bin_ffactd
    symmetry
        -> bin_sub
    inside (a + b) ^ n
        -> expnDn  (NOT Pascal, deprecated)
    convolution sum
        -> Vandermonde
    triangular sum  \sum_(0 <= i < n) i
        -> bin2_sum  (NOT triangular_sum, deprecated)
    prime divides 'C(p, k)
        -> prime_dvd_bin

Counting finite configurations
    n-tuples with a predicate, all uniq
        -> card_uniq_tuples       (binomial.v 372)
    k-subsets of a set
        -> cards_draws / card_draws  (407, 452)
    sorted tuples
        -> card_ltn_sorted_tuples / card_sorted_tuples  (457, 484)
    ordinal partitions
        -> card_partial_ord_partitions / card_ord_partitions (529, 560)
```

### 46.10 Sources

- `mathcomp/boot/tuple.v` (header lines 11-55; `tuple_of`
  l. 61, `size_tuple` l. 69, `tnth_default` l. 72, `tnth_nth`
  l. 77, `tnth_onth` l. 80, `eq_from_tnth` l. 96, notations
  l. 109-127, `tcast` family l. 135-160, seq-builder
  `Canonical`s l. 173-237, `tnth0`/`tnthS`/`thead`/`tupleP`
  l. 239-260, `tnth_map`/`tnth_nseq` l. 262-268, `tuple_eta`
  l. 276, `tnth_lshift`/`tnth_rshift` l. 282-292, tuple
  quantifiers l. 300-316, `eqEtuple` l. 331, `tnthP` l. 344,
  `tuple_uniqP` l. 356, finite instance + `card_tuple`
  l. 420-423, `ord_tuple`/`tnth_ord_tuple` l. 429-436,
  `mktuple`/`tnth_mktuple` l. 451-454, notation `[tuple E | i < n]`
  l. 467).
- `mathcomp/fingroup/perm.v` (header lines 8-37; `perm_type`
  l. 49, `pval` l. 51, `{perm T}` l. 66, `'S_n` l. 73, `perm`
  constructor l. 76, `fun_of_perm` coercion l. 79-81, `permP`
  l. 88, `permE` l. 94, `perm_inj` l. 97, group operations
  `perm_one`/`perm_mul`/`perm_inv` and HB instance l. 104-123,
  `perm1`/`permM`/`permK`/`permKV`/`permJ`/`permX` l. 125-141,
  `perm_on` l. 155, `tperm` l. 221 + `tpermP` spec l. 228,
  `tperm*` family l. 231-260, `card_perm` l. 263, `reindex_perm`
  notation l. 294, `tuple_permP` l. 315, `aperm`/`porbit`/`porbits`
  l. 342-348, `odd_perm` l. 356 + parity family l. 503-565,
  `Sym` l. 577, `card_Sn` l. 597, `lift_perm` l. 605-665,
  `permS0`/`permS1`/`permS01` l. 670-677, `cast_perm` l. 681).
- `mathcomp/fingroup/fingroup.v` (group axioms `mulgA`/`mul1g`/
  `mulVg` at l. 262-264; their right-side companions `mulg1`/
  `mulgV` are derived later in the same file; `invgK` l. 282,
  `invMg` l. 288, `eq_mulgV1` l. 342). `'S_n` inherits *all* of
  these.
- `mathcomp/boot/binomial.v` (header lines 7-17; `n^_m` l. 124-127,
  factorial bridge `ffact_factd` l. 169, `binomial` l. 174-180,
  `'C(_, _)` notation l. 182, `binE`/`bin0`/`bin0n`/`binS`/`bin1`
  l. 184-199, `bin_gt0` l. 201, `bin_small` l. 211, `binn` l. 214,
  `mul_bin_diag` l. 218, `bin_fact`/`bin_factd`/`bin_ffact`/
  `bin_ffactd` l. 224-244, `bin_sub` l. 246, `mul_bin_down`/
  `mul_bin_left` l. 252-261, `binSn` l. 263, `bin2`/`bin2odd`
  l. 266-270, `prime_dvd_bin` l. 272, `bin2_sum` l. 279, `expnDn`
  l. 298, deprecated `Pascal` l. 309-310, `Vandermonde` l. 312,
  `prime_modn_expSn`/`fermat_little` l. 351-364, combinatorial
  characterizations l. 372-571).
- §34 (bigops: `reindex_inj`, `bigD1`, `partition_big`).
- §38 (matrix; uses `'S_n` in `\det` Leibniz formula, l. 3375).
- §40 (finset; `cards_draws`, `card_draws` are the bridge to `'C`).
- §41 (nat arithmetic; ``n`!``, factorial-binomial identities live
  in `div.v` and `binomial.v` jointly).

---

