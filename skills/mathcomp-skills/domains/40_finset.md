## 40. Finset Idioms

The `finset` library (`mathcomp/boot/finset.v`, ~2780 lines) builds
finite sets `{set T}` over a `finType T` as a thin wrapper around
`{ffun T -> bool}`. Reviewers consistently flag two regressions on
finset goals: (1) hand-unfolding `\in` with `unfold`, when the
`inE` multirule normalises in one tactic; and (2) reaching for
`apply: setP` then case-analysing `=i` instead of going through
the `apply/setP => x` + boolean reflection idiom. This section
codifies the canonical reasoning patterns.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `inE` | normalise any `x \in <set-builder>` in one rewrite | §40.2 |
| `setP` | reduce `A = B` to pointwise membership (`=i`) | §40.3, §40.5 |
| `in_setU`, `in_setI`, `in_setD` | single-step membership for `:\|:`/`:&:`/`:\:` | §40.3 |
| `subsetP` | prove `A \subset B` pointwise | §40.3, §40.6 |
| `eqEsubset` | split set equality into mutual subset | §40.3, §40.5 |
| `cardsU`, `cardsT`, `cards0` | cardinality of union / full / empty | §40.3, §40.7 |
| `bigcupP`, `bigcapP` | reflect membership in `\bigcup` / `\bigcap` | §40.3, §40.4 |

### 40.1 Reading the notation

`{set T}` is a `finType` itself (since `T` is finite, so is its
power-set). Membership lives in `bool`, set equality reduces to
`=i`, and every operator unfolds to a set-builder over a `pred T`.

| Syntax | Meaning | Defining lemma |
|--------|---------|----------------|
| `{set T}` | finite sets over `T : finType` (l. 154) | `set_of T` |
| `[set x : T \| P x]` | comprehension (l. 186) | `in_set` (l. 225) |
| `[set x \| P x]` | same, `T` inferred (l. 188) | -- |
| `[set x in A]` | restrict to a set/pred `A` (l. 190) | -- |
| `[set x in A \| P x]` | restrict and filter (l. 200) | -- |
| `set0` / `setT` / `[set: T]` | empty / full (l. 233-234, 254) | `in_set0`, `in_setT` |
| `[set a]` | singleton (l. 259, 275) | `in_set1` (l. 373) |
| `[set a; b]` | doubleton (l. 282) | `in_set2` (l. 441) |
| `a \|: A` | `[set a] :\|: A` (l. 280) | `in_setU1` (l. 390) |
| `A :\|: B` | union (l. 279) | `in_setU` (l. 453) |
| `A :&: B` | intersection (l. 284) | `in_setI` (l. 520) |
| `~: A` | complement (l. 285) | `in_setC` (l. 602) |
| `A :\: B` | difference (l. 288) | `in_setD` (l. 649) |
| `A :\ a` | `A :\: [set a]` (l. 289) | `in_setD1` (l. 424) |
| `f @: A` | direct image (l. 1143) | `imsetP` (l. 1240) |
| `f @^-1: A` | preimage (l. 1142) | -- |
| `[set:: s]` | `seq`-to-set coercion (l. 207) | `set_seq*` (l. 393-398) |
| `#\|A\|` | cardinality (inherited from `fintype`) | `cardsE` (l. 731) |
| `\bigcup_(i in A) F i`, `\bigcap_(i in A) F i` | bigops over sets (l. 1769-1818) | -- |

The sentinel notations `[set: T]` (square form) and `setT`
(definition form) are interchangeable; reviewers prefer the bracket
form when `T` must be made explicit and the bare `setT` otherwise.

### 40.2 The `inE` multirule: the cornerstone

The single most useful tactic on a finset goal is `rewrite !inE`.
It is a *multirule*: an iterated tuple chained at l. 376:

```coq
Definition inE := (in_set, in_set1, inE).   (* finset.v l. 376 *)
```

(this is glued onto the earlier `inE` from `eqtype.v` and
`fintype.v`, which already covers `in_cons`, `in_nil`, `in_seq1`,
`mem_filter`, ...). Calling `rewrite !inE` thus repeatedly unfolds
every `\in` against every set-builder and seq constructor in scope,
leaving a pure boolean goal over `==` / `&&` / `||` ready for
`case`/`apply`/`/andP`.

```coq
(* Goal: x \in (a |: (A :&: B)) :\: [set b] *)
rewrite !inE.
(* Goal: (x != b) && ((x == a) || ((x \in A) && (x \in B))) *)
```

When *not* to use `rewrite !inE`:

- A *single* membership step is enough: prefer the named lemma
  (`in_setU`, `in_setI`, `in_setD`, `in_setC`, `in_setU1`,
  `in_setD1`, `in_set2`). It produces a smaller term and keeps
  intermediate goals readable.
- The goal is already in boolean normal form: `!inE` is a no-op
  but it churns the proof script.
- A `\subset` is the head: rewrite `subsetP` first, then `inE`
  inside the introduced membership (§40.6).

#### Anti-pattern: `inE` right-to-left

```coq
(* WRONG -- inE is a multi-rule; right-to-left is not predictable *)
rewrite -inE.

(* RIGHT -- pick the specific lemma *)
rewrite -in_setU.
```

(analysis PR #410: *"`inE` should never be used with
`-` (right to left), this is not supposed to be predictable."*
Cross-ref §29.4.)

### 40.3 Core lemma family

Verified against `mathcomp/boot/finset.v` at line numbers shown.
Membership lemmas (`in_set*`) state the boolean unfolding;
view-style lemmas (`set*P`) reflect the same fact into `Prop`.

| Lemma | Line | Statement (sketch) |
|-------|------|--------------------|
| `in_set` | 225 | `x \in finset pA = pA x` (the master rule) |
| `setP` | 228 | `A =i B <-> A = B` (extensionality) |
| `eqEsubset` | 297 | `(A == B) = (A \subset B) && (B \subset A)` |
| `in_setT` | 236 | `x \in setT` |
| `in_set0` | 327 | `x \in set0 = false` |
| `in_set1` | 373 | `(x \in [set a]) = (x == a)` |
| `set1P` | 367 | `reflect (x = a) (x \in [set a])` |
| `in_setU` | 453 | `(x \in A :\|: B) = (x \in A) \|\| (x \in B)` |
| `setUP` | 450 | reflect form of `in_setU` |
| `in_setU1` | 390 | `(x \in a \|: B) = (x == a) \|\| (x \in B)` |
| `in_setI` | 520 | `(x \in A :&: B) = (x \in A) && (x \in B)` |
| `setIP` | 517 | reflect form of `in_setI` |
| `in_setC` | 602 | `(x \in ~: A) = (x \notin A)` |
| `in_setD` | 649 | `(x \in A :\: B) = (x \notin B) && (x \in A)` |
| `in_setD1` | 424 | `(x \in A :\ b) = (x != b) && (x \in A)` |
| `set_seq1`, `set_cons`, `set_nil` | 393-398 | `[set:: s]` recursion |
| `set_enum` | 348 | `[set x \| x \in enum A] = A` |
| `subsetP` | fintype 582 | `reflect {subset A <= B} (A \subset B)` |
| `subset_trans` | fintype 661 | transitivity of `\subset` |
| `subxx` | fintype 611 | reflexivity (`subset_refl` is its alias) |
| `subsetIl`, `subsetIr` | 801-804 | `A :&: B \subset A` / `B` |
| `subsetUl`, `subsetUr` | 807-810 | `A \subset A :\|: B` |
| `subsetU` | 907 | `(A \subset B) \|\| (A \subset C) -> A \subset B :\|: C` |
| `subsetI` | 886 | `(A \subset B :&: C) = (A \subset B) && (A \subset C)` |
| `subUset` | 904 | dual: `(B :\|: C \subset A) = ...` |
| `cards0` | 740 | `#\|set0\| = 0` |
| `cards1` | 758 | `#\|[set x]\| = 1` |
| `cards2` | 788 | `#\|[set a; b]\| = (a != b).+1` |
| `cardsT` | 770 | `#\|setT\| = #\|T\|` |
| `cardsU` | 764 | `#\|A :\|: B\| = #\|A\| + #\|B\| - #\|A :&: B\|` |
| `cardsUI` | 761 | additive form: `#\|U\| + #\|I\| = #\|A\| + #\|B\|` |
| `cardsI` | 767 | dual of `cardsU` |
| `cardsD` | 776 | `#\|A :\: B\| = #\|A\| - #\|A :&: B\|` |
| `cardsC` | 779 | `#\|A\| + #\|~: A\| = #\|T\|` |
| `cardsCs` | 782 | `#\|A\| = #\|T\| - #\|~: A\|` |
| `cardsU1` | 785 | `#\|a \|: A\| = (a \notin A) + #\|A\|` |
| `cardsD1` | 794 | `#\|A\| = (a \in A) + #\|A :\ a\|` |
| `bigcup_seq` | 1879 | `\bigcup_(i <- r) F i = \bigcup_(i in r) F i` |
| `bigcap_seq` | 1926 | dual for `\bigcap` |
| `bigcupP` | 1833 | `reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i \| P) F i)` |
| `bigcapP` | 1906 | `reflect (forall i, P i -> x \in F i) ...` |
| `set_partition_big` | 2235 | sum over a partition |
| `partition_disjoint_bigcup` | 2239 | sum over a `trivIset`-indexed bigcup |

Two name patterns dominate: `in_<setOp>` for the boolean
membership unfolding (used by `inE`), and `<setOp>P` for the
`reflect` view (used with `apply/.../[]`). When you introduce a
new set operator, both forms are expected.

### 40.4 `\bigcup` and `\bigcap` over sets

`\bigcup_(i in A) F i` and `\bigcap_(i in A) F i` are bigops
in the `setU` / `setI` monoid; everything from §34 applies, with
`set0` / `setT` as the identity. The four ranges that actually
appear in practice:

```coq
\bigcup_(i in A) F i      (* i : I, restricted to i \in A *)
\bigcup_(i | P i) F i     (* whole finType, predicate filter *)
\bigcup_(i <- r) F i      (* i ranges over a seq r *)
\bigcup_i F i             (* whole finType *)
```

Membership goes through reflection, never through `unfold`:

```coq
(* RIGHT -- reflect view *)
move=> /bigcupP[i Pi xFi].

(* WRONG -- unfolds an opaque fold *)
rewrite /index_enum -enumT.
```

The conversion to a boolean fold (e.g. for `card_partition`) goes
via `bigcup_seq` and `bigcap_seq`; never `unlock` the bigop.

For sums *over* a partition, the canonical lemma is
`set_partition_big` (l. 2235), or `partition_disjoint_bigcup`
(l. 2239) when the index is indexed by a `trivIset`. These are the
finset analogues of `partition_big` (§34.6).

### 40.5 Set extensionality: `apply/setP`

```coq
(* RIGHT -- pointwise, drop into bool *)
apply/setP => x.
rewrite !inE.
(* Goal: x \in A = x \in B in bool *)
```

`setP` (l. 228) is `A =i B <-> A = B`. The `apply/setP` form
introduces a fresh `x`, leaving a bool-shaped goal. Two
common chained variants:

```coq
apply/eqP/setP => x; ...        (* go through ==, useful when P(A == B) *)
rewrite eqEsubset; apply/andP; split; apply/subsetP => x ...
                                (* via mutual subset (l. 297) *)
```

When the two sides differ only by predicate rewriting, `apply:
eq_set => x` (often via `eq_finset`, l. 242) is a one-liner
without going through `setP`.

### 40.6 Subset reasoning

Two complementary modes:

```coq
(* Pointwise *)
apply/subsetP => x xinA.
(* Goal: x \in B *)

(* Algebraic *)
apply: subset_trans; first exact: subsetIl.
exact: subsetUl.
```

Use `subsetP` (l. fintype 582) when the proof is a chain of `inE`
unfoldings; use the algebraic family
(`subsetIl`/`subsetIr`/`subsetUl`/`subsetUr`/`subsetU`/`subsetI`)
when the goal matches a structural shape. A typical hybrid:

```coq
apply/subsetP => x; rewrite !inE => /andP[xA xB].
by rewrite xA xB.
```

Closure of `\subset` under operations (`setUSS`, l. 468; `setISS`,
l. 535; `setDSS`, l. 661; `setCS`, l. 620) lets you propagate a
subset hypothesis without ever unfolding.

### 40.7 Cardinality: stay in the algebra

Reviewers flag manual recursion over a `seq` enumeration when a
`cards*` lemma applies. Decision flow:

| Goal head | Lemma to reach for |
|-----------|--------------------|
| `#\|A :\|: B\|` | `cardsU` (or additive `cardsUI`) |
| `#\|A :&: B\|` | `cardsI` |
| `#\|A :\: B\|` | `cardsD`, or `cardsDS` (l. 869) when `B \subset A` |
| `#\|~: A\|` | `cardsC` / `cardsCs` |
| `#\|setT\|` | `cardsT` (-> `#\|T\|`) |
| `#\|set0\|` | `cards0` (-> `0`) |
| `#\|[set a]\|` | `cards1` |
| `#\|a \|: A\|` | `cardsU1` (case-splits on `a \in A`) |
| `#\|A :\ a\|` | `cardsD1` (rearranged: `#\|A\| = (a \in A) + #\|A :\ a\|`) |
| `#\|f @: D\|` | `card_in_imset` (l. 1694), `card_imset` (l. 1697) |
| `#\|powerset A\|` | `card_powerset` (l. 1743): `2 ^ #\|A\|` |
| `\sum_(B in P) #\|B\|` over partition `P` | `card_partition` (l. 2180) |

`cardsUI` is the additive symmetry of `cardsU` and is what you
want when both sides need rearranging.

### 40.8 `partition_big` family on `{set T}`

The set-flavoured partition lemmas live at finset.v 2231-2239.
They are the canonical entry points for "sum over a set,
partitioned along a predicate":

```coq
Lemma set_partition_big_cond P D (K : pred T) (E : T -> R) :
  partition P D ->
  \big[op/idx]_(x in D | K x) E x =
  \big[op/idx]_(B in P) \big[op/idx]_(x in B | K x) E x.
                                        (* finset.v l. 2231 *)

Lemma partition_disjoint_bigcup (F : I -> {set T}) E :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  \sum_(x in \bigcup_i F i) E x = \sum_i \sum_(x in F i) E x.
                                        (* finset.v l. 2239 *)
```

`partition P D` is itself a `&&`-conjunction of `cover P == D`,
`trivIset P`, and `set0 \notin P` (l. 1991), so a partition
hypothesis decomposes via `case/and3P` -- see §28. For the
bigop-side analogue (`partition_big`, indexed by a function), see
§34.6.

### 40.9 Set comprehensions vs. predicates

`{set T}` and `{pred T}` look interchangeable but have different
algebras: predicates are `T -> bool`, sets are bundled finite
data. Conversions:

| Direction | How | When |
|-----------|-----|------|
| pred to set | `[set x \| P x]` (l. 186) | want `#\|...\|`, `\subset`, `\bigcup` |
| set to pred | `mem A` (auto-coerced) | want `{in A, ...}`, `all (in A) s` |
| seq to set | `[set:: s]` (l. 207) | indexing a finset over an enumeration |
| set to seq | `enum A` (`fintype`) | iterating, `perm_eq` reasoning |

`set_enum` (l. 348) and `enum_set0` / `enum_set1` / `enum_setT`
(l. 351, 384, 370) provide the round-trip equations.

### 40.10 Common pitfalls

1. **`rewrite -inE`** -- forbidden. The multirule is a tuple; the
   right-to-left direction picks an unspecified component
   (analysis PR #410). Use `-in_set`, `-in_setU`,
   `-in_setI`, etc.

2. **Confusing `\in` with `\subset`**. `x \in A` is membership of
   one element, `[set x] \subset A` is subset of a singleton.
   `sub1set` (l. 825) bridges the two:
   `([set x] \subset A) = (x \in A)`.

3. **Re-proving cardinality lemmas**. Anything stated in §40.7 is
   already there. A goal `#\|A :\|: B\| = ...` where the rhs has
   a subtraction asks for `cardsU`, not a manual induction. When
   `A` and `B` are disjoint, follow with `disjoint_setI0`
   (l. 945) to kill the `:&:` term.

4. **`setT_eq0` confusion**. There is no such lemma:
   `setT` and `set0` are *opposites*. The theorem names are
   `set_0Vmem` (l. 342: `(A = set0) + {x \| x \in A}`),
   `cards0_eq` (l. 755: `#\|A\| = 0 -> A = set0`), and
   `set0Pn` (l. 746: `reflect (exists x, x \in A) (A != set0)`).

5. **Using `apply: setP` then unfold**. The pointwise idiom is
   `apply/setP => x; rewrite !inE`, *not* `apply: setP =>
   /forallP h; ...`. The view-form `apply/setP` is what reviewers
   expect.

6. **`unlock` on a bigop / set**. `{set T}` and the `\bigcup`
   notations are HB-locked. `rewrite -[A]/(_)` and friends will
   not unfold the head; use the named `in_set*` and `bigcupP` /
   `bigcapP` lemmas. Cross-ref §34: `unlock` on `\big` is
   similarly forbidden.

7. **`subset_refl` vs `subxx`**. The reflexivity lemma in
   `fintype.v` is `subxx` (l. 611); `subset_refl` is a
   non-mathcomp alias and breaks `Search subxx`. Use `subxx`.

8. **`finType` overhead in lemma statements**. A lemma about
   `{set T}` already requires `T : finType`; do not also assume
   `eqType` or `choiceType` (cross-ref §36.2) -- they are
   subsumed.

### 40.11 Quick decision flow

```
Goal involves {set T}, \in, \subset, or #|...|.

  Membership in a set-builder?
    -> rewrite !inE        (multi-rule)
    -> rewrite in_setU     (single step, named lemma)

  Set equality?
    -> apply/setP => x; rewrite !inE     (pointwise)
    -> rewrite eqEsubset; apply/andP; split   (mutual subset)

  Subset?
    -> apply/subsetP => x xinA           (pointwise)
    -> exact: subsetIl / subsetUl / setUSS / setISS  (algebraic)

  Cardinality?
    -> see table in 40.7; never recurse on enum A by hand

  Bigop over a set / partition?
    -> bigcupP / bigcapP for membership
    -> set_partition_big / partition_disjoint_bigcup
    -> bigcup_seq / bigcap_seq to drop into seq form

  Reflection on emptiness?
    -> set0Pn (exists x, x \in A)
    -> set_0Vmem (constructive case-split)
```

### 40.12 Sources

`mathcomp/boot/finset.v` (file header lines 1-95; lemma sites
cited inline in 40.3); `mathcomp/boot/fintype.v` (`subsetP`
l. 582, `subxx` l. 611, `subset_trans` l. 661); analysis PR #410
(`inE` not right-to-left; cross-ref §29.4); analysis
PR #162 (`predeqE` over manual extension); MathComp
Book chapter 7 ("Finite Sets"). For bigops over sets see §34;
for the `reflect` /`==` view discipline see §28 and §36; for
naming of new `in_<op>` / `<op>P` pairs see §10 and §11.

---

