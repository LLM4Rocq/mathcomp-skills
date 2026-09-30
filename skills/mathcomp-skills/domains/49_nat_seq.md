## 49. nat and seq Idioms (ssrnat, seq)

Files: `mathcomp/boot/ssrnat.v` and `mathcomp/boot/seq.v` (under
`boot/` since mathcomp 2.5.0; `ssreflect/` in 2.0-2.4). Import `all_boot`
(§3). div/gcd live in §41.3, bigops in §34, tuples in §46. Naming (§11):
nat operations carry an `n` suffix (`addn`, `muln`, `ltn`, `eqn`;
exceptions `leq`, `odd`, `double`, `half`, `factorial`); their views
append `P` (`leqP`, `ltnP`, `ltngtP`, `eqnP`). Contrast
the `r` suffix of ring lemmas (`addrC`).

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `leqP`, `ltnP`, `ltngtP` | case-split a nat comparison | §49.3, §28.1 |
| `ltnS`, `leqNgt`, `ltnNge` | trade `<` for `<=`; push `~~` through | §49.3 |
| `subnK`, `subnKC`, `subn_eq0` | cancel truncated subtraction | §49.2 |
| `addSn`, `addnS`, `mulSn` | expose a successor (`/=` will not) | §49.4 |
| `nth_map`, `nth_default` | `nth` through `map`; `nth` out of range | §49.5 |
| `size_map`, `size_cat` | sizes of built sequences | §49.5 |
| `mem_cat`, `mem_map`, `mem_filter`, `mem_undup` | membership in built sequences | §49.6 |
| `ltn_ind`, `ubnP` | strong / bounded induction | templates.md §21 |
| `ex_minnP`, `ex_maxnP` | least / greatest `n` with `P n` | §49.11 |
| `eqb0`, `leq_b1` | a `bool` used as a `nat` | §49.7 |

### 49.1 Reading the notation

(MCB §1.2.2-1.2.3, §1.7.) `mathcomp/boot/ssrnat.v`:

| Notation | Meaning |
|----------|---------|
| `n.+1`, `n.+2` | `succn n`, `succn (succn n)` |
| `n.-1` | `predn n`, saturating: `0.-1 = 0` |
| `n.*2` | `double n` |
| `n./2` | `half n` |
| ``n`!`` | `factorial n` |
| `%/`, `%%`, `%\|` | `divn`, `modn`, `dvdn` (div.v, §41.3) |
| `m < n` | notation for `m.+1 <= n` (boot/ssrnat.v:314) |
| `m > n`, `m >= n` | `(only parsing)` (boot/ssrnat.v:315), never printed |
| `a <= b < c`, `0 < m <= n`, … | chained forms are `&&` conjunctions |
| `ltn` | `[rel m n \| m < n]`, for `sort`/`sorted` |

`leq` (l. 311) is `m - n == 0`, so every nat comparison is a `leq` term.
`ltn` (l. 320) is only the relation-valued version.

- Write `n.+1`, not `S n` or `n + 1`. Lemmas are stated with `.+1`,
  and `n + 1` needs `addn1` first. Term-level style: §32.5.
- Nat numerals parse to `S (S …)` **syntactically**, so lemmas shaped
  `_.+1` rewrite numerals directly (`num3` below).
- State with `<`/`<=` (`0 < n`, named `n_gt0`), never `n > 0`: goals
  print the canonical form. Rule: §32.6.
- `==` on nat comes from `HB.instance Definition _ := hasDecEq.Build
  nat eqnP.` (boot/ssrnat.v:179). There is no raw notation on `eqn`.
- Destructure inline with `if n is p.+1 then … else …` (§32.5).

```coq
From mathcomp Require Import all_boot.

Lemma ltS m n : (m < n.+1) = (m <= n).
Proof. by []. Qed.  (* definitional: < is .+1 <= *)

Goal forall n, n > 0 -> n >= 1.
Proof. by []. Qed. (* goal prints as 0 < n -> 0 < n *)

Lemma num3 m : m + 3 = (m + 2).+1.
Proof. by rewrite addnS. Qed.  (* the numeral 3 is 2.+1 *)

Lemma pos_add1 n : 0 < n + 1.
Proof. Fail by []. by rewrite addn1. Qed.  (* n + 1 is not n.+1 *)

Definition non_zero (n : nat) : bool := if n is _.+1 then true else false.
```

### 49.2 Truncated subtraction

(MCB §1.2.3.) `m - n = 0` whenever `m <= n`; `leq m n` **is**
`m - n == 0`. `mathcomp/boot/ssrnat.v`:

| Lemma | Statement |
|-------|-----------|
| `subn_eq0` (l. 562) | `(m - n == 0) = (m <= n)` |
| `subnK` (l. 586) | `m <= n -> (n - m) + m = n` |
| `subnKC` (l. 580) | `m <= n -> m + (n - m) = n` |
| `leq_subLR` (l. 565) | `(m - n <= p) = (m <= n + p)` |
| `subnS` (l. 303) | `m - n.+1 = (m - n).-1` |
| `subSS` (l. 278) | `m.+1 - n.+1 = m - n` |
| `subSn` (l. 610) | `m <= n -> n.+1 - m = (n - m).+1` |
| `subn0` (l. 275), `sub0n` (l. 274), `subnn` (l. 276) | `n - 0 = n`, `0 - n = 0`, `n - n = 0` |
| `predn_sub` (l. 666) | `(m - n).-1 = m.-1 - n` |
| `prednK` (l. 350) | `0 < n -> n.-1.+1 = n` |

- Every `m - n` needs `n <= m` in context before it behaves like
  ring subtraction. Get it first, then `subnK`/`subnKC`/`addnBA`.
- `n.-1.+1 = n` is **never** true by computation: it needs `0 < n`
  (`prednK`).
- Many hypotheses are really subtraction bounds in disguise:
  `rewrite -subn_eq0` / `leq_subLR` turns one into the other.

```coq
From mathcomp Require Import all_boot.

Lemma sub_trunc m n : (m - n == 0) = (m <= n).
Proof. by rewrite subn_eq0. Qed.

Lemma sub_add m n : m <= n -> n - m + m = n.
Proof. exact: subnK. Qed.

Lemma sub_le m n p : n - m <= p -> n <= m + p.
Proof. by rewrite leq_subLR. Qed.

Lemma pred_succ n : 0 < n -> n.-1.+1 = n.
Proof. exact: prednK. Qed.   (* never by computation *)
```

### 49.3 Successor and strict order

(MCB §2.2.2, §2.3.3 for items 1-3 on `nat`; the Order/ssrnum remark,
the `andP` idioms and item 4 are not from the book.)

1. `h : m < n` **is** `m.+1 <= n`: `exact: h` works, and so does
   `leq_trans h`. In Order/ssrnum `<` is a separate `lt` and needs
   `ltW`, `lt_le_trans`, `le_lt_trans`. Do not apply nat lemmas to a
   `realType` or vice versa.
2. Chained notations are `&&`: split with `case/andP` or
   `/andP[h1 h2]`, build with `apply/andP; split`.
3. A hypothesis `k < 0` is `k.+1 <= 0`, i.e. `false`: `by []` or
   `rewrite ltn0 in h`. A *goal* `k < 0` is unprovable: recheck the
   case split.
4. Naming: nat lemmas are `leq_*`/`ltn_*` (`leq_add2l`, `ltn_subRL`);
   the ordered-type ones are `le_*`/`lt_*` and `ler_*`/`ltr_*`.

`mathcomp/boot/ssrnat.v`:

| Lemma | Statement / use |
|-------|-----------------|
| `ltnS` (l. 328) | `(m < n.+1) = (m <= n)` |
| `ltn0` (l. 331) | `n < 0 = false` |
| `leqnn` (l. 332), `ltnn` (l. 361) | `n <= n`, `n < n = false` |
| `leqNgt` (l. 353) | `(m <= n) = ~~ (n < m)` |
| `ltnNge` (l. 358) | `(m < n) = ~~ (n <= m)` |
| `leqn0` (l. 364) | `(n <= 0) = (n == 0)` |
| `eqn_leq` (l. 371) | `(m == n) = (m <= n <= m)` |
| `leq_eqVlt` (l. 392) | `(m <= n) = (m == n) \|\| (m < n)` |
| `ltn_neqAle` (l. 395) | `(m < n) = (m != n) && (m <= n)` |
| `leq_trans` (l. 398) | `m <= n -> n <= p -> m <= p`; pivot `n` first |
| `ltnW` (l. 404) | `m < n -> m <= n` |
| `leq_add2l` (l. 529) | `(p + m <= p + n) = (m <= n)` |
| `ltn_add2r` (l. 538) | `(m + p < n + p) = (m < n)` |

Case splits (full family and the `leP` warning: §28.1):

| Spec | Branches |
|------|----------|
| `leqP` (l. 922) | `m <= n` / `n < m`; also rewrites `minn`/`maxn` |
| `ltnP` (l. 933) | `m < n` / `n <= m` |
| `posnP` (l. 941) | `n = 0` / `0 < n` |
| `ltngtP` (l. 953) | `m < n` / `n < m` / `m = n` |

Pin the arguments (`case: (leqP m n)`) when the goal holds other
comparisons: bare `case: leqP` matches the first `leq` it finds.

```coq
From mathcomp Require Import all_boot.

Lemma lt_ex m n (h : m < n) : m.+1 <= n.
Proof. exact: h. Qed.

Lemma ex_chain m n : 0 < m <= n -> 0 < n.
Proof. by case/andP=> m_gt0 /(leq_trans m_gt0). Qed.

Lemma c1 m n : m <= n -> ~~ (n < m).
Proof. by rewrite -leqNgt. Qed.

Lemma k_lt0 k : k < 0 -> False.   (* k < 0 is k.+1 <= 0 *)
Proof. by []. Qed.

Lemma min_le m n : minn m n <= n.
Proof. by case: (leqP m n). Qed.  (* pin the args; rewrites minn *)

Lemma cmp3 m n : (m < n) || (m == n) || (n < m).
Proof. by case: ltngtP. Qed.
```

### 49.4 Computation vs rewriting on nat

Canonical home for the `simpl never` fact (a library fact: the
book's toy `addn`, MCB §1.5, still computes).

1. `Definition addn := plus.` then `Arguments addn : simpl never.`
   (`mathcomp/boot/ssrnat.v`, `addn` (l. 193)). Same for
   `subn` (l. 265), `muln` (l. 1100), `expn` (l. 1262),
   `factorial` (l. 1361) and `double` (l. 1437).
   `addn_rec`/`subn_rec`/`muln_rec` (and `expn_rec`, `fact_rec`,
   `double_rec`) are deprecated since 2.3.0.
2. So `/=`, `simpl` and `//=` do not expose a successor: `simpl`
   leaves `n.+1 + m = 0 -> False` unchanged. `simpl` may still fire
   when an outer `predn`/match forces the redex (`(n.+1 + m).-1`
   simplifies to `n + m`; cf. the `predn` example of MCB §1.5), so do
   not rely on either behaviour.
3. Rewrite instead:

   | Operator | Lemmas |
   |----------|--------|
   | `addn` | `addSn` (l. 204), `addnS` (l. 209), `add0n`, `addn0`, `addn1` |
   | `muln` | `mulSn` (l. 1112), `mulnS` (l. 1115), `muln0`, `muln1` |
   | `subn` | `subSS` (l. 278), `subnS` (l. 303) |
   | `expn` | `expnS` (l. 1272), `expn1` (l. 1271) |
   | `double` | `doubleS` (l. 1448) |

   Never `rewrite /addn` or `unfold plus`.
4. Conversion still works: `by []` closes goals that hold by
   computation (`n.+1 + m = (n + m).+1`). Try it before a rewrite
   chain (§22.1; MCB §2.2.1).
5. `leq` does not compute under `/=` either (`leq m n` is `m - n ==
   0`): `m.+1 <= n.+1` only *prints* as `m < n.+1`. Use `ltnS`, and
   `eqSS` for `m.+1 == n.+1`.
6. Goals with free variables: rewrites, or `zify; lia` in project
   code (§45.5).
7. Your own recursive definitions: §32.5 and §31.5.

```coq
From mathcomp Require Import all_boot.

Lemma pos_sum m n : 0 < m + n.+1.
Proof. Fail by []. by rewrite addnS. Qed.  (* plus recurses on m *)

Lemma succ_add n m : n.+1 + m = (n + m).+1.
Proof. by []. Qed.              (* conversion still works *)

Lemma le_SS m n p (h : m.+1 <= n.+1) : n <= p -> m <= p.
Proof. by rewrite ltnS in h; apply: leq_trans. Qed.
```

### 49.5 seq: lookups with defaults, comprehensions, core lemmas

(MCB §1.3.1-1.3.3, §1.6 for `iota`.) `mathcomp/boot/seq.v`:

| Notation | Meaning |
|----------|---------|
| `[::]`, `[:: a; b]`, `[:: a, b & s]`, `x :: s` | literals, cons |
| `s1 ++ s2` | `cat s1 s2` |
| `[seq E \| i <- s]` | `map (fun i => E) s` |
| `[seq i <- s \| P]` | `filter (fun i => P) s` |
| `[seq E \| i <- s & C]` | map over the filtered list |
| `iota m n`, `nseq n x`, `rev s` | `[:: m; …; m + n - 1]`, `n` copies of `x`, reversal |
| ``s`_i`` | `nth 0 s i` in `ring_scope` (§39) |

`nth x0 s i` and `head x0 s` always carry a default
(`Arguments nth : simpl nomatch`, boot/seq.v:949).

- `size s <= i`: the default comes out, `nth_default` (l. 387).
- `i < size s`: any default works. `nth_map` (l. 2503) takes **two**
  defaults: `nth x2 [seq f i | i <- s] n = f (nth x1 s n)`. Pick `x1`
  for the source type: `rewrite (nth_map x1)`.
- `set_nth_default y0 x0` (l. 1695; `s`, `n` implicit) rewrites
  `nth x0 s n = nth y0 s n` under `n < size s`.

| Lemma | Statement |
|-------|-----------|
| `size_map` (l. 2497) | `size (map f s) = size s` |
| `size_cat` (l. 311) | `size (s1 ++ s2) = size s1 + size s2` |
| `size_rev` (l. 904) | `size (rev s) = size s` |
| `size_iota` (l. 3026) | `size (iota m n) = n` |
| `nth_cat` (l. 409) | `nth x0 (s1 ++ s2) n = if n < size s1 then … else …` |
| `nth_iota` (l. 3035) | `i < n -> nth p (iota m n) i = m + i` |
| `mem_nth` (l. 1189) | `n < size s -> nth x0 s n \in s` (eqType) |
| `mem_iota` (l. 3040) | `(i \in iota m n) = (m <= i < m + n)` |
| `nth0` (l. 385), `nth_nil` (l. 394) | `nth x0 s 0 = head x0 s`, `nth x0 [::] n = x0` |
| `map_cat` (l. 2494), `filter_cat` (l. 564) | distribute over `++` |
| `foldr_cat` (l. 3172) | `foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1` |
| `last_cons` (l. 333) | `last x (y :: s) = last y s` |
| `rev_rcons` (l. 913) | `rev (rcons s x) = x :: rev s` |

- Induction on `s`: templates.md §21 (`elim: s => [|x s IHs]`,
  `elim/last_ind`, `last_ind` (l. 368)). Default vs `option` in your
  own definitions: §32.5.
- Search: `Search nth map.`, `Search size (_ ++ _).`

```coq
From mathcomp Require Import all_boot.

Lemma nth_succ (s : seq nat) i : i < size s ->
  nth 0 [seq x.+1 | x <- s] i = (nth 0 s i).+1.
Proof. by move=> ltis; rewrite (nth_map 0). Qed.

Lemma nth_out (s : seq nat) : nth 0 s (size s) = 0.
Proof. by rewrite nth_default. Qed.

Lemma nth_swap (s : seq nat) i : i < size s -> nth 0 s i = nth 1 s i.
Proof. exact: set_nth_default. Qed.
```

### 49.6 Membership in a seq (eqType)

(MCB §6.6.) Once `T` is an `eqType`, `\in` on `seq T` computes by
`==`. Unfold with `rewrite in_cons` or `rewrite !inE`, then
`/orP[/eqP->|]` (intent rows: phrasebook.md §17).
`mathcomp/boot/seq.v`:

| Lemma | Statement |
|-------|-----------|
| `in_cons` (l. 1136) | `(x \in y :: s) = (x == y) \|\| (x \in s)` |
| `mem_cat` (l. 1171) | `(x \in s1 ++ s2) = (x \in s1) \|\| (x \in s2)` |
| `mem_filter` (l. 1227) | `(x \in [seq x <- s \| a x]) = a x && (x \in s)` |
| `mem_map` (l. 2870) | `injective f -> (f x \in map f s) = (x \in s)` |
| `mem_rev` (l. 1280) | `rev s =i s` |
| `mem_undup` (l. 1391) | `undup s =i s` |
| `perm_mem` (l. 1890) | `perm_eq s1 s2 -> s1 =i s2` |
| `undup_uniq` (l. 1397) | `uniq (undup s)` |
| `cons_uniq` (l. 1321) | `uniq (x :: s) = (x \notin s) && uniq s` |
| `count_uniq_mem` (l. 1360) | `uniq s -> count_mem x s = (x \in s)` |
| `count_memPn` (l. 1357) | `reflect (count_mem x s = 0) (x \notin s)` |

- `mem_map` takes the injectivity proof first: `rewrite (mem_map
  f_inj)`. Bare `mem_map` leaves an `injective f` side goal.
- Statement choice: "same elements" is `s1 =i s2`; `perm_eq s1 s2`
  when multiplicities matter; `=` only for identical lists.
- Case split on membership: `case: ifP`, or
  `have [xs|xNs] := boolP (x \in s)`.
- `\in` needs the collection's type known: annotate `(s : seq T)`.
  The `pT of mem` error: errors.md §1.

```coq
From mathcomp Require Import all_boot.

Lemma cons_mem (x y : nat) (s : seq nat) :
  x \in y :: s -> x != y -> x \in s.
Proof. by rewrite in_cons => /orP[/eqP->|//]; rewrite eqxx. Qed.

Lemma memE (x : nat) (s : seq nat) : x \in rev (undup s) = (x \in s).
Proof. by rewrite mem_rev mem_undup. Qed.

Lemma mem_succ (s : seq nat) x :
  (x.+1 \in [seq y.+1 | y <- s]) = (x \in s).
Proof. by rewrite (mem_map succn_inj). Qed.

Lemma mem_dec (x : nat) (s : seq nat) : (x \in s) || (x \notin s).
Proof. by have [xs|xNs] := boolP (x \in s). Qed.
```

### 49.7 bool as nat

(MCB §5.5.) `Coercion nat_of_bool` (boot/ssrnat.v:1389) sends `true`
to `1` and `false` to `0`. `mathcomp/boot/ssrnat.v`:

| Lemma | Statement |
|-------|-----------|
| `leq_b1` (l. 1391) | `b <= 1` |
| `eqb0` (l. 1395) | `(b == 0 :> nat) = ~~ b` |
| `eqb1` (l. 1397) | `(b == 1 :> nat) = b` |
| `lt0b` (l. 1399) | `(b > 0) = b` |

- Use it for counting: `count`, `\sum_i (P i : nat)`, and `b%:R` in
  rings.
- `Set Printing Coercions` shows where `nat_of_bool` (and `is_true`)
  were inserted. bool vs Prop statements: §36.3, §36.7.

```coq
From mathcomp Require Import all_boot.

Lemma bool_nat (b : bool) : b <= 1.   (* b coerced to nat *)
Proof. by case: b. Qed.

Lemma count_ex (s : seq nat) x :
  uniq s -> count_mem x s = (x \in s).
Proof. exact: count_uniq_mem. Qed.

Lemma b_eq0 (b : bool) : (b == 0 :> nat) = ~~ b.
Proof. exact: eqb0. Qed.
```

### 49.8 Interop with the standard library and name hygiene

1. mathcomp nat relations are `bool` (`m <= n : bool`, used as a Prop
   through `is_true`; MCB §1.2.3, §1.7, §5.5). Stdlib's `le`/`lt` live in `coq_nat_scope`:
   `(m <= n)%coq_nat`.
2. Never cite `Nat.*`, `PeanoNat` or `Arith` lemmas in mathcomp goals.
   Search the mathcomp name (§37): `addnC`, not `Nat.add_comm`;
   `ltnn`, not `Nat.lt_irrefl`.
3. To consume a Stdlib fact, bridge with `move/ltP` / `apply/leP`:
   ssrnat's **reflection bridges** `leP` (l. 500) and `ltP` (l. 520).
   Write `ssrnat.leP` / `ssrnat.ltP` when `Order.TTheory` is imported
   (§28.1).
4. `lia` on mathcomp nat needs mczify: `From mathcomp Require Import
   zify.` (§45.5).
5. Never re-declare `bool`/`nat`/`seq`/`option`/`prod` or
   `addn`/`leq`/`size`/`map`/`foldr`/`iota`/`nth` (the book does, for
   pedagogy: MCB §1.2.3, §1.3, §1.4, §1.6). A variant gets a fresh name plus an equation to the
   library function: `my_addE : my_add =2 addn`.
6. Rocq 9 spells it `From Stdlib Require …` (not `Coq.`). If a Stdlib
   module is needed, import it **before** mathcomp so mathcomp's
   `nat_scope` notations win.
7. `addn` is literally `plus` (`addnE` (l. 199)), but statements use
   the mathcomp heads.

```coq
From Stdlib Require Import PeanoNat.  (* only if forced; BEFORE mathcomp *)
From mathcomp Require Import all_boot.

Lemma from_stdlib m n : (m < n)%coq_nat -> m < n.
Proof. by move/ltP. Qed.

Lemma no_Nat m n : m + n = n + m.
Proof. exact: addnC. Qed.   (* not Nat.add_comm *)

(* Fixpoint addn ... := ...   would shadow ssrnat.addn: never *)
Fixpoint my_add (m n : nat) : nat :=
  if m is m'.+1 then (my_add m' n).+1 else n.

Lemma my_addE : my_add =2 addn.
Proof. by elim=> // m IH n /=; rewrite IH. Qed.
```

### 49.9 Common pitfalls

(MCB §1.2.2-§1.2.3, §1.3.1, §1.7, §5.2.1; details in the cited
subsections.)

1. **`case: leP` on a nat comparison.** ssrnat's `leP` is a Stdlib
   bridge, and under `Order.TTheory` it is the order-type spec. Use
   `case: leqP` / `ltnP` / `ltngtP` (§49.3, §28.1).
2. **`n + 1` instead of `n.+1`.** `ltnS`, `addnS`, `big_ord_recr`
   match `.+1`; `n + 1` needs `rewrite addn1` first (§49.1).
3. **Expecting `/=` to expose a successor.** `addn`/`muln`/`subn`/
   `expn` are `simpl never`: `rewrite addSn`/`addnS`/`mulSn`, or
   `by []` (§49.4).
4. **`m - n` without `n <= m`.** Subtraction truncates; get the bound
   first, then `subnK`/`subnKC` (§49.2).
5. **`n > 0` in statements.** `>` is parse-only; state `0 < n` so the
   statement matches the printed goal (§49.1, §32.6).
6. **Wrong `nth` default.** Under `i < size s` the default is
   irrelevant; `nth_map` needs the **source** default,
   `rewrite (nth_map x1)` (§49.5).
7. **`mem_map` without injectivity.** `rewrite (mem_map f_inj)`, not
   bare `mem_map` (§49.6).
8. **`a && b && c` for 3+ conjuncts.** It parses left-nested, so
   `/and3P` does not match it. State `[&& a, b & c]` and split with
   `move=> /and3P[ha hb hc]` (§36.7, §37.13).
9. **Stdlib names and re-declared library names.** `Nat.add_comm`
   does not rewrite `addn`; a local `Fixpoint addn` shadows
   `ssrnat.addn`, and no ssrnat lemma applies to it (§49.8).

### 49.10 Quick decision flow

```
Goal on nat / seq.

  holds by computation?                 -> by []
  case split on a comparison?           -> case: leqP / ltnP / ltngtP
                                           (pin args: case: (leqP m n))
  successor hidden behind + or * ?      -> rewrite addSn / addnS / mulSn
  m.+1 <= n.+1 or m.+1 == n.+1 ?        -> rewrite ltnS / eqSS
  truncated subtraction?                -> subnK / subnKC / leq_subLR
  n.-1.+1 ?                             -> prednK (needs 0 < n)
  induction (plain/strong/bounded)?     -> templates.md §21
  least/greatest n with P n?            -> case: (ex_minnP exP) (§49.11)
  nth / head ?                          -> nth_map x1 / nth_default
  membership?                           -> inE, mem_cat, mem_map f_inj
  a bool used as a number?              -> eqb0 / eqb1 / leq_b1
  linear arithmetic with variables?     -> zify; lia (§45.5)
```

### 49.11 Least and greatest witnesses

(MCB §8.3: `find_ex_minn`, countable choice.) From `exP : exists n, P n`
with `P : pred nat`, ssrnat computes the least witness, and, given an
explicit bound, the greatest. No axiom, no choiceType instance.

`mathcomp/boot/ssrnat.v`:

| Name | Statement / use |
|------|-----------------|
| `find_ex_minn` (l. 985) | `{m \| P m & forall n, P n -> n >= m}` (sig2, `exP` implicit) |
| `ex_minn` (l. 996) | `ex_minn exP : nat`, the least `n` with `P n` |
| `ex_minnP` (l. 1001) | spec: `case: (ex_minnP exP) => m Pm m_min` gives `P m`, `forall n, P n -> m <= n` |
| `ex_maxn` (l. 1014) | `ex_maxn exP ubP : nat`, with `ubP : forall i, P i -> i <= b` |
| `ex_maxnP` (l. 1019) | spec: `case: (ex_maxnP exP ubP) => m Pm m_max` gives `P m`, `forall j, P j -> j <= m` |
| `eq_ex_minn` (l. 1029), `eq_ex_maxn` (l. 1035) | `P =1 Q` makes the two values equal (proofs irrelevant) |

Rule: for a minimal witness or a minimal counterexample, use
`case: ex_minnP`. `ex_minnP` is a spec (§28.1): `case:` on a goal that
mentions `ex_minn exP` replaces it by the fresh `m` everywhere.

- Not `xchoose` (choice.v) or `cid` (classical/boolp.v:80, an
  axiom): both give *a* witness with no minimality, and `cid` drags in
  the boolp axioms.
- Not a hand-rolled `elim/ltn_ind` (templates.md §21) that re-derives
  minimality: it is `ex_minnP` re-proved in every file.
- Minimal counterexample: apply `ex_minnP` to `exists n, ~~ P n`; the
  bound `m_min` then says every `k < m` satisfies `P`.
- `ex_maxn` needs **both** `exP` and an upper bound `ubP`; for "largest
  `n <= b` with `P n`", bound the predicate itself
  (`[pred n | P n & n <= b]`, or `P n && (n <= b)`).

```coq
From mathcomp Require Import all_boot.

Lemma least_witness (P : pred nat) : (exists n, P n) ->
  exists2 m, P m & forall n, P n -> m <= n.
Proof. by move=> exP; case: (ex_minnP exP) => m Pm mmin; exists m. Qed.

(* minimal counterexample: everything below it satisfies P *)
Lemma least_counterexample (P : pred nat) : (exists n, ~~ P n) ->
  exists2 m, ~~ P m & forall k, k < m -> P k.
Proof.
move=> exNP; case: (ex_minnP exNP) => m NPm m_min; exists m => // k.
by apply: contraTT => /m_min; rewrite leqNgt.
Qed.

(* greatest witness below an explicit bound b *)
Lemma greatest_below (P : pred nat) b : P 0 ->
  exists2 m, P m && (m <= b) & forall n, P n -> n <= b -> n <= m.
Proof.
move=> P0; have exQ : exists n, P n && (n <= b) by exists 0; rewrite P0.
have ubQ n : P n && (n <= b) -> n <= b by case/andP.
case: (ex_maxnP exQ ubQ) => m Qm m_max; exists m => // n Pn nb.
by apply: m_max; rewrite Pn.
Qed.

(* ex_minn in a statement: case: ex_minnP abstracts it *)
Lemma ex_minn_le (P : pred nat) (exP : exists n, P n) n :
  P n -> ex_minn exP <= n.
Proof. by case: ex_minnP => m _ /[apply]. Qed.
```

### 49.12 Sources

- `mathcomp/boot/ssrnat.v`: `addn` (l. 193), `leq` (l. 311),
  `leqP` (l. 922), `ltngtP` (l. 953), `ex_minnP` (l. 1001); other
  lemma sites cited inline above.
- `mathcomp/boot/seq.v`: `nth` (l. 378), `nth_map` (l. 2503),
  `mem_map` (l. 2870); other lemma sites cited inline above;
  `mathcomp/boot/eqtype.v` (`eqType`, `==`).
- Assia Mahboubi and Enrico Tassi, *Mathematical Components*, Zenodo,
  2022 (draft v1.0.2), doi:10.5281/zenodo.3999478 (MCB ch. 1-2,
  MCB §5.2.1, MCB §5.5, MCB §6.6, MCB §8.3). The book targets Coq 8 /
  mathcomp 1.x; read §48 before reusing its code.
- Cross-references: §11 (suffixes), §28 (case analysis), §29 (rewriting),
  §32 (definitions, notations), §34 (bigops), §41 (div/gcd, int),
  §45 (`zify`/`lia`), §46 (tuples), templates.md §21 (induction).

---

