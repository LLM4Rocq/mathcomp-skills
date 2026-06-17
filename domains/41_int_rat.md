## 41. Integer, Rational, and Modular Idioms

Mathcomp factors integer and rational arithmetic across four files:
`mathcomp/boot/div.v` (nat division and gcd, the foundational layer),
`mathcomp/algebra/ssrint.v` (signed integers `int`),
`mathcomp/algebra/intdiv.v` (Euclidean division for `int`), and
`mathcomp/algebra/rat.v` (the rational field). The naming follows the
abbreviation table of §11: an `n` suffix targets `nat`, a `z` suffix
targets `int`, a `q` suffix targets `rat`. Three families of names
exist for what looks like one operation; reviewers reject the wrong
one even when its statement is provably equal to the right one.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `Posz` / `Negz`, `n%:Z` | cast `nat` to `int`; pin an integer literal | §41.1 |
| `eqz_nat`, `natz`, `intz` | bridge `nat`/`int` equality and casts | §41.1 |
| `divn_eq`, `modn_small` | unconditional `nat` division identity / bound | §41.3 |
| `divz_eq`, `divz_nat`, `modz_nat` | `int` division; pull back to `nat` | §41.4 |
| `n%:Q`, `numq`, `denq`, `numqE` | build / project a `rat`; numerator bridge | §41.2 |
| `ratr` | embed `rat` into a `realType` for analysis | §41.2 |
| `Gauss_dvdr`, `coprime1n` | coprimality-driven divisibility | §41.3 |

### 41.1 The `int` type and the `Posz` / `Negz` distinction

`mathcomp/algebra/ssrint.v` line 70:

```coq
Variant int : Set := Posz of nat | Negz of nat.
```

`Posz n` is the non-negative integer `n`; `Negz n` is `-(n+1)`, so
`Negz 0 = -1`. Both constructors take a `nat`, *not* an `int`; this
is the root cause of most cast confusion. `Posz` is a registered
**coercion** — two terms can display identically while not being
convertible (e.g. `Posz (x - y)` vs. `Posz x - Posz y` for `x y : nat`).

Three notations cast `nat` -> `int`, all valued in `int`:

| Notation | Meaning | When to use |
|----------|---------|-------------|
| `n%:Z` | `Posz n` (`ssrint.v` l. 75-76) | Pin an integer literal as `int`; clarify a coerced `nat` |
| `n%:R` | image of `n : nat` in any ring | Generic ring goal; `Lemma natz` (l. 630) bridges |
| `n%:~R` | image of `n : int` in any ring (`ssrint.v` l. 525) | When the source is already `int` |

Identities that are *propositional*, not definitional:

```coq
natz   : n%:R = n%:Z       :> int       (* l. 630 *)
intz   : n%:~R = n         :> int       (* l. 627 *)
NegzE  : Negz n = - n.+1%:Z              (* l. 241 *)
PoszD  : {morph Posz : m n / (m + n)%N >-> m + n}  (* l. 239 *)
PoszM  : {morph Posz : m n / (m * n)%N >-> m * n}  (* l. 346 *)
eqz_nat: (m%:Z == n%:Z) = (m == n)%N    (* l. 117 *)
```

`absz` (`ssrint.v` l. 394) projects `int -> nat`:

```coq
Definition absz m := match m with Posz p => p | Negz n => n.+1 end.
Notation "`| m |" := (absz m) : nat_scope.    (* l. 397 *)
```

`abszE : `|m| = `|m|%R :> int` (l. 1535) bridges `absz` and the
`Num.norm` from `realDomainType`. Use `absz` (head: `nat`) when you
will feed the result to `gcdn`/`%|`/`coprime`; use `` `|_|%R `` (head:
`int`) when staying in the ordered ring.

There is no `Posz_inj` lemma — `Posz` is a constructor and
injectivity comes for free from `case`/`congr`. Equivalently, prefer
the *boolean* form `eqz_nat` and reflect:

```coq
(* WRONG -- searching for a Posz_inj that does not exist *)
move/Posz_inj=> ->.

(* RIGHT *)
move=> /eqP; rewrite eqz_nat => /eqP ->.
```

### 41.2 The `rat` type

`mathcomp/algebra/rat.v` lines 41-44:

```coq
Record rat : Set := Rat {
  valq : (int * int);
  _ : (0 < valq.2) && coprime `|valq.1| `|valq.2|
}.
```

A `rat` is a **canonicalized** pair `(num, den)` with `den > 0` and
`gcd |num| |den| = 1`; the proof is bundled. Two notations matter:

| Notation | Meaning |
|----------|---------|
| `n%:Q` | `(n : int)%:~R : rat`, the cast `int -> rat` (l. 524) |
| `[rat x // y]` | smart constructor, `x / y` as a `rat` (printing only) |

The two projections:

```coq
Definition numq x := (valq x).1.    (* l. 57 *)
Definition denq x := (valq x).2.    (* l. 58 *)
Arguments numq : simpl never.
Arguments denq : simpl never.
```

Their core invariants (`Hint Resolve`d globally):

```coq
denq_gt0   : 0 < denq x                     (* l. 62 *)
denq_neq0  : denq x != 0                    (* l. 70 *)
coprime_num_den : coprime `|numq x| `|denq x|  (* l. 77 *)
numqE      : (numq x)%:~R = x * (denq x)%:~R   (* l. 630 *)
divq_num_den : (numq x)%:Q / (denq x)%:Q = x   (* l. 582 *)
rat_eqE    : (x == y) = (numq x == numq y) && (denq x == denq y)
```

`rat` is **not** a constructor-level fraction notation (`a # b` does
not exist for `rat`; that pattern belongs to ZArith). Build a `rat`
by division:

```coq
(* WRONG -- there is no `a # b` constructor *)
Check (3 # 4)%Q.

(* RIGHT *)
Check (3%:Q / 4%:Q).        (* via division on rat *)
Check (3 / 4)%Q.            (* same, in rat_scope *)
```

`ratr` (l. 838) is the generic embedding `rat -> R` for any
`unitRingType R`; analysis lemmas about reals applied to rational
arguments go through `ratr`:

```coq
ratr_int : ratr z%:~R = z%:~R    (* l. 840 *)
ratr_nat : ratr n%:R  = n%:R     (* l. 843 *)
```

`ratzE` (l. 539) and the file's own comments flag two anti-patterns:
`ratz n` and bare `fracq` should *never* appear in proof goals — their
canonical forms are `n%:Q` and `_%:Q / _%:Q`.

When to use `rat` vs. a `realType`: `rat` is exact, decidable,
countable, computable. `realType` (mathcomp-analysis) is uncountable,
classical, and supports `lim`/`exp`/`integral`. Picking `rat` is the
right move only when (i) every value in the proof is a
finitely-presented rational, *and* (ii) you will never call an
analytic lemma on it. Otherwise embed via `ratr`.

### 41.3 Natural-number division and gcd (`div.v`)

`mathcomp/boot/div.v` defines the foundational division on `nat`:

```coq
Notation "m %/ d" := (divn m d) : nat_scope.     (* l. 61 *)
Notation "m %% d" := (modn m d) : nat_scope.     (* l. 69 *)
Notation "m %| d" := (dvdn m d) : nat_scope.     (* l. 345 *)
Notation "m = n %[mod d]"  := (m %% d = n %% d) : nat_scope.   (* l. 70 *)
Notation "m == n %[mod d]" := (m %% d == n %% d) : nat_scope.  (* l. 71 *)
```

Two key conventions: `m %/ 0 = 0` (l. 88), `m %% 0 = m` (l. 90); the
"funny" boundary is chosen so `divn_eq` holds **unconditionally**.
`m %% d < d` requires `0 < d` (l. 134, `ltn_mod`).

| Lemma | Statement |
|-------|-----------|
| `divn_eq` (l. 84) | `m = m %/ d * d + m %% d` |
| `modn_def` (l. 75) | `m %% d = (edivn m d).2` -- unfold to `edivn` |
| `divnK` (l. 399) | `d %\| m -> m %/ d * d = m` |
| `modn_mod` (l. 257) | `m %% d = m %[mod d]` |
| `modn_small` (l. 254) | `m < d -> m %% d = m` |
| `modnDl/r` (l. 283/286) | `d + m = m %[mod d]`, `m + d = m %[mod d]` |
| `modnMDl` (l. 260) | `p * d + m = m %[mod d]` |
| `muln_modr` (l. 266) | `p * (m %% d) = (p * m) %% (p * d)` |
| `muln_modl` (l. 272) | `(m %% d) * p = (m * p) %% (d * p)` |
| `modnMm` (l. 321) | `m %% d * (n %% d) = m * n %[mod d]` |
| `eqn_mod_dvd` (l. 515) | `n <= m -> (m == n %[mod d]) = (d %\| m - n)` |
| `gcdnE` (l. 588) | `gcdn m n = if m == 0 then n else gcdn (n %% m) m` |
| `gcdnC`, `gcdnA` (l. 600, 754) | commut., assoc. |
| `coprime1n` (l. 866) | `coprime 1 n` |
| `Gauss_dvdr` (l. 917) | `coprime m n -> (m %\| n * p) = (m %\| p)` |
| `Gauss_gcdr` (l. 935) | `coprime p m -> gcdn p (m * n) = gcdn p n` |
| `chinese_remainder` (l. 1009) | `coprime m1 m2 -> reflect (x = y %[mod m1] /\ ...) (...)` |
| `chinese`, `chinese_modl/r` (l. 1020-1041) | the Chinese remainder solution |

The `(a == b %[mod n])%N` notation **lives in `nat_scope`**. Mixing
it with the homonym in `int_scope` is the single most common
modular-arithmetic bug; see §41.5.

### 41.4 Integer division (`intdiv.v`)

`mathcomp/algebra/intdiv.v` lines 53-77 define the `int` analogues:

```coq
Definition divz (m d : int) : int := ...           (* l. 53 *)
Definition modz (m d : int) : int := m - divz m d * d.   (* l. 57 *)
Definition dvdz d m := (`|d| %| `|m|)%N.           (* l. 59 *)
Definition gcdz m n := (gcdn `|m| `|n|)%:Z.        (* l. 61 *)
Definition lcmz m n := (lcmn `|m| `|n|)%:Z.        (* l. 63 *)
Definition coprimez m n := (gcdz m n == 1).        (* l. 69 *)

Infix "%/" := divz : int_scope.                    (* l. 71 *)
Infix "%%" := modz : int_scope.                    (* l. 72 *)
Notation "d %| m" := (m \in dvdz d) : int_scope.   (* l. 73 *)
```

Note that `dvdz` is a *collective* predicate (`m \in dvdz d`), unlike
`dvdn` which is a plain function — this is why `Search` for `dvdz`
returns membership lemmas. Reviewers (math-comp PR #517)
flag uses of `dvdz d m` as a function as a regression.

The defining choice for `modz`: `0 <= m %% d` whenever `d != 0`
(`modz_ge0`, l. 119), so `(- 7) %/ 3 = -3` and `(- 7) %% 3 = 2`. This
matches the mathematical convention but **diverges from C-style
truncating division**.

| Lemma | Statement |
|-------|-----------|
| `divz_eq` (l. 98) | `m = (m %/ d)%Z * d + (m %% d)%Z` |
| `divz_nat` (l. 79) | `(n %/ d)%Z = (n %/ d)%N` for `n d : nat` |
| `modz_nat` (l. 107) | `(m %% d)%Z = (m %% d)%N` for `m d : nat` |
| `divzN` (l. 82) | `(m %/ - d)%Z = - (m %/ d)%Z` |
| `modzN` (l. 101) | `(m %% - d)%Z = (m %% d)%Z` |
| `divzK` (l. 356) | `(d %\| m)%Z -> (m %/ d)%Z * d = m` |
| `modz_mod` (l. 243) | `((m %% d)%Z = m %[mod d])%Z` |
| `modz_small` (l. 240) | `0 <= m < d -> (m %% d)%Z = m` |
| `modzMm` (l. 304) | `((m %% d) * (n %% d) = m * n %[mod d])%Z` |
| `modzXm` (l. 307) | `((m %% d) ^+ k = m ^+ k %[mod d])%Z` |
| `gcdzC`, `gcdzA` (l. 469, 527) | commut., assoc. of `gcdz` |
| `gcdNz` (l. 478) | `gcdz (- m) n = gcdz m n` |
| `Bezoutz` (l. 603) | `{u & {v \| u * m + v * n = gcdz m n}}` |
| `coprimezP` (l. 606) | reflect form of Bezout |
| `Gauss_dvdz` (l. 615) | `coprimez m n -> (m * n %\| p)%Z = (m %\| p) && (n %\| p)` |
| `coprimezMr` (l. 631) | `coprimez p (m * n) = coprimez p m && coprimez p n` |
| `zchinese_remainder` (l. 667) | int Chinese remainder theorem |
| `zchinese`, `zchinese_modl/r` (l. 675-685) | int CRT solution |

The `nat`-flavoured projections via `divz_nat` / `modz_nat` are the
**standard** way to discharge an `int`-division goal whose arguments
are non-negative — always pull back to `nat` first when possible.

### 41.5 The two `%[mod ...]` notations

The notation `m = n %[mod d]` is **scope-sensitive**. The `nat_scope`
form (`div.v` l. 70) reduces to `m %% d = n %% d` over `nat`; the
`int_scope` form (`intdiv.v` l. 74) reduces to `modz m d = modz n d`
over `int`. Both display the same, but they are different
propositions:

```coq
(* nat_scope: arguments parsed as nat *)
Goal (5 = 12 %[mod 7])%N. by []. Qed.

(* int_scope: arguments parsed as int *)
Goal ((5 : int) = 12 %[mod 7])%Z. by rewrite ...modz... Qed.
```

A frequent reviewer gripe: writing `(... %[mod ...])` without a
scope delimiter when both sides are `nat`-coerced-to-`int`, then
`rewrite modnDl` fails because the head is `modz`, not `modn`.
Solution: mark scope explicitly (`%N` or `%Z`), or use `divz_nat` /
`modz_nat` to project to `nat`.

### 41.6 Search families

The `_mod_` and `_dvd_` infixes are the canonical search tags
(cf. §37). Examples that pay off:

```coq
Search "_mod_" (_ + _).        (* modn/modz commuting with + *)
Search "_dvd_" (gcdn _ _).     (* dvdn vs gcdn *)
Search "Gauss".                (* Gauss_dvd, Gauss_gcd, *)
Search (coprime _ _) "M".      (* coprimeMr, coprimeMl, ... *)
Search (gcdn _ _) (_ %% _).    (* gcdn_modr, gcdn_modl *)
Search (chinese _ _).          (* CRT family *)
Search "egcd".                 (* extended gcd *)
Search "Bezout".               (* Bezoutl, Bezoutr (nat); Bezoutz (int) *)
Search "Euclid".               (* Euclid_dvdM, Euclid_dvdX in prime.v *)
```

`Euclid_dvdM`, `Euclid_dvdX`, `Euclid_dvd_prod` live in
`mathcomp/boot/prime.v` (l. 425-435) — they package the prime case
of `Gauss_dvd`. Use them when the outer hypothesis is `prime p`,
not a manual `coprime` invocation.

### 41.7 Common pitfalls

1. **`Z` (stdlib) vs `int` (mathcomp).** For mathcomp / mathcomp-
   analysis upstream contributions, prefer `int` over `ZArith.Z`:
   `ZArith.Z` is not an `eqType`, has no canonical `Num.realDomainType`,
   and clashes with the `%Z` scope delimiter (which mathcomp reuses
   for `int_scope`). Other Rocq projects (VST, Iris, Bedrock) deliberately
   use `Z` for performance / interoperability reasons; the rule here
   is mathcomp-house-style, not a universal claim about Rocq code.
2. **`Posz_inj` does not exist.** `Posz` is a *constructor*; use
   `case` for elimination, `eqz_nat` for the boolean equality.
3. **`(a == b %[mod n])%N` vs `(a == b %[mod n])%Z`.** Same display,
   different head symbol (`modn` vs `modz`). When in doubt, type
   the scope: `%N` for nat, `%Z` for int.
4. **`m %% 0 = m`, not `0`.** `divn`/`modn`/`divz`/`modz` all use
   the math-comp convention; a `0 < d` side condition is not a
   modular arithmetic prerequisite, only a "result is in `[0, d)`"
   one.
5. **Building rationals as `a # b`.** No such notation; use
   `(a%:Q / b%:Q)` or the printing-only `[rat a // b]`.
6. **`ratz n` in goals.** Mathcomp's own comment (`rat.v` l. 538):
   "ratz should not be used, %:Q should be used instead."
   `ratzE : ratz n = n%:Q` (l. 539) is the canonical rewrite.
7. **`fracq` in goals.** `fracq` is internal to the construction of
   `rat`; reviewers ask for it to be rewritten away
   via `fracqE` (l. 572).
8. **`rat` confused with a `realType`.** `rat` is a
   `realFieldType`, *not* a `realType` (no `lim`, no `exp`). Lemmas
   parameterized over `R : realType` will not unify with
   `R := rat`; embed via `ratr : rat -> R` instead.
9. **`absz` vs `Num.norm` mismatch.** `absz : int -> nat` and
   `Num.norm : int -> int`; they coincide via `abszE` but are not
   the same head symbol. `Search \|_\|` returns `Num.norm` lemmas;
   `Search absz` returns the nat-projection family. Pick the side
   matching the surrounding context, then bridge with `abszE` once.
10. **Mixing `%/` in `nat_scope` and `int_scope` without delimiters.**
    The infix has the same precedence in both, so an expression
    like `(m + n) %/ d` will parse with whichever scope is active.
    When `m, n : nat` but the surrounding goal is in `ring_scope`,
    write `((m + n) %/ d)%N` explicitly.

### 41.8 Quick decision flow

```
Goal involves division / modulus / gcd.

  All arguments are nat?
    -> div.v: divn/modn/dvdn/gcdn/lcmn/coprime
    -> %N scope, no Posz casts

  Arguments are int (possibly mixed with nat via Posz)?
    -> intdiv.v: divz/modz/dvdz/gcdz/lcmz/coprimez
    -> %Z scope; reduce to nat via divz_nat/modz_nat when args >= 0

  Arguments are rat?
    -> rat is a field; use plain /, ^-1; no division-with-remainder
    -> projections numq, denq for normal-form access; numqE bridges

  Need Bezout coefficients?
    -> nat: egcdn, Bezoutl/r          (div.v l. 677, 724-732)
    -> int: egcdz, Bezoutz             (intdiv.v l. 65, 603)

  Chinese remainder?
    -> nat: chinese (div.v l. 1020), chinese_remainder (l. 1009)
    -> int: zchinese (intdiv.v l. 675), zchinese_remainder (l. 667)

  Prime divides product?
    -> Euclid_dvdM, Euclid_dvdX, Euclid_dvd_prod (prime.v)
       (use these BEFORE rolling Gauss_dvd by hand)

  Distribute mod across +/* ?
    -> modnDm/modnMm (div.v); modzDm/modzMm (intdiv.v)
       (single rewrite, not chained _ml then _mr)
```

Sources: `mathcomp/boot/div.v` (file header lines 1-30; lemma sites
cited inline above); `mathcomp/algebra/ssrint.v` (`int` definition
l. 70, `Posz`/`Negz` semantics l. 8-40 header, `absz` l. 394, `intz`
l. 627, `natz` l. 630); `mathcomp/algebra/intdiv.v` (`divz`/`modz`/
`dvdz`/`gcdz`/`coprimez` l. 53-69, `Bezoutz` l. 603,
`zchinese_remainder` l. 667); `mathcomp/algebra/rat.v` (`rat` record
l. 41, `numq`/`denq` l. 57-58, `n%:Q` notation l. 524, `fracqE`
l. 572, `ratr` l. 838); `mathcomp/boot/prime.v` (`Euclid_dvd*`
l. 422-441). Cross-references: §10 (lemma naming), §11 (`n` vs `z`
abbreviation), §23 (avoiding fully-qualified identifiers), §37
(search idioms).

---

