## 39. Polynomial Idioms

The univariate polynomial library (`mathcomp/algebra/poly.v`, ~3500 lines)
sits between `bigop` (§34) and the algebraic hierarchy: `{poly R}` is built
as a sub-`seqType` of `R` with a non-zero last coefficient, then has the
ring/idomain HB structures stacked on top. Reviewers expect a particular
calculus of `coef`, `lead_coef`, `size`, and `horner` rewrites: hand-rolling
recursions on the underlying `seq` is the single most common rejection.
This section codifies the canonical idioms.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `coefE` | rewrite any coefficient `p\`_i` (the multi-rule) | §39.2 |
| `hornerE` | evaluate any `p.[x]` (the multi-rule) | §39.2 |
| `derivE` | compute any derivative `p^\`()` (the multi-rule) | §39.2 |
| `polyP` | reduce `p = q` to coefficient-wise equality | §39.2, §39.3 |
| `coefK`, `poly_def` | recover `p` as `\sum_i p\`_i *: 'X^i` | §39.2, §39.6 |
| `rootP`, `factor_theorem` | root as `p.[x] = 0`; factor out `'X - a` | §39.2 |
| `lead_coef_eq0`, `size_poly_gt0` | discharge `p != 0` before size lemmas | §39.2, §39.8 |

### 39.1 Reading the notation

```coq
{poly R}            (* polynomials over the (semi)ring R *)
'X                  (* the indeterminate *)
'X^n                (* := 'X ^+ n; convertible to 'X when n = 1 *)
c%:P                (* polyC c, the constant polynomial *)
\poly_(i < n) E i   (* poly n (fun i => E i): builder, degree < n *)
p`_i                (* generic seq-nth at 0; the i-th coefficient *)
size p              (* (degree p).+1, or 0 if p = 0 *)
lead_coef p         (* p`_(size p).-1 *)
p.[x]               (* horner p x: Horner evaluation *)
p^`()               (* deriv p: formal derivative *)
p^`(n)              (* derivn n p: iterated derivative *)
p^`N(n)             (* nderivn n p: derivn n p / n! *)
p \Po q             (* comp_poly q p: composition; q on the right *)
```

The head of `\poly_`, `polyC`, `polyX`, and the binary operators are
all `locked_with`. Do not `unlock` — the lemmas below cover every
manipulation.

### 39.2 The core lemma family

Spot-checked against `mathcomp/algebra/poly.v`.

| Lemma | Statement / use |
|-------|-----------------|
| `coefE` (l. 2681) | multi-rule for `p\`_i`: bundles `coef0`, `coef1`, `coefC`, `coefX`, `coefXn`, `coefD`, `coefN`, `coefB`, `coefZ`, `coefMC`, `coefCM`, `coefXnM`, `coefMXn`, `coefMX`, `coefXM`, `coefMn`, `coef_cons`, `coef_Poly`, `coef_poly`, `coef_deriv`, `coef_derivn`, `coef_nderivn`, `coef_map`, `coef_sum`, `coef_comp_poly` |
| `coefC` (l. 175) | `c%:P\`_i = if i == 0 then c else 0` |
| `coefX` (l. 698) | `'X\`_i = (i == 1)%:R` |
| `coefXn` (l. 767) | `'X^n\`_i = (i == n)%:R` |
| `coefD` (l. 378) | `(p + q)\`_i = p\`_i + q\`_i` |
| `coefM` (l. 519) | `(p * q)\`_i = \sum_(j < i.+1) p\`_j * q\`_(i - j)` |
| `coefZ` (l. 670) | `(a *: p)\`_i = a * p\`_i` |
| `coefMXn` (l. 805) | `(p * 'X^n)\`_i = if i < n then 0 else p\`_(i - n)` |
| `coef_poly` (l. 267) | `(\poly_(i < n) E i)\`_k = if k < n then E k else 0` |
| `coef_sum` (l. 387) | swap `\sum` and `_\`_i` |
| `coefK` (l. 280) | `\poly_(i < size p) p\`_i = p` (recovery) |
| `poly_def` (l. 829) | `\poly_(i < n) E i = \sum_(i < n) E i *: 'X^i` |
| `polyP` (l. 188) | `nth 0 p =1 nth 0 q <-> p = q` (extensional equality) |
| `polyseqC` (l. 169) | `c%:P = nseq (c != 0) c :> seq R` |
| `polyseqXn` (l. 772) | `'X^n = rcons (nseq n 0) 1 :> seq R` |
| `polyseq0` (l. 314) | `(0 : {poly R}) = [::]` |
| `polyseq1` (l. 508) | `(1 : {poly R}) = [:: 1]` |
| `polyseqXaddC` (l. 733) | `'X + a%:P = [:: a; 1]` |
| `lead_coefE` (l. 161) | `lead_coef p = p\`_(size p).-1` (definitional) |
| `lead_coef0` (l. 323) | `lead_coef 0 = 0` |
| `lead_coef1` (l. 517) | `lead_coef 1 = 1` |
| `lead_coefC` (l. 184) | `lead_coef c%:P = c` |
| `lead_coefM` (l. 2919) | `lead_coef (p * q) = lead_coef p * lead_coef q` (idomain) |
| `lead_coef_eq0` (l. 349) | `(lead_coef p == 0) = (p == 0)` |
| `size_polyC` (l. 172) | `size c%:P = (c != 0)` |
| `size_polyXn` (l. 778) | `size 'X^n = n.+1` |
| `size_mulX` (l. 751) | `p != 0 -> size (p * 'X) = (size p).+1` |
| `size_mulXn` (l. 811) | `p != 0 -> size (p * 'X^n) = (n + size p)%N` |
| `size_polyD` (l. 399) | `size (p + q) <= maxn (size p) (size q)` |
| `size_polyMleq` (l. 543) | `size (p * q) <= (size p + size q).-1` |
| `size_poly0` (l. 317) | `size (0 : {poly R}) = 0` |
| `size_poly_eq0` (l. 325) | `(size p == 0) = (p == 0)` |
| `size_poly_gt0` (l. 334) | `(0 < size p) = (p != 0)` |
| `polyC_eq0` (l. 355) | `(c%:P == 0) = (c == 0)` |
| `polyC_inj` (l. 181) | `injective polyC` |
| `polyCD`, `polyCN`, `polyCB`, `polyCM` (l. 391, 1542, 1545, 594) | `polyC` is a ring morphism |

Horner family (`hornerE` is the multi-rule):

| Lemma | Statement |
|-------|-----------|
| `hornerE` (l. 2726) | bundles `hornerD`, `hornerN`, `hornerX`, `hornerC`, `horner_exp`, `simp`, `hornerCM`, `hornerZ`, `hornerM`, `horner_cons` |
| `hornerC` (l. 847) | `(c%:P).[x] = c` |
| `hornerX` (l. 850) | `'X.[x] = x` |
| `hornerXn` (l. 973) | `('X^n).[x] = x ^+ n` |
| `horner0` (l. 844) | `(0 : {poly R}).[x] = 0` |
| `hornerD` (l. 893) | `(p + q).[x] = p.[x] + q.[x]` |
| `hornerN` (l. 1586) | `(- p).[x] = - p.[x]` |
| `hornerM` (l. 2705) | `(p * q).[x] = p.[x] * q.[x]` (commutative) |
| `hornerZ` (l. 906) | `(c *: p).[x] = c * p.[x]` |
| `horner_exp` (l. 2719) | `(p ^+ n).[x] = p.[x] ^+ n` |
| `hornerXsubC` (l. 1589) | `('X - a%:P).[x] = x - a` |
| `horner_coef` (l. 871) | `p.[x] = \sum_(i < size p) p\`_i * x ^+ i` |
| `horner_poly` (l. 887) | `(\poly_(i < n) E i).[x] = \sum_(i < n) E i * x ^+ i` |
| `horner_sum` (l. 916) | `(\sum_(i <- r \| P i) F i).[x] = \sum F i.[x]` |

Derivative family (`derivE` is the multi-rule):

| Lemma | Statement |
|-------|-----------|
| `derivE` (l. 1643) | bundles `derivZ`, `deriv_mulC`, `derivC`, `derivX`, `derivMXaddC`, `derivXsubC`, `derivM`, `derivB`, `derivD`, `derivN`, `derivXn`, `derivMn` |
| `derivC` (l. 1083) | `c%:P^\`() = 0` |
| `derivX` (l. 1086) | `'X^\`() = 1` |
| `derivXn` (l. 1089) | `('X^n)^\`() = 'X^(n.-1) *+ n` |
| `derivM` (l. 1126) | `(p * q)^\`() = p^\`() * q + p * q^\`()` |
| `coef_deriv` (l. 1071) | `p^\`()\`_i = p\`_i.+1 *+ i.+1` |

Roots and the factor theorem:

| Lemma | Statement |
|-------|-----------|
| `rootP` (l. 1442) | `reflect (p.[x] = 0) (root p x)` |
| `rootE` (l. 1439) | unfolds `root p x` and `x \in root p` to `p.[x] == 0` |
| `rootC` (l. 1451) | `root a%:P x = (a == 0)` |
| `rootX` (l. 1460) | `root 'X x = (x == 0)` |
| `root_XsubC` (l. 1732) | `root ('X - a%:P) x = (x == a)` |
| `factor_theorem` (l. 1738) | `reflect (exists q, p = q * ('X - a%:P)) (root p a)` |
| `dvdp_XsubCl` (polydiv.v l. 1364) | `('X - x%:P) %\| p = root p x` |

### 39.3 `apply: polyP` for coefficient-wise equality

The reflex for `p = q : {poly R}` is to reduce to a coefficient
equality and then close with `coefE`:

```coq
apply/polyP => i.
rewrite !coefE.    (* or specific coefM, coefD, ... *)
(* now an equation in R, indexed by i *)
```

`polyP` (l. 188) is stated as `nth 0 p =1 nth 0 q <-> p = q`. The
companion `eq_poly` (l. 832) is for **builder equality**: if
`forall i, i < n -> E1 i = E2 i`, then `\poly_(i < n) E1 i =
\poly_(i < n) E2 i`. Use `eq_poly` whenever both sides are
already in `\poly_(i < n) _` form; reach for `polyP` only when the
two sides are not syntactically built by the same builder.

### 39.4 Polynomial division and roots

Pseudo-division (`polydiv.v`) provides `%/`, `%%`, `%|`, `%=` in
`ring_scope`:

| Notation (polydiv.v) | Reads as |
|----------------------|----------|
| `m %/ d` (l. 830) | `divp m d` |
| `m %% d` (l. 831) | `modp m d` |
| `p %\| q` (l. 832) | `dvdp p q` |
| `p %= q` (l. 833) | `eqp p q` (associate, i.e. `p %\| q && q %\| p`) |

The Euclidean identity is `divp_eq` (polydiv.v l. 921):
`(lead_coef q ^+ scalp p q) *: p = (p %/ q) * q + (p %% q)`. Over a
field the leading-coefficient power becomes `1`.

Workhorses:

```coq
rewrite -dvdp_XsubCl.       (* (X - a) %| p   <->   root p a *)
rewrite root_factor_theorem.(* same, oriented as a rewrite *)
case/factor_theorem: rpa => q ->.   (* a-rooted p factors as q * (X - a) *)
case/dvdpP: dvd => q ->.            (* d %| p  yields  q with p = q * d *)
```

### 39.5 Horner evaluation

Two distinct evaluation morphisms:

- **`horner_eval x : {poly R} -> R`** (l. 909) is the `(semi)linear`
  and (over commutative `R`) `monoid_morphism` view of `p \mapsto
  p.[x]`. Use it when you want `raddf_sum`, `rmorphM`, `rmorphXn`,
  `rmorph_prod` to fire on a Horner-evaluated bigop.
- **`horner_morph cfu`** (l. 1907) for `cfu : commr_rmorph f u`
  evaluates `(map_poly f p).[u]`. It is a full ring morphism
  `{poly aR} -> rR` and is the entry point for the universal
  property of `{poly R}`.

```coq
(* Push horner into a sum *)
Goal (\sum_(i < n) F i).[x] = \sum_(i < n) (F i).[x].
Proof. exact: (raddf_sum (horner_eval _)). Qed.   (* horner_sum *)
```

Always prefer the named alias (`horner_sum`, `horner_prod`) over the
raw morphism invocation (§34.4 rule).

### 39.6 Bigop patterns over polynomials

Recovery from coefficients:

```coq
have : p = \sum_(i < size p) p`_i *: 'X^i by rewrite -poly_def coefK.
```

`poly_def` (l. 829) and `coefK` (l. 280) are the two halves; chained
they are the main interface between `\poly_` and `\sum_(i < n) _ *:
'X^i`.

`under eq_bigr` inside a polynomial sum (cross-ref §34.3):

```coq
under eq_bigr => i _ do rewrite coefE.
rewrite -poly_def horner_poly.
under eq_bigr => i _ do rewrite mulrC.
```

Double-induction over a polynomial expression: `poly_ind` (l. 726)
gives the `0 / p * 'X + c%:P` recursion, exactly mirroring the
big-endian seq representation. Use it instead of `case: (polyseq p)`
plus a manual `cons_poly_def` rewrite.

### 39.7 Naming conventions for poly lemmas

The mathcomp suffix interpretation (poly.v l. 96-99) is part of the
contract:

- `C` — constant polynomial: `polyseqC`, `coefC`, `lead_coefC`,
  `size_polyC`, `polyC_eq0`, `polyC_inj`, `polyCD`, `polyCM`, `hornerC`,
  `derivC`, `rootC`.
- `X` — the variable `'X`: `polyseqX`, `coefX`, `size_polyX`,
  `lead_coefX`, `hornerX`, `derivX`, `rootX`.
- `Xn` — a power `'X^n`: `coefXn`, `size_polyXn`, `lead_coefXn`,
  `hornerXn`, `derivXn`, `monicXn`.
- `XsubC`, `XaddC` — `'X - c%:P` / `'X + c%:P`: `size_XsubC`,
  `lead_coefXsubC`, `hornerXsubC`, `derivXsubC`, `monicXsubC`,
  `root_XsubC`, `polyseqXsubC`.

Cross-ref §10 for the full mathcomp suffix list, §11 for the
abbreviation table.

### 39.8 Common pitfalls

1. **`c%:P` (poly constant) vs `c%:R` (ring of-int)**. Both use
   scope-driven coercions but produce different types: `c%:P : {poly R}`,
   `c%:R : R`. Reading `n%:R%:P` is `(n%:R : R)%:P : {poly R}`;
   `polyC_natr` (l. 617) collapses it to `n%:R : {poly R}` in idomain
   contexts.

2. **Manual `coef` calculations vs `coefE` rewrites**.
   ```coq
   (* WRONG *)
   move=> i; rewrite /coefM /add_poly /mul_poly !unlock /=.
   (* RIGHT *)
   move=> i; rewrite !coefE.
   ```

3. **`size 0 = 0` is a special case**. `size_poly_gt0` (l. 334)
   states `(0 < size p) = (p != 0)`, and many size lemmas have a
   `p != 0` precondition. Always discharge `p != 0` before unfolding
   a size identity.

4. **`size_polyMleq` is `<=`, not `=`**. The proper-mul equality
   `size (p * q) = (size p + size q).-1` is `size_proper_mul`
   (l. 562), gated on `lead_coef p * lead_coef q != 0`.

5. **`=p` (`%=`, the associate relation) vs `=`**. `p %= q`
   (polydiv.v l. 833) means `dvdp p q && dvdp q p`. It is *not*
   propositional equality on `{poly R}`. Convert to `=` via
   `eqp_eq` (polydiv.v l. 1422) when you need scaled equality.

6. **`Search` on poly notations.** The `\poly_(i < n) E` head is
   `poly`; prefer `Search "\poly_"` (substring) or
   `Search (\poly_(_ < _) _)`. Constant-polynomial lemmas are
   `polyC*`, *not* `polyc*` — case matters (cross-ref §11).

7. **Unlocking `'X` or `polyC`.** Both are `locked_with`; downstream
   tactics expect them locked so that `coefE`/`hornerE` can rewrite
   them. The right move is `rewrite polyseqC` / `rewrite polyseqX`
   to expose the seq, or stay at the `coef` level.

8. **`poly_ind` vs `case: p`**. `case: (p : seq R)` exposes the
   `subType` projection; `elim/poly_ind: p` recurses on the
   `cons_poly_def` shape `p * 'X + c%:P` (l. 720, 726). Use the
   latter for any inductive proof.

### 39.9 Quick decision flow

```
Goal involves a polynomial.

  Equality of two polys?
    -> apply/polyP => i; rewrite !coefE        (coef-wise)
    -> apply/eq_poly => i lt_in; ...           (both are \poly_)

  A coefficient `_`_i`?
    -> rewrite !coefE                          (multi-rule)
    -> single coef*: pick from §39.2 table

  A horner evaluation `_.[x]`?
    -> rewrite !hornerE                        (multi-rule)
    -> push into a sum/prod: horner_sum / horner_prod
    -> change of ring: horner_morph / map_poly

  A derivative `_^`()`?
    -> rewrite !derivE                         (multi-rule)
    -> coefficient: rewrite coef_deriv

  A root statement?
    -> apply/rootP                             (Prop bridge)
    -> rewrite root_XsubC / rootC / rootX
    -> factor: case/factor_theorem            (or dvdp_XsubCl)

  A size argument?
    -> first eliminate `p = 0` (poly0Vpos / size_poly_gt0)
    -> size_polyD / size_polyMleq / size_proper_mul / size_mulXn

  Recover p as `\sum p`_i *: 'X^i`?
    -> rewrite -poly_def coefK

  Induction on a polynomial?
    -> elim/poly_ind: p => [|p c IHp]
       (NOT case: (p : seq R))

  Bigop manipulation under the binder?
    -> under eq_bigr do rewrite ...            (§34.3)
```

Sources: `mathcomp/algebra/poly.v` (file header lines 1-104; lemma
sites cited in §39.2; multi-rules at lines 2681, 2726, 1643);
`mathcomp/algebra/polydiv.v` (notations l. 830-833; `divp_eq`
l. 921; `dvdp_XsubCl` l. 1364; `root_factor_theorem` l. 1377;
`eqpP` l. 1394). MathComp Book chapter 5 ("Polynomials") covers
`polyP`/`coefE`/`hornerE` in tutorial form. Cross-ref §10 (head
naming), §11 (suffix table), §13 (definition naming category),
§34 (the bigop calculus all polynomial sums plug into).

---

