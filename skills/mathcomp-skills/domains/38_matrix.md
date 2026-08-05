## 38. Matrix Idioms

The `matrix.v` library (`mathcomp/algebra/matrix.v`, ~5100 lines) is the
backbone of every linear-algebra proof in mathcomp. Two things make
matrix proofs distinctive: (1) all sizes are tracked statically through
ordinals, so type-checking a matrix expression is half the proof, and
(2) every matrix is *definitionally* a function `'I_m -> 'I_n -> R`,
so every concrete-construction lemma reduces to one canonical rewrite,
`mxE`. Reviewers consistently flag two regressions on matrix code:
opening a `\matrix_(i, j) ...` term without `mxE`, and using `apply:
funext` instead of `apply/matrixP` for entry-wise equalities. This
section codifies the canonical idioms.

### Essential lemmas (start here)

| Lemma / notation | Use it to… | § / cite |
|------------------|------------|----------|
| `mxE` | open any `\matrix_(i, j) F i j` applied to indices | §38.2, §38.4 |
| `matrixP` | reduce `A = B` to entry-wise equality (`=2`) | §38.2, §38.3 |
| `\matrix_(i, j) E i j` | build a matrix from an entry function | §38.1 |
| `mulmx` / `_*m_` | multiply matrices; entries via `mxE` + `\sum` | §38.2, §38.5 |
| `\det`, `det_mulmx` | Leibniz determinant; `\det (A *m B)` factor | §38.2, §38.7 |
| `mulmx_block` | expand a 2-by-2 block product | §38.6 |
| `trmx` / `_^T`, `trmxK` | transpose and its involution | §38.2 |

### 38.1 Reading the notation

The general form is `'M[R]_(m, n)` -- an m-by-n matrix with entries in
`R`. The square, row, and column shorthands all expand to this form:

| Notation | Meaning |
|----------|---------|
| `'M[R]_(m, n)` | m-by-n matrix over `R` (matrix.v l. 326) |
| `'M[R]_n` | square: `'M[R]_(n, n)` (l. 329) |
| `'M[R]_(n)` | parsing-only alias for `'M[R]_n` (l. 330) |
| `'rV[R]_n` | row vector: `'M[R]_(1, n)` (l. 327) |
| `'cV[R]_n` | column vector: `'M[R]_(n, 1)` (l. 328) |
| `'M_(m, n)`, `'M_n`, `'rV_n`, `'cV_n` | implicit-`R` versions (l. 331-334) |

The `[R]` is dropped when `R` is fixed by context (a section variable,
or the goal). Reviewers prefer the bracket-free form in section bodies
and the bracketed form in lemma statements (see §24 on type-constraint
hygiene): `Lemma foo (A : 'M[R]_(m, n)) : ...` rather than relying on
section variables to fix `R`.

Builders:

| Notation | Builds |
|----------|--------|
| `\matrix_(i, j) E i j` | the matrix `(i, j) \mapsto E i j` (l. 346) |
| `\matrix_(i < m, j < n) E i j` | explicit-bound builder (l. 340) |
| `\matrix_(i, j < n) E i j` | square; both bounds `n` (l. 343) |
| `\row_(j < n) E j`, `\row_j E` | row vector builder (l. 357, 359) |
| `\col_(i < m) E i`, `\col_i E` | column vector builder (l. 353, 355) |
| `M i j` | element access (via `fun_of_matrix` coercion, l. 289-291) |
| `\matrix[k]_(i, j) E` | keyed builder, used by mathcomp internals (l. 337) |

The keyed form `\matrix[k]_(...)` exists so that distinct matrix
operations (`addmx`, `mulmx`, `delta_mx`, ...) all sit on top of a
single `matrix_of_fun` definition without rewriting through each other
unintentionally; user code essentially never writes the keyed form by
hand.

A matrix is, definitionally, an `{ffun 'I_m * 'I_n -> R}` wrapped in a
`Variant matrix` (l. 283). The coercion `fun_of_matrix` makes `M i j`
mean `mx_val M (i, j)`; element access is *application*, not a separate
operator. Hence: do not write `mx_val M`, never call `nth` on a row
vector -- always use `M i j`.

### 38.2 The core lemma family

Spot-checked against `mathcomp/algebra/matrix.v` in `rocq-9.1`.

| Lemma | What it does |
|-------|--------------|
| `mxE` (l. 308) | the canonical equation: `(\matrix[k]_(i, j) F i j) i j = F i j` |
| `matrixP` (l. 311) | reflect: `A =2 B <-> A = B` -- entry-wise equality |
| `eq_mx` (l. 317) | `F1 =2 F2 -> \matrix_(i,j) F1 i j = \matrix_(i,j) F2 i j` |
| `rowP` (l. 445) | row-vector entry equality |
| `colP` (l. 457) | column-vector entry equality |
| `row_matrixP` (l. 451) | `(forall i, row i A = row i B) <-> A = B` |
| `const_mx` (l. 379) | the constant matrix |
| `trmx` (l. 401), notation `_^T` | transpose; `trmxK` (l. 596) is the involution |
| `trmx_const` (l. 430) | `(const_mx a)^T = const_mx a` |
| `trmx_mul` (l. 3216) | `(A *m B)^T = B^T *m A^T` |
| `delta_mx i j` (l. 2268) | the standard basis matrix |
| `matrix_sum_delta` (l. 2295) | `A = \sum_i \sum_j A i j *: delta_mx i j` |
| `scalar_mx` / `_%:M` (l. 2002, notation l. 2004) | embeds `R` into `'M_n` (diagonal) |
| `mx11_scalar` (l. 2053) | a 1-by-1 matrix is `(M 0 0)%:M` |
| `mulmx` / `_*m_` (l. 2363, notation l. 2366) | product `'M_(m,n) -> 'M_(n,p) -> 'M_(m,p)` |
| `mulmxA` (l. 2368) | associativity |
| `mul0mx`, `mulmx0` (l. 2376, 2381) | absorbing zero |
| `mul1mx`, `mulmx1` (l. 2492, 2497) | identity `1%:M` |
| `mulmxDl`, `mulmxDr` (l. 2386, 2393) | bilinearity |
| `mulmxBl`, `mulmxBr` (l. 3333, 3337) | subtraction (over a ring) |
| `mulmxN`, `mulNmx` (l. 3327, 3330) | sign |
| `mulmxE` (l. 2849) | `mulmx = *%R` -- recover `*%R` for the square-ring instance |
| `mulmx_suml`, `mulmx_sumr` (l. 2411, 2417) | distribute `*m` over `\sum` |
| `summxE` (l. 1640) | `(\sum_(k <- r \| P k) E k) i j = \sum_(...) E k i j` |
| `\det` (l. 3375, notation l. 3391) | Leibniz determinant |
| `det_tr` (l. 3486), `det1` (l. 3502), `det0` (l. 3515) | det of transpose / unit / zero |
| `det_mulmx` (l. 3527) | `\det (A *m B) = \det A * \det B` (commutative ring) |
| `det_mx11` (l. 3524), `det_mx00` (l. 3505) | small-size determinants |
| `expand_det_row`, `expand_det_col` (l. 3585, 3606) | Laplace expansion |
| `\adj` / `adjugate` (l. 3384, notation l. 3392) | adjugate (cofactor transpose) |
| `mul_mx_adj`, `mul_adj_mx` (l. 3620, 3634) | `A *m \adj A = (\det A)%:M` and dually |
| `adj1` (l. 3639) | `\adj 1%:M = 1%:M` |
| `cofactor` (l. 3379) | the (i, j) cofactor |
| `unitmx`, `invmx` (l. 3718) | invertibility predicate and inverse |

### 38.3 `apply/matrixP` for entry-wise equality

Two matrices are equal iff all entries match. Use `matrixP`, not
`funext`, not `apply: val_inj`:

```coq
(* WRONG -- funext needs FunctionalExtensionality and is rejected. *)
apply: funext => i; apply: funext => j; rewrite ...

(* WRONG -- val_inj works but exposes the ffun representation. *)
apply: val_inj; apply/ffunP => -[i j]; rewrite ...

(* RIGHT *)
apply/matrixP => i j; rewrite !mxE.
```

The accompanying tactic chord `apply/matrixP => i j; rewrite !mxE` is
the matrix analogue of `apply/eqP; rewrite eqE`. For row / column
vectors the specialized `rowP` and `colP` are slightly more concise:

```coq
apply/rowP => j; rewrite !mxE.    (* 'rV[R]_n *)
apply/colP => i; rewrite !mxE.    (* 'cV[R]_m *)
```

### 38.4 `mxE`: the sigma-algebra of matrix manipulation

`mxE` collapses any `\matrix_(i, j) F i j` applied to indices: this is
the *only* lemma that opens a builder. In practice:

```coq
(* Goal: (M + N) i j = M i j + N i j *)
by rewrite !mxE.

(* Goal: ((a *: M)^T) i j = a * M j i *)
by rewrite !mxE.
```

The `!mxE` form is canonical -- one rewrite is rarely enough because
nested builders fire on each other.

### 38.5 Working with `(M *m N) i j`

`mulmx` is defined (l. 2363) as `\matrix[mulmx_key]_(i, k) \sum_j A i j
* B j k`. So `(M *m N) i j` rewrites with `mxE` to a `\sum`:

```coq
(* Goal: (M *m N) i j = \sum_k M i k * N k j *)
by rewrite mxE.
```

After `mxE`, all the §34 bigop machinery applies. Combined idiom for
"`A *m B` on entries" inside a bigop:

```coq
apply/matrixP => i j.
rewrite !mxE; under eq_bigr => k _ do rewrite !mxE.
(* now goal is a clean nested \sum *)
```

### 38.6 Block matrices and submatrices

| Definition | Shape |
|------------|-------|
| `row_mx A1 A2` (l. 738) | `'M_(m, n1+n2)` from `'M_(m, n1)` and `'M_(m, n2)` |
| `col_mx A1 A2` (l. 743) | `'M_(m1+m2, n)` from `'M_(m1, n)` and `'M_(m2, n)` |
| `block_mx Aul Aur Adl Adr` (l. 992) | 2-by-2 block builder |
| `lsubmx`, `rsubmx` (l. 752, 756) | left / right halves of a `'M_(m, n1+n2)` |
| `usubmx`, `dsubmx` (l. 760, 764) | upper / lower halves of a `'M_(m1+m2, n)` |
| `ulsubmx`, `ursubmx`, `dlsubmx`, `drsubmx` (l. 1008-) | the four blocks of a `'M_(m1+m2, n1+n2)` |

For multiplying through a block matrix, the canonical lemma is
`mulmx_block` (l. 2706): a 2-by-2 block product expands to the four
sums of products. Reviewers reject hand-rolled
`apply/matrixP => i j; case: (split i)` indexing where `mulmx_block`
applies.

### 38.7 Determinant, cofactors, adjugate

```coq
(* Multiplicativity (commutative ring): *)
rewrite det_mulmx.            (* \det (A *m B) = \det A * \det B *)

(* Transpose-invariance: *)
rewrite det_tr.                (* \det A^T = \det A *)

(* Identity / zero: *)
rewrite det1.                  (* \det 1%:M = 1 *)
rewrite det0.                  (* \det (0 : 'M_n.+1) = 0 *)

(* Small sizes: *)
rewrite det_mx00.              (* \det (A : 'M_0) = 1 *)
rewrite det_mx11.              (* \det (A : 'M_1) = A 0 0 *)

(* Row / column expansion: *)
rewrite (expand_det_row A i0). (* Laplace along row i0 *)
rewrite (expand_det_col A j0). (* Laplace along column j0 *)
```

The adjugate `\adj A := \matrix_(i, j) cofactor A j i` (l. 3384) gives
Cramer's rule via `mul_mx_adj` (l. 3620) and `mul_adj_mx` (l. 3634):

```coq
A *m \adj A = (\det A)%:M.
\adj A *m A = (\det A)%:M.
```

For `mxalgebra.v` (`mathcomp/algebra/mxalgebra.v`):

| Lemma | What it does |
|-------|--------------|
| `\rank A` / `mxrank` (notation l. 2301) | matrix rank |
| `mxrank_tr` (l. 473) | `\rank A^T = \rank A` |
| `mxrank0` (l. 505), `mxrank_eq0` (l. 508) | rank of zero |
| `kermx`, `cokermx` (l. 214, 215) | left / right kernels |
| `mxrank_ker` (l. 1276) | `\rank (kermx A) = m - \rank A` |
| `mulmx_ker` (l. 1288) | `kermx A *m A = 0` |
| `pinvmx`, `mulmxKpV` (l. 217, 524) | pseudo-inverse and its cancellation |

### 38.8 Naming patterns

1. **`E`-suffix means "open the builder"**. `mxE`, `summxE`,
   `block_mxEul`, `row_mxEl`, `col_mxEu`, `lsubmxEsub`, `castmxE`,
   `mxsub_const`. The suffix is the §10 `E` for "evaluate / compute".

2. **`K`-suffix means "cancel" (§10)**. `trmxK`, `row_mxKl`, `row_mxKr`,
   `col_mxKu`, `col_mxKd`, `hsubmxK`, `vsubmxK`, `submxK`, `mulmxK`,
   `mulKmx`. A `K`-lemma is what you `rewrite` to fold a
   build-then-extract pair.

3. **`tr_*` prefix** for transpose interactions: `tr_row`, `tr_col`,
   `tr_row_mx`, `tr_col_mx`, `trmx_mul`, `trmx_lsub`, `trmx_usub`. The
   `tr_*` form has the transpose on the *outside* of the LHS (head
   symbol), per §37.2.

4. **Side suffixes `l` / `r` / `u` / `d`** on splitting lemmas.

### 38.9 `vector.v` is not for matrices

mathcomp's `mathcomp/algebra/vector.v` defines abstract
finite-dimensional vector-space structures (the `vectType` HB
hierarchy, see §35), not concrete row / column vectors. Concrete row
vectors are `'rV[R]_n`, defined and operated on in `matrix.v`.

### 38.10 Common pitfalls

```coq
(* WRONG -- entered a builder without opening it. *)
have : (\matrix_(i, j) f i j) i j = f i j by [].
(* RIGHT *)
have : (\matrix_(i, j) f i j) i j = f i j by rewrite mxE.

(* WRONG -- funext / propositional extensionality not needed. *)
apply: funext => i; apply: funext => j; rewrite ...
(* RIGHT *)
apply/matrixP => i j; rewrite !mxE.

(* WRONG -- exposes the underlying ffun. *)
apply: val_inj; apply/ffunP => -[i j].
(* RIGHT *)
apply/matrixP => i j.

(* WRONG -- rolling the bilinear product by hand. *)
rewrite mxE; apply: eq_bigr => k _; rewrite !mxE.
(* RIGHT *)
rewrite mxE; under eq_bigr => k _ do rewrite !mxE.

(* WRONG -- decomposing (A *m B) i j by hand. *)
rewrite /mulmx /= /matrix_of_fun unlock /= ffunE.
(* RIGHT *)
rewrite mxE.

(* WRONG -- pattern-matching block_mx product. *)
apply/matrixP => i j; case: (split i) => i'; case: (split j) => j'; ...
(* RIGHT *)
rewrite mulmx_block.

(* WRONG -- recomputing Cramer from \det / cofactor. *)
rewrite /invmx /adjugate /determinant ...
(* RIGHT -- invoke the canonical identity. *)
rewrite mul_mx_adj.

(* WRONG -- naming a transpose lemma `_trmx`. *)
Lemma mul_trmx ... (* pattern: head_symbol is mul, tr_ is a modifier. *)
(* RIGHT (§10, §37.2): tr on the LHS head, so prefix it. *)
Lemma trmx_mul A B : (A *m B)^T = B^T *m A^T.
```

### 38.11 Quick decision flow

```
Goal involves a concrete matrix.

  Equality of two matrices?
    -> apply/matrixP => i j; rewrite !mxE
    -> apply/rowP / apply/colP for vectors

  An entry of a builder (\matrix_..., addmx, mulmx, scalemx, ...)?
    -> rewrite mxE                (one builder)
    -> rewrite !mxE               (nested builders)
    -> rewrite summxE             (a \sum of matrices indexed)

  An entry of A *m B?
    -> rewrite mxE; under eq_bigr => k _ do rewrite !mxE

  Multiplying a 2-by-2 block product?
    -> rewrite mulmx_block
    -> mul_row_col / mul_block_col / mul_row_block for partial splits

  Determinant of a special matrix?
    -> det1 / det0 / det_mx00 / det_mx11 / det_scalar / det_tr
    -> det_mulmx for products
    -> expand_det_row / expand_det_col for Laplace expansion

  Cramer / inverse?
    -> mul_mx_adj / mul_adj_mx
    -> invmx (only if A \in unitmx)

  Rank / kernel?
    -> mxrank0 / mxrank_eq0 / mxrank_tr / mxrank_ker
    -> mulmx_ker (kermx A *m A = 0)
```

### 38.12 Sources

`mathcomp/algebra/matrix.v` (file header l. 270-282; lemma sites cited
in 38.2-38.7 above; the `mxE` / `matrixP` pair l. 308-314 is the file's
first theorem); `mathcomp/algebra/mxalgebra.v` (`mxrank` notation
l. 2301; `kermx` / `cokermx` l. 214-215); MathComp Book chapter 8
("Linear Algebra"). The `apply/matrixP; rewrite !mxE` discipline is
enforced throughout matrix.v itself; spot-check the proof of `mulmxA`
(l. 2371) for the canonical form. Cross-ref §10 (naming), §11
(suffixes), §13 (definition naming), §34 (bigops), §35 (HB
hierarchy).

---

