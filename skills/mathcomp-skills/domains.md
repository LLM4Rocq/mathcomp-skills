# mathcomp-skills — Domains dispatcher

This file is an **index**. Each library area lives in its own file
under `domains/` so that loading one section does not pull in the
others. Read the specific file matching your question.

## Cross-file references

`reference.md` holds the **core** (§1-§37): conventions, naming,
proof style, HB instances, deprecation, concision, idiomatic
ssreflect, the PR Citation Index, and the cross-cutting idioms
(Bigops, HB Factories, Choice/Decidability, Search Discipline).
It also holds **§48**, the migration map from the MathComp book
(mathcomp 1.x / Coq 8) to mathcomp 2.5 / HB / Rocq 9.

The files under `domains/` hold the **library-specific idioms**
(§38-§47 and §49). Cross-references obey:

- `(§N)` with `N ≤ 37` or `N = 48` → `reference.md`
- `(§N)` with `38 ≤ N ≤ 47` or `N = 49` → `domains/<N>_<topic>.md`

## Which file to load

| Section | File | Topic |
|---------|------|-------|
| §38 | `domains/38_matrix.md` | Matrix idioms (`'M[R]_(m,n)`, `mxE`, `\det`, block matrices) |
| §39 | `domains/39_polynomial.md` | Polynomial idioms (`{poly R}`, `coefE`, `hornerE`, `derivE`) |
| §40 | `domains/40_finset.md` | Finset idioms (`{set T}`, `inE`, cardinality) |
| §41 | `domains/41_int_rat.md` | Integer, rational, and modular arithmetic (`int`, `rat`, `divz`/`modz`/`gcdz`, `'Z_p`) |
| §42 | `domains/42_derive.md` | Derivative and `is_derive` typeclass resolution |
| §43 | `domains/43_measure.md` | Measure theory and Lebesgue integral |
| §44 | `domains/44_topology.md` | Topology, filters, and `near` proofs |
| §45 | `domains/45_algebra_tactics.md` | `ring` / `field` / `lra` / `nra` / `zify` decision tree |
| §46 | `domains/46_tuple_perm_binomial.md` | Tuples (`n.-tuple`), permutations (`'S_n`), binomials (`'C(n,m)`) |
| §47 | `domains/47_finfun.md` | Finite functions (`{ffun T -> R}`) |
| §49 | `domains/49_nat_seq.md` | nat and seq (ssrnat: `.+1`, `subn`, `leqP`/`ltnP`; seq: `nth`, `[seq …]`, `\in` on seq) |

## Decision flow for "which file?"

```
Question mentions ...                          → Read

  matrix, vector, \det, \tr, mxE, \mulmx       → domains/38_matrix.md
  polynomial, {poly R}, horner, deriv          → domains/39_polynomial.md
  {set T}, [set _ | _], #|_|, finset           → domains/40_finset.md
  int, rat, %:R, divz, modz, gcdz, intdiv      → domains/41_int_rat.md
  'Z_p, 'F_p, inZp, arithmetic mod p           → domains/41_int_rat.md
  is_derive, 'D[_], differentiable             → domains/42_derive.md
  measurable_fun, \int[mu]_..., Lebesgue       → domains/43_measure.md
  filter, nbhs, cvg, lim, \near, topology      → domains/44_topology.md
  ring, field, lra, nra, lia, nia, zify        → domains/45_algebra_tactics.md
  n.-tuple, tnth, {perm T}, 'S_n, 'C(n, m)     → domains/46_tuple_perm_binomial.md
  {ffun T -> R}, [ffun x => _], ffunE, ffunP   → domains/47_finfun.md
  nat, .+1, .-1, subn, leqP, ltnP, bool as nat → domains/49_nat_seq.md
  seq, nth, [seq _ | _ <- _], iota, \in on seq → domains/49_nat_seq.md

  MathComp book, mathcomp 1.x / Coq 8 code     → reference.md §48
```

If a question spans two files (e.g. "determinant of a permutation
matrix" needs both §38 and §46), Read both.
