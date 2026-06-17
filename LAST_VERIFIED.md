# Verification dates for cite-heavy sections

The skill cites mathcomp source by `file:line`. Mathcomp source
files reorganize regularly (~10% annual rate); line numbers go
stale silently. This file stamps the **last date** each section
was end-to-end verified against an installed mathcomp.

If a user reports a stale citation in section §N, the date below
tells them whether the skill is fresh or old, and the rocq /
mathcomp version it was checked against.

## Target versions

Citations in this skill are verified against the versions in the
**Tested** column. The **Minimum** column reflects the lowest version
the skill is expected to be reasonably accurate against (lemma names
should resolve; line numbers may drift by tens of lines).

| Component                                   | Minimum | Tested              |
|---------------------------------------------|---------|---------------------|
| Rocq                                        | 9.0     | **9.1.1**           |
| mathcomp-ssreflect (+ boot/order/fingroup)  | 2.4.0   | **2.5.0**           |
| mathcomp-algebra                            | 2.4.0   | **2.5.0**           |
| mathcomp-field                              | 2.4.0   | **2.5.0**           |
| mathcomp-analysis (+ classical/reals)       | 1.13.0  | **1.16.0**          |
| mathcomp-zify                               | 1.5.0   | **1.6.0+2.3+8.18**  |
| mathcomp-algebra-tactics                    | 1.2.0   | **1.2.7**           |
| hierarchy-builder (HB)                      | 1.8.0   | **1.10.2**          |

If your installed versions differ: lemma **names** should still
resolve; **line numbers** in `file.v:line` citations may drift by
±5 to ±50 (see "What a stale citation looks like" below).

| Section(s) | Last verified | Rocq version | Mathcomp version | Audit notes |
|------------|---------------|--------------|------------------|-------------|
| §1-§32 (core conventions) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 / analysis 1.16.0 | v1 + v2 audits; PR citations may be stale (see §33 caveats) |
| §33 (PR Citation Index) | 2026-04-29 | n/a | n/a | Multiple citations flagged `[topic ≠ rule]`; treat as community-norm pointers, not authoritative |
| §34 (Bigops) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 | line numbers spot-checked against `boot/bigop.v`; ~28 lemmas verified |
| §35 (HB Factories) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 + HB 1.x | verified against `boot/nmodule.v`, `algebra/ssralg.v`, `mxalgebra.v`, `order.v` |
| §36 (Choice/Decidability) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 + analysis 1.16.0 | axiom names verified at `classical/boolp.v:83-89`, `pselect:227`, `cid:92` |
| §37 (Search Discipline) | 2026-04-30 | Rocq 9.1.1 | analysis 1.16.0 | `Search "_le"` etc. verified in current Rocq; `_subdef`/`_subproof` blacklist confirmed |
| §38 (`domains/38_matrix.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | ~35 lemmas line-cited from `algebra/matrix.v`; `mxE`/`matrixP` at 308/311 confirmed |
| §39 (`domains/39_polynomial.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | multi-rules `coefE`/`hornerE`/`derivE` confirmed at 2681/2726/1643 |
| §40 (`domains/40_finset.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | 29 lemmas verified at `boot/finset.v`; `inE` multirule at 376 |
| §41 (`domains/41_int_rat.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | `int` at `ssrint.v:70`; `divz`/`modz`/`gcdz` at `intdiv.v:53-69` |
| §42 (`domains/42_derive.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | `is_derive` Class at `derive.v:249`; 15 instance line numbers verified |
| §43 (`domains/43_measure.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | files in `lebesgue_integral_theory/`, `measure_theory/`, `probability_theory/` confirmed real |
| §44 (`domains/44_topology.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | `Filter`/`ProperFilter` at `classical/filter.v:430,444`; `nbhs_ballP`/`nbhs_normP` confirmed |
| §45 (`domains/45_algebra_tactics.md`) | 2026-04-29 | Rocq 9.1.1 | algebra-tactics 1.x + zify 1.x | `ring`/`field` at `ring.v:443,453`; `lra`/`nra`/`psatz` at `lra.v:403-407`; zify carrier coverage verified |
| §46 (`domains/46_tuple_perm_binomial.md`) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 | ~50 lemmas cited: `boot/tuple.v` (`tnth_nth:77`, `eq_from_tnth:96`, `card_tuple:422`), `fingroup/perm.v` (`permP:88`, `permM:128`, `card_Sn:597`), `boot/binomial.v` (`bin_fact:224`, `expnDn:298`, `Vandermonde:312`) |
| §47 (`domains/47_finfun.md`) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 | core lemmas verified at `boot/finfun.v`: `ffunE:175`, `ffunP:181`, `ffunK:194`, `eq_ffun:322`, `card_ffun:484`; `sum_ffunE` at `boot/nmodule.v:1293` |

## Re-validation script

**Shipped.** `scripts/check-citations.sh` greps `reference.md` and
`domains/*.md` for `file.v:line` and `` `ident` (l. NNN) `` citations
and verifies each named lemma still exists near that line in the
installed mathcomp (`$MATHCOMP_ROOT`, else
`$(rocqc -where)/user-contrib/mathcomp`, else the `coqc` equivalent).
It reports `OK` / `WARN` (line drifted past the `±N` tolerance, with a
suggested fix) / `ERROR` (file or identifier gone), exits non-zero on
ERROR (or on WARN under `--strict`), and **degrades gracefully to
exit 0** when mathcomp is not installed. See `scripts/README.md` for
flags and exit codes.

**How the weekly check works.** `.github/workflows/citations.yml`
runs on a Monday `schedule:` cron (plus manual `workflow_dispatch`),
opam-installs the pinned stack from the *Target versions* table above
(Rocq 9.1.1 / mathcomp 2.5.0 / analysis 1.16.0), and runs
`check-citations.sh --strict --require-mathcomp`. A failing run is the
drift alert: open the run log, read the `WARN`/`ERROR` lines, fix the
cited line numbers, and bump the relevant date in the table above.
Until a run fires, re-validation can still be done manually: run the
script locally against your install, or spot-check a sample of cited
lines and bump the date column.

## What a stale citation looks like

If line numbers in §N are wrong:
- The lemma name should still exist (rename is rare).
- The line number is off by ±5 to ±50 (typical post-refactor drift).
- Run `grep -n "Lemma <name>" /path/to/file.v` to find the new line.

If the file path itself is wrong:
- The mathcomp library reorganized (e.g. analysis split
  `lebesgue_integral.v` into the `lebesgue_integral_theory/`
  subdir during 2024).
- Check the analysis `CHANGELOG.md` for "moved to" entries.
- The file was renamed: `find /path/to/mathcomp -name "*.v" | xargs grep -l "Lemma <name>"`.
