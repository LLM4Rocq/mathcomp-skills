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

Facts marked *analysis 1.16* (the `all_ssreflect_compat` shim,
SsrOldRewriteGoalsOrder porting comments) were checked against the
1.16.0 sources; a 1.15 install does not have them.

| Section(s) | Last verified | Rocq version | Mathcomp version | Audit notes |
|------------|---------------|--------------|------------------|-------------|
| §1-§32 (core conventions) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 / analysis 1.16.0 | v1 + v2 audits; PR citations may be stale (see §33 caveats) |
| §3, §5 (imports, header flags) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 / analysis 1.15.0 | flags at `boot/ssreflect.v:4-6`; `all_ssreflect.v` deprecated since 2.5.0; `all_ssreflect_compat.v` (mathcomp-classical ≥ 1.16) and the SsrOldRewriteGoalsOrder porting comments (`dedekind.v`, `realseq.v`) checked against the analysis 1.16.0 sources, absent from the 1.15.0 install; analysis cited without line numbers, not re-verified here |
| §25.5, §26.5, §27.9-§27.12 (bookkeeping) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `Test Bullet Behavior` = "None"; rewrite side-goal order checked under both `SsrOldRewriteGoalsOrder` settings; snippets compiled; `boot/ssrnat.v`, `boot/bigop.v`, `boot/monoid.v`, `boot/finset.v`, `algebra/matrix.v` cites checked |
| §28.1 (case specs) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `boot/ssrnat.v` `leP:500` `ltP:520` `leqP:922` `ltnP:933` `posnP:941` `ltngtP:953`; `lerP` at `algebra/num_theory/numdomain.v:2654`; `comparable_leP` at `order/order.v:1866` |
| §29.8-§29.9, §30.7-§30.8, §32.5-§32.6 | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `simpl never` nat operators at `boot/ssrnat.v:194`; snippets compiled; few line cites (`boot/ssrnat.v`, `boot/bigop.v`) |
| §33 (PR Citation Index) | 2026-04-29 | n/a | n/a | Multiple citations flagged `[topic ≠ rule]`; treat as community-norm pointers, not authoritative |
| §34 (Bigops) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 | line numbers spot-checked against `boot/bigop.v`; ~28 lemmas verified |
| §34.10 (custom Monoid laws) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `Monoid` factories at `boot/bigop.v:340-462`, library instances l. 532-556; `algebra/ssralg.v:1070, 2974`; `boot/nmodule.v:398`; `Monoid.isComLaw.Build` snippet compiled |
| §35 (HB Factories) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 + HB 1.x | verified against `boot/nmodule.v`, `algebra/ssralg.v`, `mxalgebra.v`, `order.v` |
| §36 (Choice/Decidability) | 2026-04-30 | Rocq 9.1.1 | mc 2.5.0 + analysis 1.16.0 | axiom names verified at `classical/boolp.v:83-89`, `pselect:227`, `cid:92` |
| §36.12 (instances for new types) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `boot/eqtype.v` l. 748-770; `boot/choice.v` GenTree l. 164, l. 545; `boot/fintype.v` l. 183, 207, 1316, 1416-1418, 1727, 1772; snippets compiled |
| §36.13 (sub-types) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `boot/eqtype.v` l. 287, 326, 564-642, 793, 799; `boot/tuple.v:63`, `boot/fintype.v:1731`, `algebra/matrix.v:287`, `boot/finfun.v:506`; snippets compiled |
| §37 (Search Discipline) | 2026-04-30 | Rocq 9.1.1 | analysis 1.16.0 | `Search "_le"` etc. verified in current Rocq; `_subdef`/`_subproof` blacklist confirmed |
| §37.12-§37.13 (inspection, statement shape) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `About`/`Print`/`Locate`/`Fail` output checked; `leq_trans` (ssrnat l. 398), `le_trans` (preorder l. 1043), `pdivP` (prime l. 561) |
| §48 (MCB → mathcomp 2.5 map) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 + HB 1.10.2 | removed book names checked with `Fail Check`, modern names resolve; deprecated ring notations at `algebra/ssralg.v:7081` warn, `unitRingType` does not; `algebra/zmodp.v:152, 252`; `boot/eqtype.v` l. 596-799 |
| §38 (`domains/38_matrix.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | ~35 lemmas line-cited from `algebra/matrix.v`; `mxE`/`matrixP` at 308/311 confirmed |
| §38.10 (dimension casts) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `castmx`/`conform_mx` family at `algebra/matrix.v` l. 389-602; `boot/fintype.v:1808`, `boot/tuple.v:135` |
| §39 (`domains/39_polynomial.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | multi-rules `coefE`/`hornerE`/`derivE` confirmed at 2681/2726/1643 |
| §40 (`domains/40_finset.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | 29 lemmas verified at `boot/finset.v`; `inE` multirule at 376 |
| §41 (`domains/41_int_rat.md`) | 2026-05-04 | Rocq 9.1.1 | mc 2.5.0 | `int` at `algebra/ssrint.v:70`; `divz`/`modz`/`gcdz` at `algebra/intdiv.v:53-69` |
| §41.7 (`'Z_p`, `'I_p`, `inZp`) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `algebra/zmodp.v` l. 258-384 (`Zp_nat`, `Zp_cast`, `pchar_Zp`, `card_Fp`, ...) |
| §42 (`domains/42_derive.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | `is_derive` Class at `analysis/derive.v:249`; 15 instance line numbers verified |
| §43 (`domains/43_measure.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | files in `lebesgue_integral_theory/`, `measure_theory/`, `probability_theory/` confirmed real |
| §44 (`domains/44_topology.md`) | 2026-05-04 | Rocq 9.1.1 | analysis 1.16.0 | `Filter`/`ProperFilter` at `classical/filter.v:430,444`; `nbhs_ballP`/`nbhs_normP` confirmed |
| §45 (`domains/45_algebra_tactics.md`) | 2026-04-29 | Rocq 9.1.1 | algebra-tactics 1.x + zify 1.x | `ring`/`field` at `algebra_tactics/ring.v:443,453`; `lra`/`nra`/`psatz` at `algebra_tactics/lra.v:403-407`; zify carrier coverage verified |
| §46 (`domains/46_tuple_perm_binomial.md`) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 | ~50 lemmas cited: `boot/tuple.v` (`tnth_nth:77`, `eq_from_tnth:96`, `card_tuple:422`), `fingroup/perm.v` (`permP:88`, `permM:128`, `card_Sn:597`), `boot/binomial.v` (`bin_fact:224`, `expnDn:298`, `Vandermonde:312`) |
| §46.2 (canonical tuple instances) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | `[isSub for tval]` at `boot/tuple.v:63`; `size_tuple` heads at l. 120-237, 427-443; snippets compiled |
| §47 (`domains/47_finfun.md`) | 2026-04-29 | Rocq 9.1.1 | mc 2.5.0 | core lemmas verified at `boot/finfun.v`: `ffunE:175`, `ffunP:181`, `ffunK:194`, `eq_ffun:322`, `card_ffun:484`; `sum_ffunE` at `boot/nmodule.v:1293` |
| §49 (`domains/49_nat_seq.md`) | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | 95 line cites, mostly `boot/ssrnat.v` and `boot/seq.v` (e.g. `leqP` l. 922, `subnK` l. 586, `nth_map` l. 2503); all snippets compiled |
| `templates.md` §21-§23 | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | skeletons and examples compiled; cites (`ubnP` l. 484, `seq_ind2` l. 981, `inj_eqAxiom` at `boot/eqtype.v:758`) checked by hand: `check-citations.sh` does not scan templates.md |
| `errors.md` §7-§9 | 2026-09-29 | Rocq 9.1.1 | mc 2.5.0 | error and warning texts reproduced verbatim; `boot/prime.v:623` checked by hand (not scanned by `check-citations.sh`) |

## Re-validation script

**Shipped.** `scripts/check-citations.sh` greps `reference.md` and
`domains/*.md` for `file.v:line` and `` `ident` (l. NNN) `` citations
and verifies each named lemma still exists near that line in the
installed mathcomp (`$MATHCOMP_ROOT`, else
`$(rocq c -where)/user-contrib/mathcomp`, else the `coqc` equivalent).
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
