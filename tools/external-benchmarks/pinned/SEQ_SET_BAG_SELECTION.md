# Phase 6 Seq/Set/Bag external selection

The six pins below are deliberately small SMT-LIB regression inputs fetched by
`tools/import_external_benchmarks.py` from raw, commit-pinned URLs. The
`t150.smt2` pin elides only its terminal blank line (recorded in its manifest
provenance); every other payload is unmodified. Their source lock entries and
manifest provenance record the repository, path, commit, SHA-256, and upstream
license notice. Z3's
`z3test` is MIT licensed (`LICENSE.txt`); cvc5 is modified BSD 3-clause
(`COPYING`).  No upstream suite is vendored.

## Taken

| Solver dialect | Upstream regression | Matrix/boundary evidence |
| --- | --- | --- |
| Z3 | `regressions/smt2/2417.smt2` | Native `Seq BitVec`, `seq.len`, `seq.extract`, and a SAT result. |
| Z3 | `regressions/smt2/3695.smt2` | Z3 `(Set (_ BitVec 1))` array-set syntax and finite-domain extensionality. |
| Z3 | `regressions/smt2/t150.smt2` | Z3 `(_ map ...)` nested-array bag-count encoding and pointwise addition. |
| cvc5 1.3.4 | `test/regress/cli/regress0/seq/nth-oob.smt2` | cvc5-only `seq.update` and negative/out-of-range `seq.nth`. |
| cvc5 1.3.4 | `test/regress/cli/regress0/sets/card-2.smt2` | Native finite `set.card` and `set.union`. |
| cvc5 1.3.4 | `test/regress/cli/regress1/bags/proj-issue584.smt2` | Native `bag.card`, `bag.inter_min`, and `bag.empty`. |

The Z3 inputs intentionally omit `set-logic`, as accepted by Z3's own
regression runner.  They are therefore pinned for parser and Z3-oracle
coverage, not falsely advertised as HolSmt typecheck cases.  The cvc5 inputs
have parser and cvc5-oracle passes; their `typecheck-only` rows are explicit
red Phase-6 translation obligations until the native builders land.

## Skipped

- Large cvc5 SQL/table, tuple, nullable, SyGuS, and finite-model-finding
  regressions were skipped: their non-Seq/Set/Bag surface would obscure the
  Phase-6 signal and make unsuitable CI inputs.
- cvc5's higher-order `bag.map`/`bag.filter` and set-comprehension regressions
  were skipped here because they combine the bag/set work with HO/table or
  quantifier machinery; the focused matrix/corpus owns those combinations.
- Z3 `testmap.smt2`, `testmapi.smt2`, and `testfoldl.smt2` were skipped because
  their interactive `simplify`/`eval` command streams are outside the
  conformance command surface. Model-validation regressions whose assertion
  is an invalid-model diagnostic were likewise skipped; `2417.smt2` is kept
  because its theory assertion has a stable SAT result at every supported Z3
  anchor.
- No native Z3 Bag test exists: Z3 has no `Bag` sort. `t150.smt2` is the
  applicable upstream evidence because the Phase-6 Z3 dialect represents bags
  with integer arrays and `(_ map ...)`.

## Recorded verification (2026-08-07)

`python3 tools/import_external_benchmarks.py` followed by `--check` was
idempotent. A focused v2 run over these six pins recorded six parser passes,
three cvc5-oracle passes, three Z3-oracle passes, and three expected red
`typecheck-only` gaps (the native cvc5 Seq/Set/Bag builders). No focused row
was unexpected. A full v2 parser-mode run recorded 1,766 matched rows and two
pre-existing expected implementation gaps, with zero unexpected regressions.
