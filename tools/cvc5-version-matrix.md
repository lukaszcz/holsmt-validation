# cvc5 CPC version matrix

The checked cvc5 proof path uses native CPC output with:

```
--produce-proofs --dump-proofs --proof-format-mode=cpc \
--proof-granularity=dsl-rewrite --lang smt
```

| cvc5 version | CPC mode | Checked corpus result | Status |
| --- | --- | --- | --- |
| 1.3.4 | `dsl-rewrite` | 60/60 captured queries; 6/6 datatype conformance cases | supported |

| cvc5 version | HO logics and surface | CPC HO export | Checked HO replay |
| --- | --- | --- | --- |
| 1.3.4 | `HO_*`; arrows, lambda, `@`, omission/partial-application extension | 9/9 native queries, 155 steps, 30 rules | 9/9 native queries plus the `thm_CVCp` selftest band |

The 1.3.4 corpus was captured on 2026-07-14 and replayed again on
2026-07-15 against the current checker: all 60 retained post-preprocessing
queries and all 6 datatype conformance cases passed.  It has no CPC `trust`
steps at the pinned granularity.
The datatype conformance slice covers constructor disjointness, mutual,
parametric, and recursive declarations, selectors, and constructor/tester
terms.  Its QF_DT disjointness seed declares `Color` with `red` and `blue`,
asserts `(= red blue)`, and replays to the HOL theorem `~(red = blue)`.

The higher-order row is recorded under `tools/cpc-ho-corpus/`.  Its two
exported `trust` steps are not oracle admissions: the HOL CPC `trust`
handler independently reproves their explicit propositions and the final
theorems pass `Library.check_oracle_tags`.  cvc5 1.3.4 rejects standard
SMT-LIB 2.7 `(_ f x)` application syntax and accepts its `(@ f x)`
extension; the HOL cvc5 boundary therefore emits `@` while the shared parser
continues to accept both standard spellings.

For a cvc5 upgrade, capture the generated SMT-LIB inputs and run:

```
python3 "$HOLSMT_VALIDATION_DIR/tools/record_cvc5_cpc_corpus.py" \
  --cvc5 "$HOL4_CVC_EXECUTABLE" --out /tmp/cvc5-cpc-corpus <queries>/*.smt2
"$HOLSMT_VALIDATION_DIR/tools/run_cvc5_cpc_gate.sh" \
  --out /tmp/cvc5-cpc-matrix.json <queries>/*.smt2
```

For the HO row, use `tools/cpc-ho-corpus/inputs.txt` and the exact commands
in its README.  Recheck logic acceptance, `@` application, partial
application, lambda export, the CPC inventory, and checked replay together.

Only promote a new version after every matrix entry reports
`CVC_CPC_TAC_PASS` and the corresponding version is added to the CPC rule
registry. Unknown rules or a known rule from an unregistered cvc5 version are
version-gated replay obligations, not candidates for unchecked fallback.
