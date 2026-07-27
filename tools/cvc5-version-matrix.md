# cvc5 CPC version matrix

The checked cvc5 proof path uses native CPC output with:

```
--produce-proofs --dump-proofs --proof-format-mode=cpc \
--proof-granularity=dsl-rewrite --lang smt
```

The corpus recorder additionally uses `--proof-print-conclusion`.  That
inspection option is deliberately not enabled by the live checked driver:
existing non-string handlers reconstruct their certificate conclusions in
HOL-normal forms.

| cvc5 version | CPC mode | Checked corpus result | Status |
| --- | --- | --- | --- |
| 1.3.4 | `dsl-rewrite` | 60/60 captured queries; 6/6 datatype conformance cases | supported |

| cvc5 version | HO logics and surface | CPC HO export | Checked HO replay |
| --- | --- | --- | --- |
| 1.3.4 | `HO_*`; arrows, lambda, `@`, omission/partial-application extension | 9/9 native queries, 155 steps, 30 rules | 9/9 native queries plus the `thm_CVCp` selftest band |

| cvc5 version | String corpus | CPC string export | Checked status |
| --- | --- | --- | --- |
| 1.3.4 | 52 D2/D5 queries; 48 proofs; 2,130 steps | 3 `string_*` rules, 24 string RARE rewrites, 0 `trust`; `str` not observed | 17/38 normalized ground inputs replay; remaining certificate blockers are named below |

| Namespace | CPC name | 1.3.4 status |
| --- | --- | --- |
| ProofRule | `str` | registered; no corpus occurrence |
| ProofRule | `string_eager_reduction` | Boolean target routed to checked string re-prover |
| ProofRule | `string_length_pos` | obligation: omitted target requires rule-specific reconstruction |
| ProofRule | `string_reduction` | Boolean target routed to checked string re-prover |
| RareRewrite | `re-all-elim` | obligation: RegLan language equivalence is not HOL datatype equality |
| RareRewrite | `re-concat-merge` | obligation: omitted structural target |
| RareRewrite | `re-diff-elim` | obligation: RegLan language equivalence is not HOL datatype equality |
| RareRewrite | `re-in-comp` | obligation: omitted membership target |
| RareRewrite | `re-in-cstring` | obligation: omitted membership target |
| RareRewrite | `re-inter-cstring` | obligation: proof-local unary `re.inter` term is not parsed yet |
| RareRewrite | `re-loop-elim` | obligation: proof-local compact `re.loop` term is not parsed yet |
| RareRewrite | `re-opt-elim` | obligation: RegLan language equivalence is not HOL datatype equality |
| RareRewrite | `re-plus-elim` | obligation: RegLan language equivalence is not HOL datatype equality |
| RareRewrite | `re-repeat-elim` | obligation: proof-local compact `re.^` term is not parsed yet |
| RareRewrite | `str-concat-clash-rev` | obligation: omitted concat target |
| RareRewrite | `str-concat-unify-rev` | obligation: omitted concat target |
| RareRewrite | `str-contains-concat-find` | obligation: omitted contains target |
| RareRewrite | `str-in-re-eval` | Boolean target routed to checked regex re-prover |
| RareRewrite | `str-in-re-range-elim` | obligation: omitted membership target |
| RareRewrite | `str-in-re-union-elim` | obligation: omitted membership target |
| RareRewrite | `str-is-digit-elim` | rule-specific target reconstructed and checked |
| RareRewrite | `str-len-concat-rec` | obligation: omitted length target |
| RareRewrite | `str-lt-elim` | rule-specific target reconstructed and checked |
| RareRewrite | `str-replace-re-all-eval` | Boolean target routed to checked string re-prover |
| RareRewrite | `str-replace-re-eval` | Boolean target routed to checked string re-prover |
| RareRewrite | `str-substr-empty-range` | obligation: omitted substring target |
| RareRewrite | `str-substr-empty-str` | obligation: omitted substring target |
| RareRewrite | `str-substr-eq-empty` | obligation: omitted substring target |

The normalized ground replay pass also records two surrounding CPC-core
obligations rather than attributing them to a string RARE handler:

- `trans` composes an equality with cvc5's Boolean equality-normalization in
  12 ground certificates; the existing trans handler rejects the reversed
  intermediate orientation.
- `evaluate` in `extra_char_constant` leaves a normalized string-character
  hypothesis that the final CPC hypothesis check cannot match to the source
  assertion.

`re-inter-cstring`, `re-loop-elim`, and `re-repeat-elim` currently fail while
parsing cvc5's proof-local unary/index-flattened regex annotations.  These
remain named obligations, not unchecked admissions.

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
For the string row, use `tools/cpc-string-corpus/README.md`, compare all named
rows above, run the checked `thm_CVCp` selftest band, and run the
`cvc5-oracle` conformance mode as an explicitly labeled solver-result check.

Only promote a new version after every matrix entry reports
`CVC_CPC_TAC_PASS` and the corresponding version is added to the CPC rule
registry. Unknown rules or a known rule from an unregistered cvc5 version are
version-gated replay obligations, not candidates for unchecked fallback.
