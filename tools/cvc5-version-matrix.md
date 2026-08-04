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

| cvc5 version | FloatingPoint corpus | CPC FP export | Checked status |
| --- | --- | --- | --- |
| 1.3.4 | 44 queries, `--fp-exp`, 3,591,281 proof bytes | 22,118 steps, 50 rules, 88 `trust` (0.40%), 0 proof-size gates | 28 replay; 1 D12 gate; 13 `trust` obligations; 2 parse-time obligations |

The FP inventory is frozen at `dsl-rewrite` granularity.  All 42 observed
`ProofRule` names and all eight observed `RareRewrite` names are registered.
The FP-specific additions are checked handlers for `equiv_elim1`,
`bool-eq-true`, `bool-xor-comm`, `bool-xor-false`, and `bool-xor-true`;
the live matrix additionally required `bool-impl-true1`.  The `trust`
handler routes FP conclusions through `SmtFpProve` with no oracle fallback.

| FP obligation | Cases | 1.3.4 status |
| --- | ---: | --- |
| `trust`: cvc5 private `@fp.*` bit decomposition | 11 | parsed as free HOL bit-vectors; the missing relationship to the source FP term is rejected with `rule=trust; theory=fp` |
| `trust`: underspecified `fp.min_total` / `fp.max_total` | 2 | parsed as free HOL functions; the missing public/private operator bridge is rejected with `rule=trust; theory=fp` |
| CPC scale-certificate parsing | 2 | 0.75 MB / 1.31 MB proofs exceed both the 60 s matrix timeout and a 180 s audit timeout; tracked performance obligations |
| `trust`: symbolic add circuit residue | 1 | `CVC_CPC_TAC_RESOURCE_GATED`; D12 term-size diagnostic, 200001 observed / 200000 maximum |

The 28 checked cases cover arbitrary formats, every ground arithmetic
operator, all five FP literals and NaN payload equality, mixed-format and
Real/BV conversions, and symbolic negation/to-real normalization.  Every
successful theorem is kernel checked; the driver and selftests run
`Library.check_oracle_tags`.

The explicitly labeled `cvc5-oracle` conformance band has 38/38 passing FP
logic rows (SAT and UNSAT for each of 19 accepted FP-bearing logics).  Those
rows record solver answers only and do not create HOL theorems.

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
For the FP row, use `tools/cpc-fp-corpus/README.md`.  A version bump must
recapture with `--solver-arg=--fp-exp`, compare both rule namespaces, trust
density, and proof sizes against the 16 MB pre-parse gate, then rerun the
44-case checked matrix and the labeled FP `cvc5-oracle` conformance rows.

Only promote a new version after every matrix entry is a checked pass, an
enumerated D12 resource gate, or a named certificate-shape obligation in this
file, and after the version is added to the CPC rule registry.  Unknown rules
or an unregistered dialect are version-gated replay obligations, not
candidates for unchecked fallback.
