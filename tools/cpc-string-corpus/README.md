# cvc5 CPC string corpus

This corpus freezes cvc5 1.3.4 CPC output for the Phase 4 D2 proof-shape
inputs and the D5 curated string benchmarks.  The recorder uses
`dsl-rewrite` granularity and requests explicit conclusions so every named
string step can be audited independently of the HOL parser.

The checked-in baseline contains 52 queries, 48 CPC certificates, 2,130
steps, 76 distinct rule names, and no `trust` steps.  Three SAT inputs
correctly have no proof.  `draft_str_lt.smt2` times out after 30 seconds; a
ready-to-file issue draft records that reproducer in the HolSmt source
checkout.

The string inventory contains the three `string_*` proof rules and 24 RARE
rewrites recorded in `tools/cvc5-version-matrix.md`.  cvc5 did not emit the
generic `str` theory rule in this slice; it remains registered and
version-gated in the checker.

From the validation repository root, recapture with:

```sh
python3 tools/record_cvc5_cpc_corpus.py \
  --cvc5 "$HOL4_CVC_EXECUTABLE" \
  --granularity dsl-rewrite \
  --out /tmp/cvc5-cpc-string-corpus \
  tools/proof-corpus/strings/inputs/*.smt2 \
  tools/external-benchmarks/curated-small/strings/*.smt2
```

The D2 inputs intentionally retain their original Z3-oriented command order
and do not add native-string `wfstr` guards.  Consequently they are raw CPC
shape evidence, not all direct inputs to the checked benchmark driver.
Checked end-to-end evidence comes from the `thm_CVCp` selftest band and the
eligible D5 input.  A normalized pass over the 38 ground D2 inputs closes
17; every remaining certificate blocker is named in the version matrix.
Do not add an oracle fallback for those rows.

The exact paths in JSON artifacts record the checkout used for the frozen
run; content hashes in raw filenames and the raw payloads are the portable
evidence.
