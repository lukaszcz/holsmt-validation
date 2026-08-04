# cvc5 CPC FloatingPoint corpus

This corpus freezes cvc5 1.3.4 CPC output for the Phase 5 FP seed set at
`dsl-rewrite` granularity.  The 44 inputs cover ground arithmetic and
conversions, literal normalization, arbitrary formats, the Float32
`fp.lt`/classification probe shapes, small-format symbolic comparisons and
classifications, and the D12 add/multiply scale exemplars.

cvc5 1.3.4 requires its experimental FP engine for formats other than
Float32 and Float64.  Both capture and checked replay therefore use
`--fp-exp`; this is solver configuration at the cvc5 boundary, not a trusted
HOL mechanism.

From the validation repository root, recapture with:

```sh
mapfile -t queries < <(
  git ls-files 'tools/proof-corpus/floatingpoint/inputs/*.smt2'
)
python3 tools/record_cvc5_cpc_corpus.py \
  --cvc5 "$HOL4_CVC_EXECUTABLE" \
  --solver-arg=--fp-exp \
  --granularity dsl-rewrite \
  --out /tmp/cvc5-cpc-fp-corpus "${queries[@]}"
```

After building the HOL driver, rerun the checked matrix with:

```sh
tools/run_cvc5_cpc_gate.sh \
  --holsmt-root "$HOLSMT_ROOT" \
  --cvc5 "$HOL4_CVC_EXECUTABLE" \
  --out /tmp/cvc5-cpc-fp-matrix.json "${queries[@]}"
```

The checked-in `cvc5-1.3.4` directory is the evidence used to freeze the
rule inventory.  A cvc5 bump must rerun both commands, compare both rule
namespaces and proof sizes against the 16 MB D12 limit, and keep every
unsupported shape as a named obligation rather than adding an oracle.
