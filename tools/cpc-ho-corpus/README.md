# cvc5 CPC higher-order corpus

This corpus freezes the native higher-order CPC vocabulary emitted by cvc5
1.3.4 at `dsl-rewrite` granularity.  It covers `@` application, curried and
partially applied functions, beta and eta conversion, alpha-renaming,
extensionality, lambda equality, and a lambda below a quantifier.

The six D3 proof-rule cases are checked through the complete conformance
suite.  They use the Z3-lowered input dialect by design, so they are not fed
directly to cvc5's native recorder.  The checked HOL driver translates those
terms back through the cvc5 Standard27 boundary.

From the validation repository root, recapture and replay with:

```sh
mapfile -t queries < <(grep -v '^[[:space:]]*#' \
  tools/cpc-ho-corpus/inputs.txt)
python3 tools/record_cvc5_cpc_corpus.py \
  --cvc5 "$HOL4_CVC_EXECUTABLE" \
  --granularity dsl-rewrite \
  --out /tmp/cvc5-cpc-ho-corpus "${queries[@]}"
tools/run_cvc5_cpc_gate.sh \
  --holsmt-root "$HOLSMT_ROOT" \
  --cvc5 "$HOL4_CVC_EXECUTABLE" \
  --input-list tools/cpc-ho-corpus/inputs.txt \
  --out /tmp/cvc5-cpc-ho-matrix.json
```

The checked-in `cvc5-1.3.4` directory is the recorder output used to promote
the corresponding HOL replay handlers.  A cvc5 bump must recapture the raw
proofs, compare the rule inventory, and pass every checked-replay matrix
entry before its version is added to the registry.
