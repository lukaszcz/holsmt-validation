# cvc5 CPC Seq/Set/Bag corpus

This Phase 6 corpus freezes cvc5 1.3.4 CPC output at `dsl-rewrite`
granularity for every cvc5-solvable
`theory:Z3_Extensions:*:unsat-proof` conformance input.  `inputs.txt` is the
manifest-selected list of 58 inputs: 17 Seq, 21 finite-Set, and 20 Bag
queries.  SAT, type-error, and P6.4 boundary rows are intentionally excluded:
they have no UNSAT CPC proof to record.

Regenerate it (and the companion Z3 corpus) from the validation-repository
root:

```sh
python3 tools/proof-corpus/seq_set_bag/record.py \
  --cvc5 "$HOME/.local/bin/cvc5" --skip-z3
```

The checked-in `cvc5-1.3.4` directory holds raw input/stdout/stderr/CPC
payloads and the recorder report.  It is evidence for future checked replay,
not a checked replay result.  In particular, every `trust` step remains a
named, untrusted replay obligation; recording never admits an oracle.
