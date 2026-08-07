# Z3 Seq/Set/Bag proof corpus

This Phase 6 corpus freezes all currently enabled Z3-compatible
`theory:Z3_Extensions:*:unsat-proof` conformance cases, together with four
focused shape probes.  It covers the full five-version support matrix:
4.11.2, 4.12.4, 4.13.0, 4.14.1, and 4.15.3.

`conformance-unsat-inputs.txt` lists all 36 Z3-compatible conformance
inputs.  `seq.fold_left` and `seq.fold_lefti` are unavailable in 4.11.2, so
that anchor records 34 conformance inputs; every newer anchor records all 36.
The four inputs in `inputs/` force the non-trivial proof shapes needed by the
replay work: sequence length/nth, set subset (array), and encoded bag map plus
arithmetic.  Thus each version directory has 38 or 40 entries respectively.

The ordinary generated UNSAT inputs deliberately retain their source-coverage
role even where the solver simplifies their explicit contradiction before a
theory lemma is needed.  The focused probes prevent that simplification from
silently narrowing the replay evidence.

Regenerate the Z3 and cvc5 captures from the validation-repository root:

```sh
python3 tools/proof-corpus/seq_set_bag/record.py \
  --z3-dir "$HOME/.local/bin" \
  --cvc5 "$HOME/.local/bin/cvc5"
```

For a Z3-only refresh use `--skip-cvc5`; for CPC-only use `--skip-z3`.
The recorder requires an UNSAT proof for every selected Z3 query and fails on
an unknown proof head.  Every version directory contains the standard raw
stdout/stderr, extracted proofs, JSONL entries, summary, and rule gate.
Version-specific shape drift is deliberately recorded rather than normalized;
see `.agent-files/reports/phase6_proof_shape_inventory.md` in the HOL tree.
