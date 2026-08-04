# Z3 FloatingPoint proof corpus

This Phase 5 corpus freezes fpa2bv proof shapes across Z3 4.11.2,
4.12.4, 4.13.0, 4.14.1, and 4.15.3. Its 109 UNSAT inputs include the exact 51
TASK05 semantic scripts and 14 recorded TASK06 special cases, plus the 44
focused shape probes. They cover ground arithmetic, remainder and rounding,
every conversion family (including RNA, mixed formats, BV and real
conversions), symbolic comparisons and classifications, abs/neg, literal
normalization, NaN equality, arbitrary formats, and the D12 tiny-format
`fp.add` exemplar.

The Float32 symbolic-add proof is intentionally not present: `manifest.json`
records the drafting measurement (891 MiB, 65 s) as metadata only. Recording
that payload is forbidden by the task because it is far beyond the 16 MiB D12
budget.

Every recorded source-linked proof is under 16 MiB in all five versions; the
largest is 1,853,207 bytes. `matrix-summary.json` records that rewrite-category
shapes are stable. The sole rule-set difference is the already-supported
`symm` rule in the symbolic `fp.to_real` bridge, so no widening of the
two-version `holsmt-z3-selftest` matrix is required.

Regenerate inputs and derived summaries:

```sh
python3 tools/proof-corpus/floatingpoint/generate.py
python3 tools/proof-corpus/floatingpoint/summarize.py
```

Record and gate one version:

```sh
version=4.15.3
python3 tools/record_z3_proof_corpus.py \
  --z3 "$HOME/.local/bin/z3-$version" \
  --z3-version "$version" \
  --out "tools/proof-corpus/floatingpoint/z3-$version" \
  --fp-corpus \
  --timeout 120 \
  --expected-rules tools/proof-corpus/floatingpoint/expected_rules.json \
  --fail-on-unseen-rules \
  --fail-on-unknown-rules \
  --forbid-rule-occurrence th-lemma-fp \
  --forbid-rule-occurrence th-lemma-fpa \
  --forbid-rule-occurrence th-lemma-floating-point
```

Each version directory contains inputs' raw stdout/stderr, extracted proof
payloads, normalized entries with exact fpa2bv rewrite offsets and hashes,
a summary, and a passing rule gate. `rewrite-catalog.json` indexes exact
atom-conversion, ground-evaluation, literal-normalization, and bit-decomposition
forms back into those payloads. `matrix-summary.json` is the compact per-case
size and solve-time table.
