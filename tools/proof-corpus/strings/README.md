# Z3 string and regex proof corpus

This Phase 4 corpus freezes raw Z3 proof shapes for:

- the eleven planning probes;
- one unsat input for each of the 21 `str.*` and 13 `re.*`
  operators in the current official surface;
- the missing frontend entries `re.comp` and `(_ char H)`;
- proof-output spellings for representative SMT-LIB string escapes.

Regenerate the deterministic input set:

```sh
python3 tools/proof-corpus/strings/generate.py
python3 tools/proof-corpus/strings/summarize.py
```

Record and gate one supported Z3 version:

```sh
version=4.15.3
python3 tools/record_z3_proof_corpus.py \
  --z3 "$HOME/.local/bin/z3-$version" \
  --z3-version "$version" \
  --out "tools/proof-corpus/strings/z3-$version" \
  --string-corpus \
  --expected-rules tools/proof-corpus/strings/expected_rules.json \
  --fail-on-unseen-rules \
  --fail-on-unknown-rules \
  --require-rule-occurrence th-lemma-seq \
  --require-rule-occurrence th-lemma-char \
  --require-theory-subkind 'seq:*' \
  --require-theory-subkind 'char:*'
```

Every checked-in version directory contains the raw solver output,
extracted proof payloads, normalized entries and summary, and a passing
`rule-gate.json`. The exact paths in JSON artifacts record the checkout
used for the frozen run; hashes and raw payloads are the portable
evidence.
