# HolSmt Coverage Manifest Audit

The manifest in `coverage_manifest.json` is the evidence checklist for rows in
`smtlib_coverage.json`. It is intentionally small at first; later coverage
tasks should add rows as executable evidence is created.

Run the enforcing audit with:

```sh
python3 tools/coverage/audit_coverage_manifest.py --enforce
```

The default mode still validates the manifest and prints missing row-level
obligations without failing, but CI always uses `--enforce`. Enforcing mode
rejects unresolved `unknown` or `untested` rows, implemented rows without
positive executable evidence, unsupported-diagnostic rows without negative
diagnostic evidence, and stale or missing proof-version evidence. The
checked-in supported-version and complete proof summaries are loaded as
default `--proof-report` inputs; pass additional `--proof-report` paths when
auditing freshly recorded Z3 proof-corpus runs.

The COMPLETE audit reads the generated v2 `logics.json` contract by default,
so aggregate/internal and cvc5-extension exclusions agree with corpus
generation. `--logic-source` is retained as a fallback when that JSON does
not exist.

Add one manifest entry per coverage row, using the exact `section`, `item`, and
`class` values from `smtlib_coverage.json`. Put the covered status columns in
`phases`, and set `expected_status` to the status those phases must have. Use:

- `positive_tests` for implemented behavior that should pass.
- `negative_tests` for unsupported behavior that must produce an exact
  diagnostic.
- `z3_versions` for proof-corpus rows that must be supported by specific Z3
  versions.
- `artifacts` for source files, checked-in reports, parse-only justifications,
  or not-applicable explanations.

The audit understands `source`, `conformance_result`, `proof_rule`,
`proof_version`, and `manual` evidence kinds. Source evidence checks that the
path exists and, when `match` is present, that the text appears in the file.
When no generated COMPLETE case maps to a row, validated positive executable
evidence supplies that row's `complete_test_ids`; an actual red case always
takes precedence. This keeps version, proof-wrapper, and source-level audit
rows from becoming red merely because they have no natural generated script.
Conformance and proof evidence is checked only when report paths are supplied
with `--conformance-report` or `--proof-report`. For release validation, pass
the locally generated parser, Z3 oracle/proof, typecheck-only, and checked
`Z3_TAC` reports to the enforcing audit.
