# HolSmt External Benchmark Layer

This directory contains the checked-in, small external benchmark slice used by
default CI.  It is deliberately not a vendored SMT-LIB benchmark checkout.
Large official SMT-LIB and Z3 regression suites should be kept outside the
repository and passed to `run_conformance_suite.py` with:

```sh
python3 tools/run_conformance_suite.py \
  --no-default-suite \
  --benchmark-dir /path/to/smtlib-benchmarks \
  --z3-proof-dir /path/to/z3/regressions \
  --regression-dir tools/external-benchmarks/local-regressions \
  --out /tmp/holsmt-external-benchmarks
```

`sources.json` records the upstream sources and exact pins used when refreshing
curated or scheduled benchmark runs.  Refreshing a large suite should update the
pin first, then preserve any failing input as a minimized `.smt2` under a local
regression directory.

The `ho/` slice is a four-case, checked-in selection of small TPTP-derived
SMT-LIB 2.7 higher-order benchmarks. Its entries are pinned in
`pinned/manifest.json` to the SMT-LIB benchmark-submission commit; the
importer hash-checks the local payloads before copying them into the v2 corpus.
The UNSAT cases carry checked `cvc5-oracle` expectations, and two lowerable
cases also carry `z3-tac` spot-check expectations.

`pinned/manifest.json` is the reduced mandatory checked-in slice.  Refresh it
with:

```sh
python3 tools/import_external_benchmarks.py
```

The importer verifies each pinned SHA256 before writing the case file or merging
the `class = external-benchmark` row into the v2 conformance manifest.  It keeps
large upstream archives out of the repository; only the reduced imported `.smt2`
cases are checked in.

The conformance report keeps external benchmark evidence separate from focused
row-level coverage evidence.  Benchmark runs may support a row, but they must
not replace the manifest's required positive tests, exact unsupported
diagnostics, parse-only justifications, or proof-version evidence.

Default CI should run `curated-small` in parser mode.  Scheduled or manual CI
can point `HOLSMT_LARGE_BENCHMARK_DIR`, `HOLSMT_Z3_PROOF_DIR`, and
`HOLSMT_REGRESSION_DIR` at larger local checkouts without downloading them
during ordinary tests.
