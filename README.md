# HolSmt validation

Versioned conformance corpora, proof-replay evidence, external benchmark
snapshots, coverage reports, and validation tooling for HolSmt.

The data deliberately lives outside the HOL source repository.  The tools are
kept under `tools` to preserve stable corpus paths, but they operate
on a separate HolSmt source checkout selected by `HOLSMT_ROOT`.

With AGM, this checkout is normally at `$PROJ_DIR/deps/holsmt-validation/main`:

```sh
export HOLSMT_ROOT=$PROJ_DIR/worktrees/smt
export HOLSMT_VALIDATION_DIR=$PROJ_DIR/deps/holsmt-validation/main
python3 "$HOLSMT_VALIDATION_DIR/tools/run_conformance_suite.py" \
  --mode parser-only --out /tmp/holsmt-conformance
```

When an output option is omitted, validation tools write generated reports
under this validation checkout, independently of the caller's working
directory.  Explicit `--out` and `--out-dir` options still select any desired
location.

The cvc5 oracle runs the original benchmark text and checks its `sat` or
`unsat` result.  It is currently enabled for the higher-order extension band:

```sh
python3 "$HOLSMT_VALIDATION_DIR/tools/run_conformance_suite.py" \
  --mode cvc5-oracle --cvc5 cvc5 --out /tmp/holsmt-cvc5-oracle
```

If cvc5 is unavailable, rows are reported explicitly as `unsupported` with a
`tool-unavailable` classification; they are never counted as solver passes.

`HOLSMT_ROOT` must contain `src/HolSmt`; tools that need checked drivers expect
them at `$HOLSMT_ROOT/src/HolSmt/holsmt-typecheck` and
`$HOLSMT_ROOT/src/HolSmt/holsmt-z3-tac`.  Checked cvc5 CPC matrix runs use
`$HOLSMT_ROOT/src/HolSmt/holsmt-cvc-cpc-tac`; build it with
`Holmake -C "$HOLSMT_ROOT/src/HolSmt" holsmt-cvc-cpc-tac`.

The cvc5 CPC gate has a single entry point that builds that driver, runs every
query, writes the JSON matrix, and removes the generated launcher on exit:

```sh
HOLSMT_ROOT=$PROJ_DIR/worktrees/smt \
HOL4_CVC_EXECUTABLE=$HOME/.local/bin/cvc5 \
  tools/run_cvc5_cpc_gate.sh <queries>/*.smt2
```
