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

`HOLSMT_ROOT` must contain `src/HolSmt`; tools that need checked drivers expect
them at `$HOLSMT_ROOT/src/HolSmt/holsmt-typecheck` and
`$HOLSMT_ROOT/src/HolSmt/holsmt-z3-tac`.  Checked cvc5 CPC matrix runs use
`$HOLSMT_ROOT/src/HolSmt/holsmt-cvc-cpc-tac`; build it with
`Holmake -C "$HOLSMT_ROOT/src/HolSmt" holsmt-cvc-cpc-tac`.
