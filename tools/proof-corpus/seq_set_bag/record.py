#!/usr/bin/env python3
"""Record the Phase 6 Seq/Set/Bag Z3 and cvc5 proof corpora."""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys


Z3_VERSIONS = ("4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3")
CVC5_VERSION = "1.3.4"


def phase6_cases(root: pathlib.Path, solver: str, version: str) -> list[pathlib.Path]:
    corpus = root / "tools/conformance-corpus/v2"
    manifest = json.loads((corpus / "manifest.json").read_text(encoding="utf-8"))
    result = []
    for case in manifest["cases"]:
        availability = case.get("solver_availability", {}).get(solver, [])
        if (
            case["id"].startswith("theory:Z3_Extensions:")
            and case["id"].endswith(":unsat-proof")
            and version in availability
        ):
            result.append(corpus / case["file"])
    return result


def run(command: list[str]) -> None:
    print("+", " ".join(str(item) for item in command), flush=True)
    subprocess.run(command, check=True)


def main(argv: list[str]) -> int:
    here = pathlib.Path(__file__).resolve().parent
    root = here.parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--z3-dir", type=pathlib.Path,
                        default=pathlib.Path.home() / ".local/bin")
    parser.add_argument("--cvc5", default=str(pathlib.Path.home() / ".local/bin/cvc5"))
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--skip-z3", action="store_true")
    parser.add_argument("--skip-cvc5", action="store_true")
    args = parser.parse_args(argv)

    z3_recorder = root / "tools/record_z3_proof_corpus.py"
    cpc_recorder = root / "tools/record_cvc5_cpc_corpus.py"
    probes = sorted((here / "inputs").glob("*.smt2"))
    if len(probes) != 4:
        raise ValueError("expected four focused Z3 shape probes")

    if not args.skip_z3:
        for version in Z3_VERSIONS:
            queries = phase6_cases(root, "z3", version) + probes
            run([
                sys.executable, str(z3_recorder),
                "--z3", str(args.z3_dir / f"z3-{version}"),
                "--z3-version", version,
                "--out", str(here / f"z3-{version}"),
                "--timeout", str(args.timeout),
                "--require-unsat-proofs", "--fail-on-unknown-rules",
                *(str(query) for query in queries),
            ])

    if not args.skip_cvc5:
        queries = phase6_cases(root, "cvc5", CVC5_VERSION)
        run([
            sys.executable, str(cpc_recorder),
            "--cvc5", args.cvc5,
            "--granularity", "dsl-rewrite",
            "--timeout", str(args.timeout),
            "--out", str(root / "tools/cpc-seq-set-bag-corpus/cvc5-1.3.4"),
            *(str(query) for query in queries),
        ])
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
