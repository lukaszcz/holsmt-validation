#!/usr/bin/env python3
"""Build the checked Phase 4 string proof-corpus matrix summary."""

from __future__ import annotations

import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parent
TOOLS = ROOT.parents[1]
sys.path.insert(0, str(TOOLS))

from record_z3_proof_corpus import build_summary  # noqa: E402


HISTORICAL_ORDINARY_RULES = {
    "and-elim",
    "asserted",
    "def-axiom",
    "hypothesis",
    "iff-false",
    "iff-true",
    "lemma",
    "monotonicity",
    "mp",
    "rewrite",
    "symm",
    "trans",
    "trans*",
    "unit-resolution",
}
THEORY_RULES = {
    "th-lemma-arith",
    "th-lemma-char",
    "th-lemma-seq",
}


def load_json(path: pathlib.Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    manifest = load_json(ROOT / "manifest.json")
    assert isinstance(manifest, dict)
    cases = manifest["cases"]
    versions = manifest["supported_z3_versions"]
    assert isinstance(cases, list)
    assert isinstance(versions, list)

    matrix = []
    all_rules: set[str] = set()
    for version in versions:
        version_root = ROOT / f"z3-{version}"
        entries = [
            json.loads(line)
            for line in (version_root / "entries.jsonl").read_text(
                encoding="utf-8"
            ).splitlines()
        ]
        summary = load_json(version_root / "summary.json")
        gate = load_json(version_root / "rule-gate.json")
        assert summary == build_summary(entries)
        assert len(entries) == len(cases)
        assert all(
            item["solver"]["result"] == "unsat"
            and item["proof"]["available"]
            and item["z3"]["exit_code"] == 0
            and not item["z3"]["timed_out"]
            for item in entries
        )
        assert isinstance(gate, dict) and gate["passed"]

        escape_entry = next(
            item
            for item in entries
            if item["input"]["path"].endswith(
                "draft_literal_escapes.smt2"
            )
        )
        by_version = summary["rules_by_version"][0]
        rules = set(by_version["rules"])
        all_rules.update(rules)
        matrix.append(
            {
                "version": version,
                "entry_count": len(entries),
                "proof_count": sum(
                    1 for item in entries if item["proof"]["available"]
                ),
                "rule_gate_passed": gate["passed"],
                "rules": sorted(rules),
                "theory_lemma_histogram": (
                    by_version["theory_lemma_histogram"]
                ),
                "string_internal_symbols": (
                    by_version["string_internal_symbols"]
                ),
                "indexed_string_internal_symbols": (
                    by_version["indexed_string_internal_symbols"]
                ),
                "seq_prefix_symbols": by_version["seq_prefix_symbols"],
                "char_bit_indices": by_version["char_bit_indices"],
                "escape_output_spellings": sorted(
                    escape_entry["proof"]["string_shape"][
                        "string_literals"
                    ]
                ),
            }
        )

    result = {
        "schema": "holsmt-z3-string-proof-corpus-summary-v1",
        "case_count": len(cases),
        "drafting_probe_count": sum(
            1 for item in cases if "drafting_probe" in item
        ),
        "official_operator_count": len(
            {
                operator
                for item in cases
                for operator in item["operators"]
            }
        ),
        "matrix": matrix,
        "ordinary_rule_heads_outside_phase4_baseline": sorted(
            all_rules - HISTORICAL_ORDINARY_RULES - THEORY_RULES
        ),
        "theory_rule_heads": sorted(all_rules & THEORY_RULES),
    }
    (ROOT / "matrix-summary.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
