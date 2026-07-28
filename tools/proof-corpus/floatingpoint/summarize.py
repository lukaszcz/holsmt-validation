#!/usr/bin/env python3
"""Summarize the checked Phase 5 FloatingPoint proof matrix."""

from __future__ import annotations

import collections
import json
import pathlib


ROOT = pathlib.Path(__file__).resolve().parent


def relative(value: str) -> str:
    path = pathlib.Path(value)
    parts = path.parts
    if "tools" in parts:
        return str(pathlib.Path(*parts[parts.index("tools") :]))
    return value


def main() -> None:
    manifest = json.loads((ROOT / "manifest.json").read_text())
    cases = {item["id"]: item for item in manifest["cases"]}
    versions = manifest["supported_z3_versions"]
    matrix: dict[str, object] = {
        "schema": "holsmt-z3-fp-proof-corpus-matrix-v1",
        "versions": [],
        "metadata_only_cases": manifest["metadata_only_cases"],
    }
    catalog: dict[str, object] = {
        "schema": "holsmt-z3-fp-rewrite-catalog-v1",
        "operators": {},
        "bit_decompositions": {},
    }
    operator_catalog: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    decomposition_catalog: dict[str, list[dict[str, object]]] = collections.defaultdict(list)

    for version in versions:
        version_root = ROOT / f"z3-{version}"
        entries = [
            json.loads(line)
            for line in (version_root / "entries.jsonl").read_text().splitlines()
        ]
        rows = []
        aggregate_rules: collections.Counter[str] = collections.Counter()
        for entry in entries:
            case_id = pathlib.Path(entry["input"]["path"]).stem
            metadata = cases[case_id]
            proof = entry["proof"]
            shape = proof["fp_shape"]
            aggregate_rules.update(proof["rule_histogram"])
            categories = collections.Counter(
                rewrite["category"] for rewrite in shape["rewrites"]
            )
            rows.append(
                {
                    "case_id": case_id,
                    "format": metadata["format"],
                    "result": entry["solver"]["result"],
                    "elapsed_seconds": entry["z3"]["elapsed_seconds"],
                    "proof_bytes": proof["raw_bytes"],
                    "proof_steps": proof["parsed_dag_summary"][
                        "proof_rule_application_count"
                    ],
                    "rules": sorted(proof["rule_histogram"]),
                    "bv_skolem_widths": sorted(
                        {item["width"] for item in shape["bv_skolems"]}
                    ),
                    "bool_skolem_count": shape["bool_skolem_count"],
                    "bit_decomposition_count": len(
                        shape["bit_decompositions"]
                    ),
                    "rewrite_categories": dict(sorted(categories.items())),
                }
            )
            proof_ref = relative(proof["raw_path"])
            for rewrite in shape["rewrites"]:
                names = rewrite["operators"]
                if not names:
                    if rewrite["category"] == "bit-decomposition":
                        names = ["$bit-decomposition"]
                    elif rewrite["category"] == "literal-normalization":
                        names = ["$literal-normalization"]
                    else:
                        names = ["$ground-fp-literal"]
                ref = {
                    "version": version,
                    "case_id": case_id,
                    "format": metadata["format"],
                    "category": rewrite["category"],
                    "proof_path": proof_ref,
                    "proof_sha256": proof["raw_sha256"],
                    "start_offset": rewrite["start_offset"],
                    "end_offset": rewrite["end_offset"],
                    "formula_bytes": rewrite["formula_bytes"],
                    "formula_sha256": rewrite["formula_sha256"],
                    "formula_roots": rewrite["formula_roots"],
                }
                if "formula" in rewrite:
                    ref["formula"] = rewrite["formula"]
                else:
                    ref["formula_prefix"] = rewrite["formula_prefix"]
                    ref["formula_suffix"] = rewrite["formula_suffix"]
                for name in names:
                    operator_catalog[name].append(ref)
            decomposition_catalog[version].extend(
                {
                    "case_id": case_id,
                    "format": metadata["format"],
                    "variable": item["variable"],
                    "skolem": item["skolem"],
                    "expanded_formula": item.get("expanded_formula"),
                    "proof_path": proof_ref,
                    "formula_sha256": item["formula_sha256"],
                }
                for item in shape["bit_decompositions"]
            )
        gate = json.loads((version_root / "rule-gate.json").read_text())
        matrix["versions"].append(
            {
                "version": version,
                "case_count": len(rows),
                "proof_count": sum(row["result"] == "unsat" for row in rows),
                "total_proof_bytes": sum(row["proof_bytes"] for row in rows),
                "rules": sorted(aggregate_rules),
                "rule_histogram": dict(sorted(aggregate_rules.items())),
                "th_lemma_fp_observed": any(
                    aggregate_rules[name] > 0
                    for name in (
                        "th-lemma-fp",
                        "th-lemma-fpa",
                        "th-lemma-floating-point",
                    )
                ),
                "rule_gate_passed": gate["passed"],
                "cases": rows,
            }
        )
    catalog["operators"] = dict(sorted(operator_catalog.items()))
    catalog["bit_decompositions"] = dict(sorted(decomposition_catalog.items()))
    (ROOT / "matrix-summary.json").write_text(
        json.dumps(matrix, indent=2, sort_keys=True) + "\n"
    )
    (ROOT / "rewrite-catalog.json").write_text(
        json.dumps(catalog, indent=2, sort_keys=True) + "\n"
    )


if __name__ == "__main__":
    main()
