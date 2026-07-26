#!/usr/bin/env python3

import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from record_z3_proof_corpus import (
    DEFAULT_COMPLETE_CORPUS_MANIFEST,
    DEFAULT_STRING_CORPUS_MANIFEST,
    DEFAULT_SUPPORTED_VERSION_MANIFEST,
    HO_PROOF_CORPUS_CASE_IDS,
    PARSE_ONLY_RULES,
    REPLAY_SUPPORTED_RULES,
    RULE_PREMISE_KIND,
    STRING_DRAFTING_PROBES,
    STRING_OFFICIAL_OPERATORS,
    build_requirement_report,
    build_rule_gate_report,
    build_summary,
    classify_ho_shape,
    expected_rules_for_version,
    extract_rule_report,
    inputs_from_complete_manifest,
    inputs_from_string_manifest,
    sha256_file,
    validation_relative_path,
    validate_corpus_manifest,
    validate_ho_shape_matrix,
)


def entry(path, version, proof):
    return {
        "input": {
            "path": path,
            "sha256": "input-hash",
            "effective_sha256": "effective-input-hash",
        },
        "z3": {
            "version": version,
            "stdout_path": "raw/stdout.txt",
            "stderr_path": "raw/stderr.txt",
        },
        "proof": {
            "available": True,
            "raw_path": "proofs/input.proof",
            "raw_sha256": "proof-hash",
            **proof,
        },
        "holsmt": {
            "proof_replay_status": "not-run",
            "replay_result": {"status": "not-run", "checked": False},
        },
        "theorem": {
            "tag_summary": {
                "checked": False,
                "oracle_tags": [],
                "axiom_tags": [],
                "unexpected_tags": [],
                "has_oracles": False,
                "has_axioms": False,
            }
        },
    }


class ProofRuleExtractionTests(unittest.TestCase):
    def proof_fragment_for_rule(self, rule):
        if rule.startswith("th-lemma-"):
            theory = rule.removeprefix("th-lemma-")
            return f"((_ th-lemma {theory}) (asserted a) false)"
        if rule == "rewrite":
            return "((_ rewrite) false)"

        premise_kind = RULE_PREMISE_KIND[rule]
        if premise_kind == "zero":
            return f"({rule} false)"
        if premise_kind == "one":
            return f"({rule} (asserted a) false)"
        if premise_kind == "two":
            return f"({rule} (asserted a) (asserted b) false)"
        if premise_kind == "list":
            return f"({rule} (asserted a) (asserted b) false)"
        self.fail(f"unsupported synthetic premise kind for {rule}: {premise_kind}")

    def test_extracts_histogram_from_z3_v4_wrapper(self):
        proof = """((set-logic QF_UF)
(proof
(let (($x25 (not a)))
 (let ((@x26 (asserted $x25)))
 (let ((@x24 (asserted a)))
 (unit-resolution @x24 @x26 false))))))
"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"]["asserted"], 2)
        self.assertEqual(report["rule_histogram"]["unit-resolution"], 1)
        self.assertEqual(sorted(report["rule_contexts"]), ["asserted", "unit-resolution"])
        self.assertEqual(report["unknown_rules"], [])
        self.assertEqual(report["malformed_fragments"], [])

    def test_all_core_replay_rules_have_raw_proof_extraction_coverage(self):
        core_rules = sorted(
            rule for rule in REPLAY_SUPPORTED_RULES if not rule.startswith("th-lemma-")
        )
        proof = "(proof\n  " + "\n  ".join(
            self.proof_fragment_for_rule(rule) for rule in core_rules
        ) + "\n)"

        report = extract_rule_report(proof)

        for rule in core_rules:
            self.assertIn(rule, report["rule_histogram"])
        self.assertEqual(report["unknown_rules"], [])
        self.assertEqual(report["malformed_fragments"], [])

    def test_parse_only_rule_is_recorded_but_not_replay_unknown(self):
        proof = "(proof (proof-bind (asserted false)))"
        report = extract_rule_report(proof)
        gate = build_rule_gate_report(
            [entry("proof-bind.smt2", "4.12.4", report)],
            {"default": ["asserted", "proof-bind"]},
        )

        self.assertEqual(PARSE_ONLY_RULES, {"proof-bind"})
        self.assertEqual(report["rule_histogram"]["proof-bind"], 1)
        self.assertEqual(report["unknown_rules"], [])
        self.assertTrue(gate["passed"])
        self.assertEqual(gate["replay_unknown_rules"], [])
        self.assertEqual(gate["parse_only_rules"][0]["rule"], "proof-bind")

    def test_ho_shape_metadata_records_lambda_defs_and_bind_consumers(self):
        proof = """(proof
(let ((?x1 (lambda ((x Int)) (rewrite (= x x)))))
  (nnf-pos (proof-bind ?x1)
    (! (forall ((x Int)) (= (select z3name!0 x) x))
       :qid :lambda-def))))
"""
        report = extract_rule_report(proof)
        shape = report["ho_shape"]

        self.assertEqual(shape["lambda_term_count"], 1)
        self.assertEqual(shape["named_lambda_symbols"], ["z3name!0"])
        self.assertEqual(shape["lambda_def_axiom_count"], 1)
        self.assertIn(":qid :lambda-def", shape["lambda_def_axioms"][0]["shape"])
        self.assertEqual(shape["proof_bind_count"], 1)
        self.assertIn("proof-bind ?x1", shape["proof_binds"][0]["shape"])
        self.assertEqual(shape["proof_bind_consumers"], {"nnf-pos": 1})
        self.assertNotIn("proof-bind", REPLAY_SUPPORTED_RULES)
        self.assertEqual(RULE_PREMISE_KIND["proof-bind"], "one")
        self.assertEqual(report["unknown_rules"], [])

    def test_complete_manifest_contains_the_ho_corpus(self):
        paths = inputs_from_complete_manifest(
            DEFAULT_COMPLETE_CORPUS_MANIFEST,
            list(HO_PROOF_CORPUS_CASE_IDS),
        )

        self.assertEqual(len(paths), len(HO_PROOF_CORPUS_CASE_IDS))
        self.assertTrue(all(path.exists() for path in paths))

        manifest = json.loads(DEFAULT_COMPLETE_CORPUS_MANIFEST.read_text())
        ho_cases = {
            case["id"]: case
            for case in manifest["cases"]
            if case["id"] in HO_PROOF_CORPUS_CASE_IDS
        }
        self.assertEqual(set(ho_cases), set(HO_PROOF_CORPUS_CASE_IDS))
        for case in ho_cases.values():
            self.assertEqual(
                set(case["expected_shape_families"]),
                {"4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"},
            )

    def test_checked_in_ho_recordings_match_pinned_matrix(self):
        corpus_root = DEFAULT_COMPLETE_CORPUS_MANIFEST.parent
        for version in ("4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"):
            entries_path = corpus_root / f"z3-{version}" / "entries.jsonl"
            entries = [
                json.loads(line)
                for line in entries_path.read_text().splitlines()
                if "proof_rule_ho_" in line
            ]
            self.assertEqual(
                validate_ho_shape_matrix(
                    entries,
                    DEFAULT_COMPLETE_CORPUS_MANIFEST,
                ),
                [],
            )

    def test_classifies_verbatim_and_named_lambda_shapes(self):
        verbatim = entry(
            "verbatim.smt2",
            "4.11.2",
            {"ho_shape": {
                "lambda_term_count": 1,
                "named_lambda_symbols": [],
                "lambda_def_axiom_count": 0,
                "proof_bind_count": 0,
            }},
        )
        named = entry(
            "named.smt2",
            "4.15.3",
            {"ho_shape": {
                "lambda_term_count": 2,
                "named_lambda_symbols": ["z3name!0"],
                "lambda_def_axiom_count": 1,
                "proof_bind_count": 1,
            }},
        )

        self.assertEqual(classify_ho_shape(verbatim), "verbatim-lambda")
        self.assertEqual(classify_ho_shape(named), "named-lambda-def")

    def test_parse_only_rule_is_reported_without_expected_manifest(self):
        proof = extract_rule_report("(proof (proof-bind (asserted false)))")
        gate = build_rule_gate_report(
            [entry("proof-bind.smt2", "4.12.4", proof)],
            None,
        )

        self.assertTrue(gate["passed"])
        self.assertEqual(gate["unseen_rules"], [])
        self.assertEqual(gate["replay_unknown_rules"], [])
        self.assertEqual(gate["parse_only_rules"][0]["rule"], "proof-bind")

    def test_unknown_rule_is_reported_with_context(self):
        proof = """(proof
(let ((@x1 (mystery-rule false)))
  (unit-resolution @x1 false)))
"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"]["mystery-rule"], 1)
        self.assertEqual(report["rule_histogram"]["unit-resolution"], 1)
        self.assertEqual(report["unknown_rules"][0]["rule"], "mystery-rule")
        self.assertIn("mystery-rule", report["unknown_rules"][0]["contexts"][0]["context"])

    def test_indexed_th_lemma_is_normalized_by_theory(self):
        proof = """(proof ((_ th-lemma arith farkas 1 1) @x1 @x2 false))"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"], {"th-lemma-arith": 1})

    def test_char_theory_rule_and_string_internal_shapes_are_recorded(self):
        proof = """(proof
((_ th-lemma char) (asserted a)
  (= (seq.unit (_ Char 97))
     ((_ seq.tail seq.tail) "a" 0)))
((_ th-lemma seq) (asserted b)
  ((_ seq.prefix.c seq.prefix.c) "a"))
((_ rewrite) (= "A\\u{1f642}" "A\\u{1f642}"))
((_ char.bit char.bit 17) (_ Char 97)))
"""
        report = extract_rule_report(proof)
        shape = report["string_shape"]

        self.assertIn("th-lemma-char", REPLAY_SUPPORTED_RULES)
        self.assertEqual(report["theory_lemma_histogram"]["char:<none>"], 1)
        self.assertIn("seq.unit", shape["symbols"])
        self.assertIn("seq.tail", shape["symbols"])
        self.assertIn("seq.prefix.c", shape["seq_prefix_symbols"])
        self.assertIn("(_ Char 97)", shape["char_literals"])
        self.assertEqual(shape["char_bit_indices"], ["17"])
        self.assertIn('"A\\u{1f642}"', shape["string_literals"])

    def test_malformed_fragment_is_recorded(self):
        report = extract_rule_report("(proof (asserted false)")
        self.assertEqual(report["rule_histogram"], {})
        self.assertEqual(len(report["malformed_fragments"]), 1)
        self.assertIn("missing", report["malformed_fragments"][0]["message"])

    def test_summary_records_stable_rule_lists_by_z3_version(self):
        proof_a = extract_rule_report("(proof (unit-resolution (asserted a) false))")
        proof_b = extract_rule_report("(proof (asserted false))")
        summary = build_summary(
            [
                entry("a.smt2", "4.13.0", proof_a),
                entry("b.smt2", "4.12.4", proof_b),
            ]
        )
        self.assertEqual(summary["discovered_rules"], ["asserted", "unit-resolution"])
        self.assertEqual(summary["inferred_rules"], [])
        self.assertEqual(summary["aggregate_inferred_rule_histogram"], {})
        self.assertEqual(summary["proof_rule_support"]["parse_only"], ["proof-bind"])
        self.assertEqual(
            summary["rules_by_version"],
            [
                {
                    "z3_version": "4.12.4",
                    "rules": ["asserted"],
                    "rule_histogram": {"asserted": 1},
                    "inferred_rules": [],
                    "inferred_rule_histogram": {},
                    "theory_lemma_subkinds": [],
                    "theory_lemma_histogram": {},
                },
                {
                    "z3_version": "4.13.0",
                    "rules": ["asserted", "unit-resolution"],
                    "rule_histogram": {"asserted": 1, "unit-resolution": 1},
                    "inferred_rules": [],
                    "inferred_rule_histogram": {},
                    "theory_lemma_subkinds": [],
                    "theory_lemma_histogram": {},
                },
            ],
        )

    def test_records_indexed_th_lemma_metadata(self):
        report = extract_rule_report("(proof ((_ th-lemma arith farkas 1 1) (asserted a) false))")

        self.assertEqual(report["rule_histogram"], {"asserted": 1, "th-lemma-arith": 1})
        self.assertEqual(report["theory_lemma_histogram"], {"arith:farkas": 1})
        self.assertEqual(report["theory_lemma_metadata"][0]["theory"], "arith")
        self.assertEqual(report["theory_lemma_metadata"][0]["subkind"], "farkas")
        self.assertEqual(report["parsed_dag_summary"]["proof_rule_application_count"], 2)

    def test_expected_rules_are_version_aware(self):
        manifest = {
            "default": ["asserted"],
            "versions": {
                "4.*": ["unit-resolution"],
                "4.13.0": ["rewrite"],
            },
        }
        self.assertEqual(
            expected_rules_for_version(manifest, "4.13.0"),
            {"asserted", "unit-resolution", "rewrite"},
        )
        self.assertEqual(expected_rules_for_version(manifest, "3.0.0"), {"asserted"})

    def test_gate_flags_unseen_rule_with_version_input_and_context(self):
        proof = extract_rule_report("(proof (unit-resolution (asserted a) false))")
        report = build_rule_gate_report(
            [entry("minimal.smt2", "4.13.0", proof)],
            {"default": ["asserted"]},
        )
        self.assertFalse(report["passed"])
        self.assertEqual(report["unseen_rules"][0]["z3_version"], "4.13.0")
        self.assertEqual(report["unseen_rules"][0]["input"], "minimal.smt2")
        self.assertEqual(report["unseen_rules"][0]["rule"], "unit-resolution")
        self.assertIn(
            "unit-resolution",
            report["unseen_rules"][0]["contexts"][0]["context"],
        )
        self.assertEqual(
            report["unseen_rules"][0]["artifacts"],
            {
                "effective_input_sha256": "effective-input-hash",
                "input_sha256": "input-hash",
                "proof_path": "proofs/input.proof",
                "proof_sha256": "proof-hash",
                "stderr_path": "raw/stderr.txt",
                "stdout_path": "raw/stdout.txt",
            },
        )

    def test_gate_flags_replay_unknown_rule_with_context(self):
        proof = extract_rule_report("(proof (mystery-rule false))")
        report = build_rule_gate_report(
            [entry("synthetic.smt2", "4.13.0", proof)],
            {"default": ["mystery-rule"]},
        )
        self.assertFalse(report["passed"])
        self.assertEqual(report["unseen_rules"], [])
        self.assertEqual(report["replay_unknown_rules"][0]["rule"], "mystery-rule")
        self.assertEqual(report["replay_unknown_rules"][0]["input"], "synthetic.smt2")
        self.assertIn(
            "mystery-rule",
            report["replay_unknown_rules"][0]["contexts"][0]["context"],
        )
        self.assertEqual(
            report["replay_unknown_rules"][0]["artifacts"]["proof_path"],
            "proofs/input.proof",
        )

    def test_gate_flags_malformed_fragment_with_artifacts(self):
        proof = extract_rule_report("(proof (asserted false)")
        report = build_rule_gate_report(
            [entry("malformed.smt2", "4.13.0", proof)],
            {"default": ["asserted"]},
        )

        self.assertFalse(report["passed"])
        self.assertEqual(report["malformed_fragments"][0]["input"], "malformed.smt2")
        self.assertEqual(
            report["malformed_fragments"][0]["artifacts"]["stdout_path"],
            "raw/stdout.txt",
        )

    def test_requirement_report_flags_missing_rules_subkinds_and_replay(self):
        proof = extract_rule_report("(proof ((_ th-lemma arith farkas 1) (asserted a) false))")
        report = build_requirement_report(
            [entry("arith.smt2", "4.13.0", proof)],
            required_rules=["th-lemma-arith", "unit-resolution"],
            required_theory_subkinds=["arith:farkas", "arith:gomory"],
            require_replay_success=True,
            require_no_oracles=True,
        )

        self.assertFalse(report["passed"])
        self.assertEqual(report["missing_rule_occurrences"], [{"rule": "unit-resolution"}])
        self.assertEqual(report["missing_theory_subkinds"], [{"theory_subkind": "arith:gomory"}])
        self.assertEqual(report["replay_failures"][0]["proof_replay_status"], "not-run")
        self.assertEqual(report["oracle_failures"], [])

    def test_requirement_report_accepts_inferred_rule_occurrence(self):
        proof = extract_rule_report("(proof ((_ th-lemma arith) (asserted a) false))")
        item = entry("nonlinear.smt2", "4.13.0", proof)
        item["proof"]["inferred_rule_histogram"] = {  # type: ignore[index]
            "th-lemma-nonlinear-arith": 1
        }

        report = build_requirement_report(
            [item],
            required_rules=["th-lemma-nonlinear-arith"],
            required_theory_subkinds=[],
            require_replay_success=False,
            require_no_oracles=False,
        )

        self.assertTrue(report["passed"])
        self.assertEqual(report["missing_rule_occurrences"], [])

    def test_requirement_report_accepts_theory_subkind_wildcards(self):
        proof = extract_rule_report(
            "(proof ((_ th-lemma char) (asserted a) false) "
            "((_ th-lemma seq extensionality) (asserted b) false))"
        )
        report = build_requirement_report(
            [entry("strings.smt2", "4.15.3", proof)],
            required_rules=["th-lemma-char", "th-lemma-seq"],
            required_theory_subkinds=["char:*", "seq:*"],
            require_replay_success=False,
            require_no_oracles=False,
        )

        self.assertTrue(report["passed"])
        self.assertEqual(report["missing_theory_subkinds"], [])

    def test_checked_in_string_manifest_covers_probes_and_operators(self):
        versions, paths = inputs_from_string_manifest(
            DEFAULT_STRING_CORPUS_MANIFEST
        )
        manifest = json.loads(DEFAULT_STRING_CORPUS_MANIFEST.read_text())
        probes = {
            case["drafting_probe"]
            for case in manifest["cases"]
            if "drafting_probe" in case
        }
        operators = {
            operator
            for case in manifest["cases"]
            for operator in case["operators"]
        }

        self.assertEqual(
            versions,
            {"4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"},
        )
        self.assertEqual(probes, set(STRING_DRAFTING_PROBES))
        self.assertEqual(operators, set(STRING_OFFICIAL_OPERATORS))
        self.assertEqual(len(paths), len(manifest["cases"]))
        self.assertTrue(all(path.exists() for path in paths))

    def test_checked_in_string_recordings_are_complete_and_gated(self):
        corpus_root = DEFAULT_STRING_CORPUS_MANIFEST.parent
        validation_root = corpus_root.parents[2]
        manifest = json.loads(DEFAULT_STRING_CORPUS_MANIFEST.read_text())
        expected_count = len(manifest["cases"])

        for version in sorted(manifest["supported_z3_versions"]):
            version_root = corpus_root / f"z3-{version}"
            entries = [
                json.loads(line)
                for line in (version_root / "entries.jsonl")
                .read_text()
                .splitlines()
            ]
            summary = json.loads((version_root / "summary.json").read_text())
            gate = json.loads((version_root / "rule-gate.json").read_text())

            self.assertEqual(len(entries), expected_count)
            self.assertTrue(
                all(
                    item["solver"]["result"] == "unsat"
                    and item["proof"]["available"]
                    and item["z3"]["exit_code"] == 0
                    and not item["z3"]["timed_out"]
                    for item in entries
                )
            )
            self.assertEqual(build_summary(entries), summary)
            self.assertTrue(gate["passed"])
            self.assertEqual(gate["unseen_rules"], [])
            self.assertEqual(gate["replay_unknown_rules"], [])
            self.assertEqual(gate["malformed_fragments"], [])
            self.assertEqual(
                gate["requirements"]["missing_rule_occurrences"],
                [],
            )
            self.assertEqual(
                gate["requirements"]["missing_theory_subkinds"],
                [],
            )

            for item in entries:
                for path_value in (
                    item["input"]["path"],
                    item["proof"]["raw_path"],
                    item["z3"]["stdout_path"],
                    item["z3"]["stderr_path"],
                ):
                    relative = validation_relative_path(
                        pathlib.Path(path_value)
                    )
                    self.assertTrue((validation_root / relative).is_file())
                input_path = validation_root / validation_relative_path(
                    pathlib.Path(item["input"]["path"])
                )
                proof_path = validation_root / validation_relative_path(
                    pathlib.Path(item["proof"]["raw_path"])
                )
                self.assertEqual(
                    sha256_file(input_path),
                    item["input"]["sha256"],
                )
                self.assertEqual(
                    sha256_file(proof_path),
                    item["proof"]["raw_sha256"],
                )

    def test_requirement_report_flags_oracle_tags(self):
        proof = extract_rule_report("(proof (asserted false))")
        item = entry("oracle.smt2", "4.13.0", proof)
        item["theorem"]["tag_summary"]["oracle_tags"] = ["HolSmtLib"]  # type: ignore[index]

        report = build_requirement_report(
            [item],
            required_rules=[],
            required_theory_subkinds=[],
            require_replay_success=False,
            require_no_oracles=True,
        )

        self.assertFalse(report["passed"])
        self.assertEqual(report["oracle_failures"][0]["input"], "oracle.smt2")

    def test_checked_in_supported_version_manifest_validates(self):
        self.assertEqual(validate_corpus_manifest(DEFAULT_SUPPORTED_VERSION_MANIFEST), [])

    def test_supported_version_manifest_requires_all_supported_versions(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = pathlib.Path(tmp) / "manifest.json"
            manifest.write_text(
                """{
  "schema": "holsmt-z3-proof-corpus-matrix-v1",
  "supported_z3_versions": ["4.13.0"],
  "expected_rules": "expected.json",
  "expected_summary": "summary.json",
  "expected_gate": "rule-gate.json",
  "inputs": [],
  "versions": [],
  "missing_replay_supported_justifications": {},
  "missing_parse_only_justifications": {}
}
""",
                encoding="utf-8",
            )

            errors = validate_corpus_manifest(manifest)

        self.assertTrue(
            any("supported_z3_versions mismatch" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("versions must contain exactly" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
