#!/usr/bin/env python3

import contextlib
import io
import json
import os
import pathlib
import sys
import tempfile
import unittest


TOOLS_DIR = pathlib.Path(__file__).resolve().parents[1]
CORPUS_DIR = TOOLS_DIR / "conformance-corpus" / "v2"
REPO_ROOT = pathlib.Path(
    os.environ.get("HOLSMT_ROOT", TOOLS_DIR.parents[2])
).resolve()
sys.path.insert(0, str(TOOLS_DIR))
sys.path.insert(0, str(CORPUS_DIR))

import audit_complete_conformance as audit
import generate_complete_corpus as generator


class CompleteCorpusGeneratorTests(unittest.TestCase):
    def test_sample_manifest_has_one_valid_red_entry_for_each_class(self):
        manifest = generator.manifest_for_cases(generator.sample_cases())
        cases = audit.validate_v2_manifest(manifest)

        self.assertEqual(
            {case["class"] for case in cases},
            set(generator.CASE_CLASSES),
        )
        for case in cases:
            self.assertEqual(case["versions"], list(generator.SUPPORTED_Z3_VERSIONS))
            if any(result["status"] == "red" for result in case["expected"].values()):
                self.assertTrue(case["implementation_obligation"], case)
            else:
                self.assertIsNone(case["implementation_obligation"], case)

    def test_resource_gated_feature_produces_reserved_unsupported_row(self):
        case_id = "theory:FloatingPoint:synthetic-resource-gate"
        generated = generator.manifest_entry(
            case_id=case_id,
            file="cases/theories/theory_floatingpoint_synthetic_resource_gate.smt2",
            logic="QF_FP",
            standard="SMT-LIB-2.7",
            row_class="theory",
            features=[
                "theory:FloatingPoint",
                generator.RESOURCE_GATE_FEATURE,
            ],
            modes=["parser-only", "z3-tac"],
            versions=generator.SUPPORTED_Z3_VERSIONS,
            expected={
                "parser-only": generator.expected_result("pass"),
                "z3-tac": generator.expected_result("red"),
            },
            implementation_obligation=generator.implementation_obligation(
                files=["src/HolSmt/SmtResource.sml"],
                feature="synthetic-resource-gate",
                test_ids=[case_id],
                failure_phase="proof-replay",
            ),
            source=generator.source(
                "HolSmt-internal",
                "synthetic D12 resource-gate contract",
            ),
        )

        audited = audit.validate_v2_manifest(
            generator.manifest_for_cases(
                [generator.GeneratedCase(entry=generated, script="(assert false)\n")]
            )
        )[0]
        self.assertEqual(
            audited["expected"]["z3-tac"],
            {
                "status": "unsupported",
                "diagnostic": generator.RESOURCE_GATE_DIAGNOSTIC,
            },
        )
        self.assertIsNone(audited["implementation_obligation"])

    def test_dry_run_output_is_deterministic_and_valid(self):
        stdout_a = io.StringIO()
        stdout_b = io.StringIO()

        with contextlib.redirect_stdout(stdout_a):
            self.assertEqual(generator.main([]), 0)
        with contextlib.redirect_stdout(stdout_b):
            self.assertEqual(generator.main([]), 0)

        self.assertEqual(stdout_a.getvalue(), stdout_b.getvalue())
        manifest = json.loads(stdout_a.getvalue())
        audit.validate_v2_manifest(manifest)

    def test_focused_domain_subcommand_emits_only_that_class(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["proof-rules"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)
        self.assertEqual(
            len(cases),
            3
            + len(generator.HO_PROOF_CASES)
            + len(generator.TH_LEMMA_PROOF_RULE_OBLIGATIONS),
        )
        self.assertEqual({case["class"] for case in cases}, {"proof-rule"})
        case_ids = {case["id"] for case in cases}
        self.assertIn("proof-rule:asserted", case_ids)
        self.assertIn("proof-rule:th-lemma-basic", case_ids)
        self.assertIn("proof-rule:th-lemma-fp", case_ids)
        self.assertIn("proof-rule:th-lemma-char", case_ids)
        self.assertEqual(
            {
                case.case_id
                for case in generator.HO_PROOF_CASES
            },
            {
                case_id
                for case_id in case_ids
                if case_id.startswith("proof-rule:ho:")
            },
        )
        for case in cases:
            self.assertIn("proof-parse", case["expected"])
            self.assertIn("proof-replay", case["expected"])
            if case["id"] in {"proof-rule:asserted", "proof-rule:th-lemma-basic"}:
                rule = case["id"].removeprefix("proof-rule:")
                self.assertIsNone(case["implementation_obligation"])
                self.assertEqual(case["expected"]["proof-parse"]["status"], "pass")
                self.assertEqual(case["expected"]["proof-replay"]["status"], "pass")
                self.assertEqual(case["expected"]["z3-tac"]["status"], "pass")
                self.assertEqual(
                    case["expected"]["z3-tac"]["theorem_shape"],
                    "closed theorem without oracle tags",
                )
                self.assertEqual(
                    case["expected"]["proof-replay"]["proof_rule_histogram"],
                    {rule: 1},
                )
            if case["id"] == "proof-rule:th-lemma-fp":
                self.assertIsNone(case["implementation_obligation"])
                self.assertIn(
                    "proof-rule-behavior:checked-replay",
                    case["features"],
                )
                for mode in ("proof-parse", "proof-replay", "z3-tac"):
                    self.assertEqual(case["expected"][mode]["status"], "pass")
            if (
                case["id"].startswith("proof-rule:th-lemma-")
                and case["id"] != "proof-rule:th-lemma-basic"
                and case["implementation_obligation"] is not None
            ):
                self.assertIn("z3-tac", case["expected"])
                self.assertEqual(case["expected"]["z3-tac"]["failure_phase"], "proof-replay")
                self.assertEqual(
                    case["expected"]["z3-tac"]["theorem_shape"],
                    "closed theorem without oracle tags",
                )
                self.assertEqual(
                    case["implementation_obligation"]["test_ids"],
                    [case["id"]],
                )

        ho_cases = [
            case
            for case in cases
            if case["id"].startswith("proof-rule:ho:")
        ]
        self.assertEqual(len(ho_cases), len(generator.HO_PROOF_CASES))
        for case in ho_cases:
            self.assertEqual(case["logic"], "ALL")
            self.assertEqual(case["standard"], "Z3-extension")
            self.assertEqual(
                case["versions"],
                list(generator.SUPPORTED_Z3_VERSIONS),
            )
            self.assertEqual(case["expected"]["proof-parse"]["status"], "pass")
            self.assertEqual(case["expected"]["proof-replay"]["status"], "pass")
            residual = generator.HO_PROOF_Z3_TAC_RESIDUALS.get(case["id"])
            if residual is None:
                self.assertEqual(case["expected"]["z3-tac"]["status"], "pass")
                self.assertIsNone(case["implementation_obligation"])
                self.assertNotIn("proof-rule:rewrite", case["features"])
            else:
                self.assertEqual(case["expected"]["z3-tac"]["status"], "red")
                self.assertEqual(
                    case["expected"]["z3-tac"]["diagnostic"],
                    residual,
                )
                self.assertIn("proof-rule:rewrite", case["features"])
                obligation = case["implementation_obligation"]
                self.assertIsNotNone(obligation)
                self.assertEqual(obligation["feature"], "proof-rule:rewrite")
                self.assertEqual(obligation["test_ids"], [case["id"]])
            for feature in {
                "function-sort",
                "function-valued",
                "higher-order",
                "ho-core",
                "lambda",
            }:
                self.assertIn(feature, case["features"])
            if case["id"] == "proof-rule:ho:beta-instance":
                self.assertNotIn("proof-rule:proof-bind", case["features"])
            else:
                self.assertIn("proof-rule:proof-bind", case["features"])

    def test_commands_subcommand_emits_command_groups_and_datatype_corpus_cases(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["commands"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)
        recursive_replay_cases = 2
        self.assertEqual(
            len(cases),
            4 * len(generator.COMMAND_GROUPS)
            + recursive_replay_cases
            + len(generator.DATATYPE_COMMAND_CORPUS_CASES),
        )
        self.assertEqual({case["class"] for case in cases}, {"command"})

        by_group = {}
        for case in cases:
            if "command-case:datatype-corpus" in case["features"]:
                continue
            group_features = [
                feature
                for feature in case["features"]
                if feature.startswith("command-group:")
            ]
            self.assertEqual(len(group_features), 1, case)
            by_group.setdefault(group_features[0], []).append(case)

        self.assertEqual(len(by_group), len(generator.COMMAND_GROUPS))
        for group, group_cases in by_group.items():
            kinds = {
                feature
                for case in group_cases
                for feature in case["features"]
                if feature.startswith("command-case:")
            }
            expected_kinds = {
                "command-case:positive",
                "command-case:negative",
                "command-case:state",
                "command-case:reconstruction",
            }
            if group == "command-group:define-fun-rec-define-funs-rec":
                expected_kinds.update({
                    "command-case:define-fun-rec-replay",
                    "command-case:define-funs-rec-replay",
                })
            self.assertEqual(
                kinds,
                expected_kinds,
            )
            negative_cases = [
                case
                for case in group_cases
                if "command-case:negative" in case["features"]
            ]
            self.assertEqual(len(negative_cases), 1)
            for result in negative_cases[0]["expected"].values():
                self.assertEqual(result["status"], "fail")
                self.assertIn("diagnostic", result)
                self.assertIn("failure_phase", result)

        declare_fun = next(
            group for group in generator.COMMAND_GROUPS
            if group.slug == "declare-fun"
        )
        self.assertNotIn("(->", declare_fun.reconstruction_script)
        self.assertIn(
            "(declare-fun h (Bool) Bool)",
            declare_fun.reconstruction_script,
        )

        datatype_cases = [
            case for case in cases
            if "command-case:datatype-corpus" in case["features"]
        ]
        self.assertEqual(len(datatype_cases), len(generator.DATATYPE_COMMAND_CORPUS_CASES))
        self.assertTrue(
            all(
                case["file"].startswith("cases/commands/datatypes/")
                for case in datatype_cases
            )
        )
        self.assertTrue(
            all(
                "theory:Datatypes" in case["features"]
                for case in datatype_cases
            )
        )
        datatype_by_id = {case["id"]: case for case in datatype_cases}
        new_datatype_ids = {
            "command:datatypes:declare-datatypes-arity-mismatch",
            "command:datatypes:declare-datatypes-par-mismatch",
            "command:datatypes:equality-chain",
            "command:datatypes:match-default-variable",
            "command:datatypes:match-nested-branch",
            "command:datatypes:match-simple",
            "command:datatypes:mutual-selector",
            "command:datatypes:non-well-founded-self",
            "command:datatypes:parametric-tester",
            "command:datatypes:parametric-two-instances",
            "command:datatypes:selector-misapplication-sat",
        }
        self.assertLessEqual(new_datatype_ids, set(datatype_by_id))
        self.assertTrue(
            any(
                "datatype-command:parametric" in case["features"]
                and case["expected"]["typecheck-only"]["status"] == "pass"
                for case in datatype_cases
            )
        )
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:non-well-founded-self"
            ]["expected"]["typecheck-only"]["status"],
            "fail",
        )
        for case_id in {
            "command:datatypes:match-simple",
            "command:datatypes:match-nested-branch",
            "command:datatypes:match-default-variable",
        }:
            case = datatype_by_id[case_id]
            self.assertIn("datatype-command:match", case["features"])
            self.assertEqual(case["expected"]["parser-only"]["status"], "pass")
            self.assertEqual(case["expected"]["typecheck-only"]["status"], "pass")
            self.assertEqual(case["expected"]["z3-oracle"]["status"], "pass")
            self.assertEqual(case["expected"]["z3-tac"]["status"], "pass")
            self.assertIsNone(case["implementation_obligation"])
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:parametric-two-instances"
            ]["expected"]["z3-tac"]["status"],
            "pass",
        )
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:parametric-two-instances"
            ]["expected"]["z3-oracle"]["status"],
            "pass",
        )
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:selector-misapplication-sat"
            ]["expected"]["z3-oracle"]["status"],
            "pass",
        )
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:selector-misapplication-sat"
            ]["modes"],
            ["z3-oracle"],
        )
        for case_id in {
            "command:datatypes:parametric-tester",
            "command:datatypes:mutual-selector",
        }:
            case = datatype_by_id[case_id]
            self.assertEqual(case["expected"]["z3-tac"]["status"], "pass")
            self.assertEqual(case["expected"]["z3-oracle"]["status"], "pass")
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:equality-chain"
            ]["expected"]["z3-tac"]["status"],
            "pass",
        )
        self.assertEqual(
            datatype_by_id[
                "command:datatypes:equality-chain"
            ]["expected"]["z3-oracle"]["status"],
            "pass",
        )
        for case_id in {
            "command:datatypes:declare-datatypes-arity-mismatch",
            "command:datatypes:declare-datatypes-par-mismatch",
        }:
            case = datatype_by_id[case_id]
            self.assertIn(
                "command-group:declare-datatype-declare-datatypes",
                case["features"],
            )
            self.assertEqual(case["expected"]["typecheck-only"]["status"], "fail")
            self.assertIsNone(case["implementation_obligation"])

        reconstruction_cases = [
            case for case in cases
            if "command-case:reconstruction" in case["features"]
        ]
        for case in reconstruction_cases:
            obligation = case["implementation_obligation"]
            expected = case["expected"]["z3-tac"]
            group = next(
                feature.split(":", 1)[1]
                for feature in case["features"]
                if feature.startswith("command-group:")
            )
            if group in generator.RECONSTRUCTED_COMMAND_GROUPS:
                self.assertEqual(expected["status"], "pass", case)
                self.assertIsNone(obligation, case)
            elif expected["notes"] == "theorem reconstruction applies: false":
                if expected["status"] == "red":
                    self.assertIsNotNone(obligation, case)
                    for filename in obligation["files"]:
                        self.assertTrue((REPO_ROOT / filename).exists(), filename)
                else:
                    self.assertEqual(expected["status"], "unsupported", case)
                    self.assertIsNone(obligation, case)
                    self.assertIn("Z3_TAC", expected["diagnostic"], case)
            else:
                self.assertEqual(expected["status"], "red", case)
                self.assertIsNotNone(obligation, case)
                for filename in obligation["files"]:
                    self.assertTrue((REPO_ROOT / filename).exists(), filename)

    def test_logics_subcommand_emits_case_packet_per_packet_logic(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["logics"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)
        packet_logics = generator.logic_packet_logics()
        nonlinear_logics = {"QF_NIA", "QF_NRA", "NIA", "NRA"}
        int_real_logics = generator.INT_REAL_COERCION_LOGICS & set(packet_logics)
        datatype_logics = {logic for logic in packet_logics if "DT" in logic.removeprefix("QF_")}
        self.assertEqual(
            len(cases),
            6 * len(packet_logics)
            + len(nonlinear_logics & set(packet_logics))
            + len(int_real_logics)
            + len(datatype_logics),
        )
        self.assertEqual({case["class"] for case in cases}, {"logic"})
        self.assertNotIn("ALL", {case["logic"] for case in cases})

        by_logic = {}
        for case in cases:
            packet_logic = next(
                feature.split(":", 1)[1]
                for feature in case["features"]
                if feature.startswith("logic:") and not feature.startswith("logic-case:")
            )
            by_logic.setdefault(packet_logic, []).append(case)
        self.assertEqual(set(by_logic), set(packet_logics))
        for logic, logic_cases in by_logic.items():
            kinds = {
                feature
                for case in logic_cases
                for feature in case["features"]
                if feature.startswith("logic-case:")
            }
            expected_kinds = {
                "logic-case:sat",
                "logic-case:unsat-proof",
                "logic-case:type-error",
                "logic-case:malformed",
                "logic-case:fragment-violation",
                "logic-case:boundary",
            }
            if logic in nonlinear_logics:
                expected_kinds.add("logic-case:nonlinear-proof")
            if logic in int_real_logics:
                expected_kinds.add("logic-case:int-real-user-function-coercion")
            if logic in datatype_logics:
                expected_kinds.add("logic-case:datatype-fragment-violation")
            self.assertEqual(kinds, expected_kinds, logic)
            unsat = [
                case for case in logic_cases
                if "logic-case:unsat-proof" in case["features"]
            ][0]
            self.assertEqual(unsat["versions"], list(generator.SUPPORTED_Z3_VERSIONS))
            for mode in ("proof-parse", "proof-replay", "z3-tac"):
                self.assertIn(mode, unsat["modes"])
                self.assertIn(mode, unsat["expected"])

            sat = [
                case for case in logic_cases
                if "logic-case:sat" in case["features"]
            ][0]
            self.assertEqual(sat["expected"]["z3-tac"]["status"], "pass")
            has_fp = generator.logic_has_floatingpoint(logic)
            for oracle_case in (sat, unsat):
                self.assertEqual(
                    "cvc5-oracle" in oracle_case["modes"],
                    has_fp,
                    oracle_case["id"],
                )
                self.assertEqual(
                    "cvc5-oracle" in oracle_case["expected"],
                    has_fp,
                    oracle_case["id"],
                )

    def test_logics_manifest_documents_extension_exclusions(self):
        inventory = generator.logics_manifest()
        required = set(inventory["accepted_logics"])
        excluded = {item["logic"] for item in inventory["excluded_logics"]}
        expected_excluded = {"ALL", *generator.HO_EXTENSION_LOGICS}

        self.assertEqual(excluded, expected_excluded)
        self.assertTrue(expected_excluded.isdisjoint(required))
        self.assertEqual(
            required | excluded,
            set(generator.parse_accepted_logics(generator.DEFAULT_LOGIC_SOURCE)),
        )

    def test_fragment_violation_rows_are_expected_failures(self):
        manifest = generator.manifest_for_cases(generator.logic_packet_cases())
        cases = audit.validate_v2_manifest(manifest)
        fragment_cases = [
            case for case in cases
            if "logic-case:fragment-violation" in case["features"]
        ]

        self.assertEqual(
            len(fragment_cases),
            len(generator.logic_packet_logics()),
        )
        for case in fragment_cases:
            logic = case["logic"]
            diagnostic = generator.logic_fragment_violation_diagnostic(logic)
            self.assertIsNone(case["implementation_obligation"], case)
            self.assertEqual(case["expected"]["parser-only"]["status"], "pass")
            for mode in ("typecheck-only", "z3-tac"):
                with self.subTest(logic=logic, mode=mode):
                    self.assertEqual(case["expected"][mode]["status"], "fail")
                    self.assertEqual(
                        case["expected"][mode]["failure_phase"],
                        "typecheck",
                    )
                    self.assertEqual(
                        case["expected"][mode]["diagnostic"],
                        diagnostic,
                    )

    def test_floatingpoint_unsat_rows_are_semantic_and_reconstructed(self):
        symbols = {
            symbol.slug: symbol
            for symbol in generator.FLOATINGPOINT_THEORY_SYMBOLS
        }
        self.assertEqual(set(generator.FP_SEMANTIC_UNSAT_SHAPES), set(symbols))
        self.assertEqual(len(symbols), 51)

        symbolic_slugs = {
            "fp.abs",
            "fp.neg",
            "fp.leq",
            "fp.lt",
            "fp.gt",
            "fp.eq",
            "fp.isnormal",
            "fp.issubnormal",
            "fp.iszero",
            "fp.isinfinite",
            "fp.isnan",
            "fp.isnegative",
            "fp.ispositive",
        }
        actual_symbolic = {
            slug
            for slug, shape in generator.FP_SEMANTIC_UNSAT_SHAPES.items()
            if shape.declarations
        }
        self.assertEqual(actual_symbolic, symbolic_slugs)
        for slug in symbolic_slugs:
            self.assertIn("(_ FloatingPoint 3 5)",
                          generator.FP_SEMANTIC_UNSAT_SHAPES[slug].declarations)

        generated = {
            case.entry["id"]: case
            for case in generator.theory_cases()
            if case.entry["id"].startswith("theory:FloatingPoint:")
            and case.entry["id"].endswith(":unsat-proof")
        }
        self.assertEqual(len(generated), 51)
        for slug, shape in generator.FP_SEMANTIC_UNSAT_SHAPES.items():
            case_id = f"theory:FloatingPoint:{slug}:unsat-proof"
            case = generated[case_id]
            self.assertEqual(case.script,
                             generator.fp_unsat_proof_script(slug))
            self.assertIn(f"(set-logic {shape.logic})", case.script)
            self.assertIn(f"(assert {shape.assertion})", case.script)
            self.assertTrue(shape.fact)
            self.assertIn("theory-behavior:semantic-fp-proof",
                          case.entry["features"])
            self.assertIn(f"fp-proof-shape:{shape.shape}",
                          case.entry["features"])
            proof_id = "task05_" + generator.slug(
                slug + ":unsat-proof"
            )
            self.assertIn(
                f"proof-corpus-evidence:{proof_id}",
                case.entry["features"],
            )
            self.assertEqual(
                case.entry["source"]["notes"],
                "Proof occurrence: tools/proof-corpus/floatingpoint/"
                f"manifest.json#{proof_id}",
            )
            self.assertEqual(case.entry["expected"]["parser-only"]["status"],
                             "pass")
            for mode in (
                "typecheck-only",
                "z3-oracle",
                "proof-parse",
                "proof-replay",
                "z3-tac",
            ):
                self.assertEqual(case.entry["expected"][mode]["status"],
                                 "pass", (case_id, mode))
            obligation = case.entry["implementation_obligation"]
            self.assertIsNone(obligation)

    def test_floatingpoint_semantic_families_are_reconstructed(self):
        generated = {
            case.entry["id"]: case
            for case in generator.theory_cases()
            if case.entry["id"].startswith("theory:FloatingPoint:")
        }
        new_ids = {
            f"theory:FloatingPoint:{case.slug}"
            for case in generator.FLOATINGPOINT_THEORY_CASES
        }
        self.assertEqual(len(new_ids), 22)
        self.assertTrue(new_ids <= set(generated))

        family_features = {
            "theory-behavior:nan-payload-equality": 2,
            "theory-behavior:admissible-pin": 4,
            "theory-behavior:rna": 4,
            "theory-behavior:mixed-format": 2,
            "theory-behavior:qf-fplra": 3,
            "theory-behavior:comparison": 5,
            "theory-behavior:divergence-guard": 2,
            generator.RESOURCE_GATE_FEATURE: 2,
        }
        new_cases = [generated[case_id] for case_id in new_ids]
        proof_cases = [
            case for case in new_cases
            if "theory-case:unsat-proof" in case.entry["features"]
        ]
        self.assertEqual(len(proof_cases), 15)
        evidence_links = []
        metadata_links = []
        for case in proof_cases:
            links = [
                feature
                for feature in case.entry["features"]
                if feature.startswith("proof-corpus-")
            ]
            self.assertEqual(len(links), 1, case.entry["id"])
            link = links[0]
            proof_id = link.split(":", 1)[1]
            self.assertEqual(
                case.entry["source"]["notes"],
                "Proof occurrence: tools/proof-corpus/floatingpoint/"
                f"manifest.json#{proof_id}",
            )
            if link.startswith("proof-corpus-evidence:"):
                evidence_links.append(link)
            else:
                metadata_links.append(link)
        self.assertEqual(len(evidence_links), 14)
        self.assertEqual(
            metadata_links,
            [
                "proof-corpus-metadata:"
                "task06_d12_fp_add_commutativity_float32"
            ],
        )
        for feature, count in family_features.items():
            self.assertEqual(
                sum(feature in case.entry["features"] for case in new_cases),
                count,
                feature,
            )

        red_cases = [
            case for case in new_cases
            if any(
                result["status"] == "red"
                for result in case.entry["expected"].values()
            )
        ]
        self.assertEqual(red_cases, [])

        qf_fplra = [case for case in new_cases
                    if case.entry["logic"] == "QF_FPLRA"]
        self.assertEqual(len(qf_fplra), 3)
        for case in qf_fplra:
            expected = case.entry["expected"]
            self.assertEqual(expected["parser-only"]["status"], "pass")
            self.assertEqual(expected["z3-oracle"]["status"], "pass")
            self.assertEqual(expected["typecheck-only"]["status"], "pass")
            self.assertEqual(expected["z3-tac"]["status"], "pass")

    def test_floatingpoint_sat_pins_and_divergence_guards(self):
        cases = {
            case.slug: case
            for case in generator.FLOATINGPOINT_THEORY_CASES
        }
        pin_ids = {
            f"fp-{operation}-signed-zero-{pin}-pin-sat"
            for operation in ("min", "max")
            for pin in ("positive", "negative")
        }
        for case_id in pin_ids:
            case = cases[case_id]
            self.assertIn("theory-behavior:underspecified", case.features)
            self.assertIn("theory-behavior:admissible-pin", case.features)
            self.assertIn("(check-sat)", case.script)
            self.assertNotIn("(get-proof)", case.script)

        guards = [
            case for case in cases.values()
            if "theory-behavior:divergence-guard" in case.features
        ]
        self.assertEqual(len(guards), 2)
        for case in guards:
            self.assertIn("Float32", case.script)
            self.assertEqual(
                {result["status"] for result in case.expected.values()},
                {"pass"},
            )

    def test_floatingpoint_d12_exemplars_are_enumerated_gates(self):
        cases = {
            case.entry["id"]: case
            for case in generator.theory_cases()
            if generator.RESOURCE_GATE_FEATURE in case.entry["features"]
        }
        expected_ids = {
            "theory:FloatingPoint:d12-fp-add-commutativity-float32",
            "theory:FloatingPoint:d12-fp-add-commutativity-tiny-3-5",
        }
        self.assertEqual(set(cases), expected_ids)
        for case_id, case in cases.items():
            self.assertIn("fp.add", case.script)
            self.assertIn("theory-behavior:symbolic",
                          case.entry["features"])
            z3_expected = case.entry["expected"]["z3-tac"]
            self.assertEqual(z3_expected["status"], "unsupported")
            self.assertEqual(
                z3_expected["diagnostic"],
                generator.RESOURCE_GATE_DIAGNOSTIC,
            )
            self.assertEqual(len(z3_expected["diagnostic_alternatives"]), 1)
            self.assertIsNone(case.entry["implementation_obligation"])
            if case_id.endswith("float32"):
                self.assertIn("Float32", case.script)
            else:
                self.assertIn("(_ FloatingPoint 3 5)", case.script)

    def test_theories_subcommand_separates_strings_and_z3_extensions(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["theories"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)

        string_cases = [
            case for case in cases
            if "theory:UnicodeStrings" in case["features"]
        ]
        extension_cases = [
            case for case in cases
            if "theory:Z3_Extensions" in case["features"]
        ]
        self.assertTrue(string_cases)
        self.assertTrue(extension_cases)
        self.assertTrue(
            all(case["standard"] == "SMT-LIB-2.7" for case in string_cases)
        )
        self.assertTrue(
            all(case["file"].startswith("cases/theories/strings/") for case in string_cases)
        )
        self.assertTrue(
            all(
                case["standard"] in {"Z3-extension", "Solver-extension"}
                for case in extension_cases
            )
        )
        self.assertTrue(
            all(case["file"].startswith("cases/theories/z3_extensions/") for case in extension_cases)
        )
        for case in string_cases + extension_cases:
            self.assertIn("typecheck-only", case["modes"])
            self.assertFalse(set(case["modes"]) <= {"parser-only"})
            availability = case.get(
                "solver_availability",
                {"z3": generator.SUPPORTED_Z3_VERSIONS},
            )
            if "z3" in availability and "theory-case:type-error" not in case["features"]:
                self.assertIn("z3-oracle", case["modes"])
            if "cvc5" in availability and "theory-case:type-error" not in case["features"]:
                self.assertIn("cvc5-oracle", case["modes"])
            if "z3" not in availability:
                self.assertNotIn("z3-oracle", case["modes"])
                self.assertNotIn("z3-tac", case["modes"])
            if "theory-case:unsat-proof" in case["features"] and "z3" in availability:
                self.assertIn("proof-parse", case["modes"])
                self.assertIn("proof-replay", case["modes"])

        literal_cases = [
            case for case in string_cases
            if "theory-entry:UnicodeStrings:string-literal" in case["features"]
        ]
        self.assertEqual(
            {
                feature
                for case in literal_cases
                for feature in case["features"]
                if feature.startswith("theory-case:")
            },
            {
                "theory-case:boundary",
                "theory-case:sat",
                "theory-case:type-error",
                "theory-case:unsat-proof",
            },
        )

        self.assertEqual(
            len(string_cases),
            4 * len(generator.UNICODE_STRING_THEORY_SYMBOLS)
            + len(generator.UNICODE_STRING_THEORY_CASES),
        )
        self.assertEqual(len(string_cases), 163)
        string_by_id = {case["id"]: case for case in string_cases}
        self.assertFalse(
            any(
                "theory-behavior:translation-gap" in case["features"]
                for case in string_cases
            )
        )
        self.assertEqual(
            sum(
                "theory-behavior:proof-gap" in case["features"]
                for case in string_cases
            ),
            0,
        )
        for symbol in ("re.comp", "char"):
            for kind in ("sat", "unsat-proof", "type-error", "boundary"):
                case_id = f"theory:UnicodeStrings:{symbol}:{kind}"
                case = string_by_id[case_id]
                self.assertNotIn(
                    "theory-behavior:proof-gap",
                    case["features"],
                )
                if kind == "unsat-proof":
                    self.assertIsNone(case["implementation_obligation"])
                    self.assertEqual(
                        case["expected"]["z3-tac"]["status"],
                        "unsupported" if symbol == "char" else "pass",
                    )
                    self.assertEqual(
                        case["expected"]["typecheck-only"]["status"],
                        "pass",
                    )
                else:
                    self.assertIsNone(case["implementation_obligation"])
                    self.assertNotIn(
                        "red",
                        {
                            result["status"]
                            for result in case["expected"].values()
                        },
                    )
        re_comp_boundary = next(
            case
            for case in generator.theory_cases()
            if case.case_id == "theory:UnicodeStrings:re.comp:boundary"
        )
        self.assertIn(
            '(str.in_re "" (re.comp re.all))',
            re_comp_boundary.script,
        )

        fixed_literal = string_by_id[
            "theory:UnicodeStrings:literal-u-four-hex-decode"
        ]
        braced_literal = string_by_id[
            "theory:UnicodeStrings:"
            "literal-u-braced-one-to-five-hex-decode"
        ]
        for case in (fixed_literal, braced_literal):
            self.assertIsNone(case["implementation_obligation"])
            self.assertEqual(
                case["expected"]["typecheck-only"]["status"],
                "pass",
            )
            for mode in ("proof-parse", "proof-replay"):
                self.assertEqual(
                    case["expected"][mode]["status"],
                    "pass",
                )
        self.assertEqual(
            fixed_literal["expected"]["z3-tac"]["status"],
            "pass",
        )
        self.assertEqual(
            braced_literal["expected"]["z3-tac"]["status"],
            "unsupported",
        )

        out_of_range = string_by_id[
            "theory:UnicodeStrings:literal-u-braced-out-of-range"
        ]
        self.assertIsNone(out_of_range["implementation_obligation"])
        self.assertEqual(
            out_of_range["expected"]["parser-only"]["status"],
            "pass",
        )
        for mode in ("typecheck-only", "z3-tac"):
            self.assertEqual(
                out_of_range["expected"][mode]["status"],
                "fail",
            )

        for case_id in {
            "theory:UnicodeStrings:wf-free-variables-sat",
            "theory:UnicodeStrings:wf-quantified-binders-sat",
        }:
            case = string_by_id[case_id]
            self.assertIsNone(case["implementation_obligation"])
            self.assertTrue(
                all(
                    result["status"] == "pass"
                    for result in case["expected"].values()
                )
            )

        red_string_cases = [
            case for case in string_cases
            if any(
                result["status"] == "red"
                for result in case["expected"].values()
            )
        ]
        self.assertEqual(len(red_string_cases), 0)
        self.assertEqual(
            sum(
                result["status"] == "red"
                for case in string_cases
                for result in case["expected"].values()
            ),
            0,
        )
        for slug in ("str.replace-re", "str.replace-re-all"):
            case = string_by_id[
                f"theory:UnicodeStrings:{slug}:unsat-proof"
            ]
            self.assertIn(
                "theory-behavior:z3-unsupported",
                case["features"],
            )
            self.assertIsNone(case["implementation_obligation"])
            for mode in (
                "z3-oracle",
                "proof-parse",
                "proof-replay",
                "z3-tac",
            ):
                self.assertEqual(
                    case["expected"][mode]["status"],
                    "unsupported",
                )
        z3_tac_gate_ids = {
            "theory:UnicodeStrings:char:unsat-proof",
            "theory:UnicodeStrings:re-concat:unsat-proof",
            "theory:UnicodeStrings:re-plus:unsat-proof",
            "theory:UnicodeStrings:re-power:unsat-proof",
            "theory:UnicodeStrings:re.diff:unsat-proof",
            "theory:UnicodeStrings:re.opt:unsat-proof",
            (
                "theory:UnicodeStrings:"
                "literal-u-braced-one-to-five-hex-decode"
            ),
        }
        for case_id in z3_tac_gate_ids:
            case = string_by_id[case_id]
            self.assertIsNone(case["implementation_obligation"])
            self.assertEqual(
                case["expected"]["z3-tac"]["status"],
                "unsupported",
            )
            self.assertTrue(
                all(
                    case["expected"][mode]["status"] == "pass"
                    for mode in case["modes"]
                    if mode != "z3-tac"
                )
            )
        self.assertEqual(
            sum(
                any(
                    result["status"] == "unsupported"
                    for result in case["expected"].values()
                )
                for case in string_cases
            ),
            9,
        )

        for case_id in {
            "theory:UnicodeStrings:literal-doubled-quote",
            "theory:UnicodeStrings:literal-backslash-verbatim",
        }:
            case = string_by_id[case_id]
            self.assertIsNone(case["implementation_obligation"])
            self.assertTrue(
                all(
                    result["status"] == "pass"
                    for result in case["expected"].values()
                )
            )

        checked_unsat_ids = {
            "theory:ArraysEx:array:unsat-proof",
            "theory:ArraysEx:store:unsat-proof",
            "theory:Core:xor:unsat-proof",
        }
        by_id = {case["id"]: case for case in cases}
        for case_id in checked_unsat_ids:
            self.assertEqual(by_id[case_id]["expected"]["z3-tac"]["status"], "pass")
            self.assertNotIn("theorem_shape", by_id[case_id]["expected"]["z3-tac"])

        set_bag_cases = [
            case for case in extension_cases
            if {"theory-behavior:set", "theory-behavior:bag"}
            & set(case["features"])
        ]
        self.assertEqual(len(set_bag_cases), 204)
        self.assertEqual(
            {feature for case in set_bag_cases for feature in case["features"]
             if feature.startswith("theory-entry:Z3_Extensions:")},
            {
                f"theory-entry:Z3_Extensions:{symbol.slug}"
                for symbol in generator.Z3_EXTENSION_THEORY_SYMBOLS
                if "theory-behavior:set" in symbol.behavior_features
                or "theory-behavior:bag" in symbol.behavior_features
            },
        )
        for case in set_bag_cases:
            self.assertNotRegex(
                next(item.script for item in generator.theory_cases()
                     if item.case_id == case["id"]),
                r"\\(assert \\(= ([^()]*) \\1\\)\\)",
            )
        bag_count = by_id["theory:Z3_Extensions:cvc5-bag-count:boundary"]
        self.assertIn("theory-boundary:bag-count-nonnegative", bag_count["features"])
        cvc5_boundary = by_id["theory:Z3_Extensions:cvc5-set-card:boundary"]
        self.assertIn("theory-boundary:p6.4-parse-finiteness", cvc5_boundary["features"])
        self.assertIn("theory-boundary:p6.4-emission-finiteness-entailment", cvc5_boundary["features"])

    def test_theories_subcommand_emits_datatypes_and_hocore_cases(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["theories"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)

        datatype_cases = [
            case for case in cases
            if "theory:Datatypes" in case["features"]
        ]
        hocore_cases = [
            case for case in cases
            if "theory:HO_Core" in case["features"]
        ]
        self.assertEqual(len(datatype_cases), len(generator.DATATYPE_THEORY_CASES))
        self.assertEqual(len(hocore_cases), len(generator.HOCORE_THEORY_CASES))
        self.assertTrue(
            all(case["file"].startswith("cases/theories/datatypes/") for case in datatype_cases)
        )
        self.assertTrue(
            all(case["file"].startswith("cases/theories/hocore/") for case in hocore_cases)
        )
        self.assertTrue(
            any("theory-behavior:selector" in case["features"] for case in datatype_cases)
        )
        self.assertTrue(
            any("theory-behavior:disjointness" in case["features"] for case in datatype_cases)
        )
        symbolic_cases = [
            case for case in datatype_cases
            if "theory-behavior:symbolic-datatype-proof" in case["features"]
        ]
        self.assertEqual(len(symbolic_cases), 6)
        symbolic_features = {
            feature
            for case in symbolic_cases
            for feature in case["features"]
            if feature.startswith("theory-entry:Datatypes:symbolic-")
        }
        self.assertEqual(
            symbolic_features,
            {
                "theory-entry:Datatypes:symbolic-acyclicity",
                "theory-entry:Datatypes:symbolic-constructor-injectivity",
                "theory-entry:Datatypes:symbolic-mutual-family",
                "theory-entry:Datatypes:symbolic-parametric-instance",
                "theory-entry:Datatypes:symbolic-selector-constructor",
                "theory-entry:Datatypes:symbolic-tester-exhaustiveness",
            },
        )
        for case in symbolic_cases:
            self.assertIn("proof-rule:th-lemma-datatype", case["features"])
            for mode in ("proof-parse", "proof-replay"):
                self.assertEqual(case["expected"][mode]["status"], "pass")
                self.assertEqual(
                    case["expected"][mode].get("proof_rule_histogram"),
                    {"th-lemma-datatype": 1},
                )
            entry_feature = next(
                feature
                for feature in case["features"]
                if feature.startswith("theory-entry:Datatypes:symbolic-")
            )
            self.assertEqual(case["expected"]["z3-tac"]["status"], "pass", entry_feature)
            self.assertEqual(
                case["expected"]["z3-tac"].get("proof_rule_histogram"),
                {"th-lemma-datatype": 1},
            )
            self.assertIsNone(case["implementation_obligation"], case)
        hocore_by_id = {case["id"]: case for case in hocore_cases}
        new_case_ids = {
            "theory:HO_Core:at-apply",
            "theory:HO_Core:curried-function-sort",
            "theory:HO_Core:fo-apply-operator-fragment",
            "theory:HO_Core:fo-arrow-sort-fragment",
            "theory:HO_Core:fo-lambda-fragment",
            "theory:HO_Core:lambda-beta",
            "theory:HO_Core:lambda-extensionality",
            "theory:HO_Core:lambda-identity",
            "theory:HO_Core:lambda-under-quantifier",
            "theory:HO_Core:map-const-partial-application",
            "theory:HO_Core:map-valued-function-result",
            "theory:HO_Core:omission-sugar",
            "theory:HO_Core:ranked-symbol-partial-application",
            "theory:HO_Core:underscore-ambiguity",
            "theory:HO_Core:underscore-apply",
        }
        negative_case_ids = {
            "theory:HO_Core:ranked-symbol-partial-application",
            "theory:HO_Core:fo-lambda-fragment",
            "theory:HO_Core:fo-arrow-sort-fragment",
            "theory:HO_Core:fo-apply-operator-fragment",
        }
        self.assertFalse({
            case_id
            for case_id, case in hocore_by_id.items()
            if case["implementation_obligation"] is not None
        })

        scripts_by_id = {
            f"theory:HO_Core:{case.slug}": case.script
            for case in generator.HOCORE_THEORY_CASES
        }
        script_needles = {
            "theory:HO_Core:lambda-identity": (
                "(lambda ((x Bool)) x)",
            ),
            "theory:HO_Core:lambda-beta": (
                "(let ((f (lambda ((x Int)) (+ x 1)))) (f 2))",
            ),
            "theory:HO_Core:lambda-extensionality": (
                "(forall ((x Bool)) (= (f x) (g x)))",
                "(lambda ((x Bool)) (f x))",
            ),
            "theory:HO_Core:underscore-apply": ("(_ f 0)",),
            "theory:HO_Core:at-apply": ("(@ f 0.0)",),
            "theory:HO_Core:omission-sugar": ("(f 0)",),
            "theory:HO_Core:map-const-partial-application": (
                "(declare-const f (-> Int (-> Bool Bool)))",
                "(distinct (f 0) (f 0))",
            ),
            "theory:HO_Core:curried-function-sort": (
                "(declare-const f (-> Real (-> Bool Bool)))",
            ),
            "theory:HO_Core:lambda-under-quantifier": (
                "(assert (exists ((a Int))",
                "(lambda ((x Real)) (= x (to_real a)))",
            ),
            "theory:HO_Core:map-valued-function-result": (
                "(declare-fun make (Int) (-> Bool Bool))",
                "(distinct (make 0) (make 0))",
            ),
            "theory:HO_Core:ranked-symbol-partial-application": (
                "(declare-fun g (Bool Bool) Bool)",
                "(g true)",
            ),
            "theory:HO_Core:fo-lambda-fragment": (
                "(set-logic QF_UF)",
                "(lambda ((x Bool)) x)",
            ),
            "theory:HO_Core:fo-arrow-sort-fragment": (
                "(set-logic QF_LIA)",
                "(-> Int Int)",
            ),
            "theory:HO_Core:fo-apply-operator-fragment": (
                "(set-logic QF_AUFLIA)",
                "(_ f 0)",
            ),
            "theory:HO_Core:underscore-ambiguity": (
                "(_ BitVec 8)",
                "(_ f bv)",
            ),
        }
        self.assertEqual(set(script_needles), new_case_ids)
        for case_id, needles in script_needles.items():
            for needle in needles:
                self.assertIn(needle, scripts_by_id[case_id], case_id)

        curated_logic_cases = {
            "theory:HO_Core:lambda-identity": "HO_QF_UF",
            "theory:HO_Core:lambda-beta": "HO_QF_UFLIA",
            "theory:HO_Core:lambda-extensionality": "HO_UF",
            "theory:HO_Core:underscore-apply": "HO_UFLIA",
            "theory:HO_Core:at-apply": "HO_QF_UFLRA",
            "theory:HO_Core:omission-sugar": "HO_AUFLIA",
            "theory:HO_Core:map-const-partial-application": (
                "HO_QF_AUFLIA"
            ),
            "theory:HO_Core:curried-function-sort": "HO_UFLRA",
            "theory:HO_Core:lambda-under-quantifier": "HO_AUFLIRA",
            "theory:HO_Core:map-valued-function-result": "HO_ALL",
        }
        expected_ho_logics = {
            "HO_ALL",
            "HO_UF",
            "HO_QF_UF",
            "HO_UFLIA",
            "HO_QF_UFLIA",
            "HO_UFLRA",
            "HO_QF_UFLRA",
            "HO_AUFLIA",
            "HO_AUFLIRA",
            "HO_QF_AUFLIA",
        }
        self.assertEqual(set(curated_logic_cases.values()), expected_ho_logics)
        for case_id, logic in curated_logic_cases.items():
            self.assertEqual(hocore_by_id[case_id]["logic"], logic)

        lambda_case_ids = {
            "theory:HO_Core:fo-lambda-fragment",
            "theory:HO_Core:lambda-beta",
            "theory:HO_Core:lambda-extensionality",
            "theory:HO_Core:lambda-identity",
            "theory:HO_Core:lambda-under-quantifier",
        }
        for case_id in new_case_ids:
            case = hocore_by_id[case_id]
            for feature in {
                "function-sort",
                "function-valued",
                "higher-order",
                "higher-order/function-sort",
                "ho-core",
            }:
                self.assertIn(feature, case["features"], case_id)
            self.assertEqual("lambda" in case["features"], case_id in lambda_case_ids)
            expected_modes = ["parser-only", "typecheck-only", "z3-tac"]
            if case_id not in negative_case_ids:
                expected_modes = [
                    "parser-only",
                    "typecheck-only",
                    "z3-oracle",
                    "cvc5-oracle",
                    "z3-tac",
                ]
            self.assertEqual(case["modes"], expected_modes)
            self.assertEqual(case["expected"]["parser-only"]["status"], "pass")
            obligation = case["implementation_obligation"]
            if case_id in negative_case_ids:
                for mode in ("typecheck-only", "z3-tac"):
                    self.assertEqual(case["expected"][mode]["status"], "fail")
                    self.assertEqual(
                        case["expected"][mode]["failure_phase"],
                        "typecheck",
                    )
                self.assertIsNone(obligation, case_id)
            else:
                self.assertEqual(
                    case["expected"]["typecheck-only"]["status"], "pass"
                )
                self.assertNotIn(
                    "failure_phase", case["expected"]["typecheck-only"]
                )
                self.assertEqual(case["expected"]["z3-tac"]["status"], "pass")
                self.assertNotIn(
                    "failure_phase", case["expected"]["z3-tac"]
                )
                self.assertIsNone(obligation, case_id)
                self.assertEqual(case["expected"]["z3-oracle"]["status"], "fail")
                self.assertIn(
                    "unsupported logic",
                    case["expected"]["z3-oracle"]["diagnostic"],
                )
                cvc5_status = (
                    "fail"
                    if case_id in {
                        "theory:HO_Core:underscore-ambiguity",
                        "theory:HO_Core:underscore-apply",
                    }
                    else "pass"
                )
                self.assertEqual(
                    case["expected"]["cvc5-oracle"]["status"],
                    cvc5_status,
                )

        negative_diagnostics = {
            "theory:HO_Core:ranked-symbol-partial-application": (
                "function symbol 'g' of rank 2 cannot be partially applied; "
                "wrap it in a lambda (SMT-LIB 2.7 §3.9)"
            ),
            "theory:HO_Core:fo-lambda-fragment": (
                "higher-order construct (lambda) is outside logic fragment "
                "QF_UF"
            ),
            "theory:HO_Core:fo-arrow-sort-fragment": (
                "higher-order construct (arrow sort) is outside logic "
                "fragment QF_LIA"
            ),
            "theory:HO_Core:fo-apply-operator-fragment": (
                "higher-order construct (apply operator) is outside logic "
                "fragment QF_AUFLIA"
            ),
        }
        self.assertEqual(set(negative_diagnostics), negative_case_ids)
        for case_id, diagnostic in negative_diagnostics.items():
            case = hocore_by_id[case_id]
            self.assertIn("theory-case:type-error", case["features"])
            for mode in ("typecheck-only", "z3-tac"):
                self.assertEqual(
                    case["expected"][mode]["diagnostic"],
                    diagnostic,
                )

        native_case = hocore_by_id["theory:HO_Core:native-function-sort"]
        self.assertEqual(native_case["standard"], "SMT-LIB-2.7")
        self.assertEqual(
            native_case["modes"],
            ["parser-only", "typecheck-only", "z3-tac"],
        )
        self.assertIn("theory-case:sat", native_case["features"])
        self.assertIsNone(native_case["implementation_obligation"])
        for mode in native_case["modes"]:
            self.assertEqual(native_case["expected"][mode]["status"], "pass")

        legacy_green_ids = {
            "theory:HO_Core:function-argument-sort",
            "theory:HO_Core:function-result-sort",
            "theory:HO_Core:function-valued-array-declaration",
            "theory:HO_Core:higher-order-equality",
            "theory:HO_Core:native-function-sort",
        }
        function_sort_cases = [
            case for case in hocore_cases
            if "higher-order/function-sort" in case["features"]
        ]
        self.assertEqual(len(function_sort_cases), 20)
        for case_id in legacy_green_ids:
            case = hocore_by_id[case_id]
            self.assertIsNone(case["implementation_obligation"], case)
            for mode in case["modes"]:
                self.assertEqual(case["expected"][mode]["status"], "pass")

        runner = (TOOLS_DIR / "run_complete_smtlib_conformance.sh").read_text(
            encoding="utf-8"
        )
        function_sort_bucket = runner.split(
            '"function sorts": (', 1
        )[1].split("),", 1)[0]
        for needle in {
            '"function-sort"',
            '"function-valued"',
            '"higher-order"',
            '"lambda"',
            '"ho-core"',
        }:
            self.assertIn(needle, function_sort_bucket)
        strings_bucket_loop = runner.split(
            'if category == "strings/regex"', 1
        )[1].split(
            "if any(needle in text for needle in needles):", 1
        )[0]
        self.assertIn('"z3_extensions" in text', strings_bucket_loop)
        self.assertNotIn("--fail-on-red-obligations", runner)
        self.assertNotIn(
            'nonzero_exit_reasons.append("red-obligations")',
            runner,
        )
        self.assertNotIn(
            'elif summary["red_obligation_count"]',
            runner,
        )

    def test_soundness_subcommand_adds_string_injection_audits(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["soundness"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)
        self.assertEqual({case["class"] for case in cases}, {"soundness-audit"})
        injection_cases = [
            case for case in cases
            if any(
                feature.startswith("string-injection:")
                for feature in case["features"]
            )
        ]
        self.assertEqual(len(injection_cases), 4)
        self.assertEqual(
            {
                feature
                for case in injection_cases
                for feature in case["features"]
            },
            {
                "string-injection:concat",
                "string-injection:prefixof",
                "string-injection:lt",
                "string-injection:le",
            },
        )
        for case in injection_cases:
            self.assertEqual(case["modes"], ["z3-oracle"])
            self.assertEqual(
                case["expected"]["z3-oracle"]["status"], "pass"
            )
            self.assertIsNone(case["implementation_obligation"])

    def test_manifest_entry_preserves_red_obligation_contract(self):
        case_id = generator.deterministic_case_id("command", "command:future")
        common = {
            "case_id": case_id,
            "file": generator.deterministic_case_file("command", case_id),
            "logic": "QF_UF",
            "standard": "SMT-LIB-2.7",
            "row_class": "command",
            "features": ["command:future"],
            "modes": ["parser-only"],
            "versions": ["4.13.0"],
            "source": generator.source("SMT-LIB-standard", "future command"),
        }

        with self.assertRaisesRegex(generator.GeneratorError, "implementation_obligation"):
            generator.manifest_entry(
                **common,
                expected={"parser-only": generator.expected_result("red")},
                implementation_obligation=None,
            )

        obligation = generator.implementation_obligation(
            files=["src/HolSmt/SmtLib_Parser.sml"],
            feature="command:future",
            test_ids=[case_id],
            failure_phase="parser",
        )
        with self.assertRaisesRegex(generator.GeneratorError, "must be null"):
            generator.manifest_entry(
                **common,
                expected={"parser-only": generator.expected_result("pass")},
                implementation_obligation=obligation,
            )

    def test_write_mode_is_idempotent_and_writes_case_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp) / "corpus"
            manifest_path = root / "manifest.json"

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "samples", "--write"]), 0)
            first_manifest = manifest_path.read_text(encoding="utf-8")
            first_files = {
                str(path.relative_to(root)): path.read_text(encoding="utf-8")
                for path in sorted((root / "cases").rglob("*.smt2"))
            }

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "samples", "--write"]), 0)
            second_manifest = manifest_path.read_text(encoding="utf-8")
            second_files = {
                str(path.relative_to(root)): path.read_text(encoding="utf-8")
                for path in sorted((root / "cases").rglob("*.smt2"))
            }

            self.assertEqual(first_manifest, second_manifest)
            self.assertEqual(first_files, second_files)
            self.assertEqual(len(first_files), len(generator.CASE_CLASSES))
            audit.validate_v2_manifest(json.loads(second_manifest))

    def test_logics_write_mode_is_idempotent_and_writes_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp) / "corpus"
            manifest_path = root / "manifest.json"
            logics_json = root / "logics.json"

            args = [
                "--manifest",
                str(manifest_path),
                "--logics-json",
                str(logics_json),
                "logics",
                "--write",
            ]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(args), 0)
            first_manifest = manifest_path.read_text(encoding="utf-8")
            first_inventory = logics_json.read_text(encoding="utf-8")

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(args), 0)
            second_manifest = manifest_path.read_text(encoding="utf-8")
            second_inventory = logics_json.read_text(encoding="utf-8")

            self.assertEqual(first_manifest, second_manifest)
            self.assertEqual(first_inventory, second_inventory)
            cases = audit.validate_v2_manifest(json.loads(second_manifest))
            inventory = json.loads(second_inventory)
            packet_logics = audit.validate_logic_inventory(
                inventory,
                generator.parse_accepted_logics(generator.DEFAULT_LOGIC_SOURCE),
            )
            nonlinear_logics = {"QF_NIA", "QF_NRA", "NIA", "NRA"}
            int_real_logics = generator.INT_REAL_COERCION_LOGICS & set(packet_logics)
            datatype_logics = {logic for logic in packet_logics if "DT" in logic.removeprefix("QF_")}
            self.assertEqual(
                len(cases),
                6 * len(packet_logics)
                + len(nonlinear_logics & set(packet_logics))
                + len(int_real_logics)
                + len(datatype_logics),
            )

    def test_audit_subcommand_validates_existing_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = pathlib.Path(tmp) / "manifest.json"
            manifest_path.write_text(
                json.dumps({"schema_version": "2", "cases": []}, indent=2) + "\n",
                encoding="utf-8",
            )

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "audit"]), 0)

            self.assertIn("manifest ok: 0 case(s)", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
