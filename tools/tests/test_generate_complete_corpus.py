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
            self.assertEqual(case["expected"]["proof-replay"]["status"], "red")
            self.assertEqual(case["expected"]["z3-tac"]["status"], "red")
            self.assertIsNotNone(case["implementation_obligation"])
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
                self.assertEqual(
                    case["expected"]["proof-replay"]["diagnostic"],
                    "lambda proof-term replay is not implemented",
                )
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
            all(case["standard"] == "Z3-extension" for case in extension_cases)
        )
        self.assertTrue(
            all(case["file"].startswith("cases/theories/z3_extensions/") for case in extension_cases)
        )
        for case in string_cases + extension_cases:
            self.assertIn("typecheck-only", case["modes"])
            self.assertFalse(set(case["modes"]) <= {"parser-only"})
            if "theory-case:type-error" not in case["features"]:
                self.assertIn("z3-oracle", case["modes"])
            if "theory-case:unsat-proof" in case["features"]:
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

        checked_unsat_ids = {
            "theory:ArraysEx:array:unsat-proof",
            "theory:ArraysEx:store:unsat-proof",
            "theory:Core:xor:unsat-proof",
            "theory:Z3_Extensions:set:unsat-proof",
        }
        by_id = {case["id"]: case for case in cases}
        for case_id in checked_unsat_ids:
            self.assertEqual(by_id[case_id]["expected"]["z3-tac"]["status"], "pass")
            self.assertNotIn("theorem_shape", by_id[case_id]["expected"]["z3-tac"])
        self.assertEqual(
            by_id["theory:Z3_Extensions:set:unsat-proof"]["implementation_obligation"]["failure_phase"],
            "typecheck",
        )

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
        self.assertEqual(
            new_case_ids - negative_case_ids,
            {
                case_id
                for case_id, case in hocore_by_id.items()
                if case["implementation_obligation"] is not None
            },
        )

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
                self.assertEqual(case["expected"]["z3-tac"]["status"], "red")
                self.assertEqual(
                    case["expected"]["z3-tac"]["failure_phase"],
                    "translation",
                )
                self.assertIsNotNone(obligation, case_id)
                self.assertEqual(obligation["test_ids"], [case_id])
                self.assertEqual(obligation["failure_phase"], "translation")
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
