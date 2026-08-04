#!/usr/bin/env python3

import pathlib
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import record_cvc5_cpc_corpus as recorder


class CpcCorpusRecorderTests(unittest.TestCase):
    def test_inventory_records_exact_rare_names_and_conclusions(self):
        proof = """(
(step @p1 (= re.all (re.* re.allchar)) :rule re-all-elim)
(step @p2 :rule str-in-re-eval :args (true))
)"""

        report = recorder.inventory(proof)

        self.assertEqual(
            report["rules"],
            {"re-all-elim": 1, "str-in-re-eval": 1},
        )
        self.assertEqual(report["step_count"], 2)
        self.assertEqual(report["explicit_conclusions"], 1)
        self.assertEqual(report["optional_conclusions"], 1)

    def test_capture_requests_explicit_cpc_conclusions(self):
        completed = mock.Mock(
            stdout="unsat\n((step @p1 false :rule evaluate))\n",
            stderr="",
            returncode=0,
        )
        with tempfile.TemporaryDirectory() as tmp:
            input_path = pathlib.Path(tmp) / "input.smt2"
            input_path.write_text(
                "(set-logic QF_S)\n(assert false)\n(check-sat)\n",
                encoding="utf-8",
            )
            with mock.patch.object(
                recorder.subprocess, "run", return_value=completed
            ) as run:
                entry = recorder.run_one(
                    "cvc5",
                    "dsl-rewrite",
                    input_path,
                    10,
                    pathlib.Path(tmp) / "raw",
                    ["--fp-exp"],
                )

        command = run.call_args.args[0]
        self.assertIn("--proof-print-conclusion", command)
        self.assertIn("--fp-exp", command)
        self.assertTrue(entry["proof_print_conclusion"])
        self.assertEqual(entry["inventory"]["explicit_conclusions"], 1)
        self.assertEqual(entry["proof_bytes"], 33)
        self.assertFalse(entry["d12_proof_size_gate"])


if __name__ == "__main__":
    unittest.main()
