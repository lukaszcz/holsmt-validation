#!/usr/bin/env python3

import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import run_cvc5_cpc_matrix as matrix


class Cvc5CpcMatrixTests(unittest.TestCase):
    def test_timeout_output_bytes_are_decoded(self):
        timeout = subprocess.TimeoutExpired(
            cmd=["driver"], timeout=1, output=b"partial stdout\n",
            stderr=b"partial stderr\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            query = pathlib.Path(tmp) / "query.smt2"
            query.write_text(
                "(set-logic QF_FP)\n(assert false)\n(check-sat)\n",
                encoding="utf-8",
            )
            with mock.patch.object(
                matrix.subprocess, "run", side_effect=timeout
            ):
                result = matrix.run_one(
                    pathlib.Path("driver"), "cvc5", query, 1
                )

        self.assertTrue(result["timed_out"])
        self.assertEqual(result["stdout"], "partial stdout\n")
        self.assertEqual(result["stderr"], "partial stderr\n")


if __name__ == "__main__":
    unittest.main()
