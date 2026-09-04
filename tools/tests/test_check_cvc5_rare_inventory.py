#!/usr/bin/env python3

import os
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import check_cvc5_rare_inventory as checker


class RareInventoryRootDiscoveryTests(unittest.TestCase):
    def marked_root(self, base: pathlib.Path) -> pathlib.Path:
        root = base / "hol"
        holsmt = root / "src" / "HolSmt"
        holsmt.mkdir(parents=True)
        (holsmt / "Unittest.sml").write_text(
            "\n".join(
                [
                    checker.HOL_FIXTURE_START,
                    checker.HOL_FIXTURE_END,
                    checker.HOL_PUBLIC_LIST_START,
                    checker.HOL_PUBLIC_LIST_END,
                ]
            ),
            encoding="utf-8",
        )
        (holsmt / "CPC_Proof.sml").write_text(
            "val cvc134_rare_source_recipe_table = []\n"
            "val cvc134_rare_unsupported_source_reasons = []\n",
            encoding="utf-8",
        )
        return root

    def test_explicit_root_takes_precedence_anywhere(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp)
            root = self.marked_root(base)
            with mock.patch.dict(
                os.environ, {"HOLSMT_ROOT": str(base / "wrong")}
            ):
                self.assertEqual(checker.discover_hol_root(root), root)

    def test_environment_root_precedes_cwd_ancestors(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp)
            root = self.marked_root(base)
            elsewhere = base / "elsewhere"
            elsewhere.mkdir()
            old_cwd = pathlib.Path.cwd()
            try:
                os.chdir(elsewhere)
                with mock.patch.dict(
                    os.environ, {"HOLSMT_ROOT": str(root)}, clear=False
                ):
                    self.assertEqual(checker.discover_hol_root(None), root)
            finally:
                os.chdir(old_cwd)

    def test_default_searches_marked_cwd_ancestors(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp)
            root = self.marked_root(base)
            nested = root / "a" / "b"
            nested.mkdir(parents=True)
            old_cwd = pathlib.Path.cwd()
            try:
                os.chdir(nested)
                with mock.patch.dict(os.environ, {}, clear=True):
                    self.assertEqual(checker.discover_hol_root(None), root)
            finally:
                os.chdir(old_cwd)

    def test_no_marked_tree_requests_override(self):
        with tempfile.TemporaryDirectory() as tmp:
            old_cwd = pathlib.Path.cwd()
            try:
                os.chdir(tmp)
                with mock.patch.dict(os.environ, {}, clear=True):
                    with self.assertRaisesRegex(
                        SystemExit, "pass --hol-root or set HOLSMT_ROOT"
                    ):
                        checker.discover_hol_root(None)
            finally:
                os.chdir(old_cwd)

    def test_invalid_override_fails_without_guessing(self):
        with tempfile.TemporaryDirectory() as tmp:
            wrong = pathlib.Path(tmp)
            with self.assertRaisesRegex(SystemExit, "required HolSmt"):
                checker.discover_hol_root(wrong)


if __name__ == "__main__":
    unittest.main()
