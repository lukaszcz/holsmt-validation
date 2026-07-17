import json
import re
import shlex
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPECTED = {"4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"}


class Z3VersionContractTests(unittest.TestCase):
    def test_supported_version_sets_agree(self):
        verifier = (ROOT / "tools/verify_z3_versions.sh").read_text()
        runner = (ROOT / "tools/run_holsmt_tests.sh").read_text()
        manifest = json.loads(
            (ROOT / "tools/proof-corpus/complete/manifest.json").read_text()
        )

        verifier_match = re.search(r"^versions=\(([^)]*)\)", verifier, re.MULTILINE)
        self.assertIsNotNone(verifier_match)
        verifier_versions = set(shlex.split(verifier_match.group(1)))

        prose_match = re.search(
            r'^supported_z3_versions="([^"]*)"', runner, re.MULTILINE
        )
        self.assertIsNotNone(prose_match)
        runner_prose_versions = set(shlex.split(prose_match.group(1)))

        predicate_match = re.search(
            r'case "\$major\.\$minor\.\$patch" in\s*\n\s*([^\n)]+)\)',
            runner,
        )
        self.assertIsNotNone(predicate_match)
        predicate_versions = set(predicate_match.group(1).strip().split("|"))

        manifest_versions = set(manifest["supported_z3_versions"])

        self.assertEqual(verifier_versions, EXPECTED)
        self.assertEqual(runner_prose_versions, EXPECTED)
        self.assertEqual(predicate_versions, EXPECTED)
        self.assertEqual(manifest_versions, EXPECTED)


if __name__ == "__main__":
    unittest.main()
