#!/usr/bin/env python3
"""Generate the Phase 4 Z3 string/regex proof-corpus inputs."""

from __future__ import annotations

import json
import pathlib
from dataclasses import dataclass


ROOT = pathlib.Path(__file__).resolve().parent
VERSIONS = ["4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"]


@dataclass(frozen=True)
class Case:
    case_id: str
    logic: str
    body: str
    description: str
    operators: tuple[str, ...] = ()
    drafting_probe: str | None = None


def case(
    case_id: str,
    body: str,
    description: str,
    *,
    logic: str = "QF_S",
    operators: tuple[str, ...] = (),
    drafting_probe: str | None = None,
) -> Case:
    return Case(
        case_id,
        logic,
        body.strip(),
        description,
        operators,
        drafting_probe,
    )


DRAFTING_CASES = [
    case(
        "draft_concat",
        """
(declare-const x String)
(assert (= (str.++ x "a") (str.++ x "b")))
""",
        "Symbolic right-concatenation contradiction.",
        operators=("str.++",),
        drafting_probe="concat",
    ),
    case(
        "draft_length",
        """
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "abc"))
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
""",
        "Concat/length arithmetic contradiction.",
        logic="QF_SLIA",
        operators=("str.++", "str.len"),
        drafting_probe="length",
    ),
    case(
        "draft_regex_membership",
        """
(declare-const x String)
(assert (str.in_re x (re.range "a" "z")))
(assert (str.< x "a"))
""",
        "Range membership contradicting lexicographic order.",
        operators=("str.in_re", "re.range", "str.<"),
        drafting_probe="regex-membership",
    ),
    case(
        "draft_substr",
        """
(declare-const x String)
(assert (= (str.len x) 1))
(assert (not (= (str.substr x 0 1) x)))
""",
        "Length-one substring identity.",
        logic="QF_SLIA",
        operators=("str.len", "str.substr"),
        drafting_probe="substr",
    ),
    case(
        "draft_contains",
        """
(declare-const x String)
(assert (not (str.contains (str.++ x "a") "a")))
""",
        "A string contains its appended suffix.",
        operators=("str.contains", "str.++"),
        drafting_probe="contains",
    ),
    case(
        "draft_str_lt",
        """
(declare-const x String)
(declare-const y String)
(assert (str.< x y))
(assert (str.< y x))
""",
        "Lexicographic order asymmetry.",
        operators=("str.<",),
        drafting_probe="str-lt",
    ),
    case(
        "draft_str_to_int",
        """
(declare-const x String)
(assert (= (str.to_int x) 42))
(assert (= (str.len x) 1))
""",
        "A one-character decimal string cannot denote 42.",
        logic="QF_SLIA",
        operators=("str.to_int", "str.len"),
        drafting_probe="str-to-int",
    ),
    case(
        "draft_re_loop",
        """
(declare-const x String)
(assert (str.in_re x ((_ re.loop 1 3) (str.to_re "a"))))
(assert (= (str.len x) 4))
""",
        "Bounded repetition contradicting string length.",
        logic="QF_SLIA",
        operators=("str.in_re", "re.loop", "str.to_re", "str.len"),
        drafting_probe="re-loop",
    ),
    case(
        "draft_re_comp",
        """
(declare-const x String)
(assert (str.in_re x (str.to_re "a")))
(assert (str.in_re x (re.comp (str.to_re "a"))))
""",
        "A string cannot inhabit a language and its complement.",
        operators=("str.in_re", "str.to_re"),
        drafting_probe="re-comp",
    ),
    case(
        "draft_replace_all_ground",
        """
(assert (not (= (str.replace_all "aba" "a" "c") "cbc")))
""",
        "Ground replace_all proof-producing instance.",
        operators=("str.replace_all",),
        drafting_probe="replace-all-ground",
    ),
    case(
        "draft_literal_escapes",
        r'''
(assert
  (not
    (and
      (= "\u0007" "\u{7}")
      (= "\u0022" """")
      (= "\u005c" "\")
      (= "\u0041\u{1f642}" "A\u{1F642}")
      (= "\u{2ffff}" "\u{2FFFF}"))))
''',
        "Pin Z3 proof-output spelling for control, quote, backslash, "
        "non-BMP, and maximum code points.",
        drafting_probe="literal-escapes",
    ),
]


OPERATOR_CASES = [
    ("str_concat", "str.++", '(assert (not (= (str.++ "a" "b") "ab")))'),
    ("str_len", "str.len", '(assert (not (= (str.len "abc") 3)))'),
    ("str_lt", "str.<", '(assert (not (str.< "a" "b")))'),
    ("str_le", "str.<=", '(assert (not (str.<= "a" "a")))'),
    ("str_at", "str.at", '(assert (not (= (str.at "abc" 1) "b")))'),
    (
        "str_substr",
        "str.substr",
        '(assert (not (= (str.substr "abc" 1 2) "bc")))',
    ),
    (
        "str_prefixof",
        "str.prefixof",
        '(assert (not (str.prefixof "ab" "abc")))',
    ),
    (
        "str_suffixof",
        "str.suffixof",
        '(assert (not (str.suffixof "bc" "abc")))',
    ),
    (
        "str_contains",
        "str.contains",
        '(assert (not (str.contains "abc" "b")))',
    ),
    (
        "str_indexof",
        "str.indexof",
        '(assert (not (= (str.indexof "abcabc" "bc" 0) 1)))',
    ),
    (
        "str_replace",
        "str.replace",
        '(assert (not (= (str.replace "aba" "a" "x") "xba")))',
    ),
    (
        "str_replace_all",
        "str.replace_all",
        '(assert (not (= (str.replace_all "aba" "a" "x") "xbx")))',
    ),
    (
        "str_is_digit",
        "str.is_digit",
        '(assert (not (str.is_digit "7")))',
    ),
    (
        "str_to_code",
        "str.to_code",
        '(assert (not (= (str.to_code "A") 65)))',
    ),
    (
        "str_from_code",
        "str.from_code",
        '(assert (not (= (str.from_code 65) "A")))',
    ),
    (
        "str_to_int",
        "str.to_int",
        '(assert (not (= (str.to_int "123") 123)))',
    ),
    (
        "str_from_int",
        "str.from_int",
        '(assert (not (= (str.from_int 123) "123")))',
    ),
    (
        "str_to_re",
        "str.to_re",
        '(assert (not (str.in_re "a" (str.to_re "a"))))',
    ),
    (
        "str_in_re",
        "str.in_re",
        '(assert (not (str.in_re "a" (str.to_re "a"))))',
    ),
    (
        "str_replace_re",
        "str.replace_re",
        '(assert (not (= (str.replace_re "abc" (str.to_re "b") "X") '
        '(str.replace_re "abc" (str.to_re "b") "X"))))',
    ),
    (
        "str_replace_re_all",
        "str.replace_re_all",
        '(assert (not (= '
        '(str.replace_re_all "aba" (str.to_re "a") "X") '
        '(str.replace_re_all "aba" (str.to_re "a") "X"))))',
    ),
    ("re_none", "re.none", '(assert (str.in_re "a" re.none))'),
    ("re_all", "re.all", '(assert (not (str.in_re "abc" re.all)))'),
    (
        "re_allchar",
        "re.allchar",
        '(assert (not (str.in_re "a" re.allchar)))',
    ),
    (
        "re_concat",
        "re.++",
        '(assert (not (str.in_re "ab" '
        '(re.++ (str.to_re "a") (str.to_re "b")))))',
    ),
    (
        "re_union",
        "re.union",
        '(assert (not (str.in_re "a" '
        '(re.union (str.to_re "a") (str.to_re "b")))))',
    ),
    (
        "re_inter",
        "re.inter",
        '(assert (not (str.in_re "a" '
        '(re.inter re.allchar (str.to_re "a")))))',
    ),
    (
        "re_diff",
        "re.diff",
        '(assert (not (str.in_re "b" '
        '(re.diff re.allchar (str.to_re "a")))))',
    ),
    (
        "re_star",
        "re.*",
        '(assert (not (str.in_re "aaa" (re.* (str.to_re "a")))))',
    ),
    (
        "re_plus",
        "re.+",
        '(assert (not (str.in_re "aaa" (re.+ (str.to_re "a")))))',
    ),
    (
        "re_opt",
        "re.opt",
        '(assert (not (str.in_re "" (re.opt (str.to_re "a")))))',
    ),
    (
        "re_range",
        "re.range",
        '(assert (not (str.in_re "m" (re.range "a" "z"))))',
    ),
    (
        "re_power",
        "re.^",
        '(assert (not (str.in_re "aa" ((_ re.^ 2) (str.to_re "a")))))',
    ),
    (
        "re_loop",
        "re.loop",
        '(assert (not (str.in_re "aa" '
        '((_ re.loop 1 3) (str.to_re "a")))))',
    ),
]


EXTRA_CASES = [
    case(
        "extra_re_comp",
        '(assert (not (str.in_re "b" (re.comp (str.to_re "a")))))',
        "Ground complement instance for the missing frontend dictionary entry.",
    ),
    case(
        "extra_char_constant",
        '(assert (not (= (_ char #x41) "A")))',
        "Ground indexed char constant for the missing frontend "
        "dictionary entry.",
    ),
]


CASES = [
    *DRAFTING_CASES,
    *[
        case(
            f"operator_{case_id}",
            body,
            f"Ground unsat proof instance for {operator}.",
            operators=(operator,),
        )
        for case_id, operator, body in OPERATOR_CASES
    ],
    *EXTRA_CASES,
]


def write_case(item: Case) -> pathlib.Path:
    path = ROOT / "inputs" / f"{item.case_id}.smt2"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"""(set-logic {item.logic})
(set-option :produce-proofs true)
{item.body}
(check-sat)
(get-proof)
(exit)
""",
        encoding="utf-8",
    )
    return path


def main() -> None:
    manifest_cases = []
    for item in CASES:
        path = write_case(item)
        manifest_item: dict[str, object] = {
            "id": item.case_id,
            "path": str(path.relative_to(ROOT)),
            "description": item.description,
            "expected_result": "unsat",
            "operators": list(item.operators),
        }
        if item.drafting_probe is not None:
            manifest_item["drafting_probe"] = item.drafting_probe
        manifest_cases.append(manifest_item)

    manifest = {
        "schema": "holsmt-z3-string-proof-corpus-v1",
        "description": (
            "Phase 4 Z3 string/regex proof-shape corpus: eleven drafting "
            "probes, the 34-operator surface, re.comp, and (_ char H)."
        ),
        "supported_z3_versions": VERSIONS,
        "required_rule_occurrences": ["th-lemma-seq", "th-lemma-char"],
        "required_theory_subkinds": ["seq:*", "char:*"],
        "cases": manifest_cases,
    }
    (ROOT / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
