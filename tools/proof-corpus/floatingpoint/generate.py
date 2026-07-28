#!/usr/bin/env python3
"""Generate the Phase 5 Z3 FloatingPoint proof-shape corpus."""

from __future__ import annotations

import json
import pathlib
from dataclasses import dataclass


ROOT = pathlib.Path(__file__).resolve().parent
VERSIONS = ["4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3"]
REQUIRED_CLASSES = [
    "ground-arithmetic",
    "ground-rem-round-to-integral",
    "conversion-rna",
    "conversion-mixed-format",
    "conversion-bv",
    "to-real-qf-fplra",
    "symbolic-comparison",
    "symbolic-classification",
    "symbolic-abs-neg",
    "nan-payload-equality",
    "literal-normalization",
    "arbitrary-format",
    "d12-tiny-add",
]


@dataclass(frozen=True)
class Case:
    case_id: str
    logic: str
    body: str
    description: str
    operators: tuple[str, ...]
    classes: tuple[str, ...]
    format: str


def case(
    case_id: str,
    body: str,
    description: str,
    *,
    operators: tuple[str, ...],
    classes: tuple[str, ...],
    logic: str = "QF_FP",
    format: str = "(3,5)",
) -> Case:
    return Case(
        case_id,
        logic,
        body.strip(),
        description,
        operators,
        classes,
        format,
    )


GROUND = [
    ("add", "fp.add", "(fp.add RNE (fp #b0 #b011 #b0000) (fp #b0 #b011 #b0000))", "(fp #b0 #b100 #b0000)"),
    ("sub", "fp.sub", "(fp.sub RNE (fp #b0 #b100 #b0000) (fp #b0 #b011 #b0000))", "(fp #b0 #b011 #b0000)"),
    ("mul", "fp.mul", "(fp.mul RNE (fp #b0 #b100 #b0000) (fp #b0 #b100 #b0000))", "(fp #b0 #b101 #b0000)"),
    ("div", "fp.div", "(fp.div RNE (fp #b0 #b100 #b0000) (fp #b0 #b100 #b0000))", "(fp #b0 #b011 #b0000)"),
    ("fma", "fp.fma", "(fp.fma RNE (fp #b0 #b011 #b0000) (fp #b0 #b011 #b0000) (fp #b0 #b011 #b0000))", "(fp #b0 #b100 #b0000)"),
    ("sqrt", "fp.sqrt", "(fp.sqrt RNE (fp #b0 #b101 #b0000))", "(fp #b0 #b100 #b0000)"),
]

CASES = [
    *[
        case(
            f"ground_{name}",
            f"(assert (not (= {term} {result})))",
            f"Ground evaluation of {operator}.",
            operators=(operator,),
            classes=("ground-arithmetic",),
        )
        for name, operator, term, result in GROUND
    ],
    case(
        "ground_rem",
        "(assert (not (= (fp.rem (fp #b0 #b101 #b0100) "
        "(fp #b0 #b100 #b0000)) (fp #b0 #b011 #b0000))))",
        "Ground fp.rem evaluation.",
        operators=("fp.rem",),
        classes=("ground-rem-round-to-integral",),
    ),
    case(
        "ground_round_to_integral_rna",
        "(assert (not (= (fp.roundToIntegral RNA "
        "(fp #b1 #b100 #b0100)) (fp #b1 #b100 #b1000))))",
        "RNA tie-away ground roundToIntegral (-2.5 to -3).",
        operators=("fp.roundToIntegral",),
        classes=("ground-rem-round-to-integral", "conversion-rna"),
    ),
    case(
        "ground_min_signed_zero_range",
        """
(assert
  (not
    (or (= (fp.min (_ +zero 3 5) (_ -zero 3 5)) (_ +zero 3 5))
        (= (fp.min (_ +zero 3 5) (_ -zero 3 5)) (_ -zero 3 5)))))
""",
        "The underspecified fp.min signed-zero result remains one operand.",
        operators=("fp.min",),
        classes=("ground-arithmetic",),
    ),
    case(
        "ground_max_signed_zero_range",
        """
(assert
  (not
    (or (= (fp.max (_ +zero 3 5) (_ -zero 3 5)) (_ +zero 3 5))
        (= (fp.max (_ +zero 3 5) (_ -zero 3 5)) (_ -zero 3 5)))))
""",
        "The underspecified fp.max signed-zero result remains one operand.",
        operators=("fp.max",),
        classes=("ground-arithmetic",),
    ),
    case(
        "convert_real_to_fp_rna_tie",
        "(assert (not (= ((_ to_fp 3 5) RNA (/ 33.0 32.0)) "
        "(fp #b0 #b011 #b0001))))",
        "RNA real-to-FP midpoint conversion.",
        operators=("to_fp",),
        classes=("conversion-rna",),
        logic="QF_FPLRA",
    ),
    case(
        "convert_mixed_format_rna",
        """
(assert
  (not
    (= ((_ to_fp 3 5) RNA (fp #b0 #b0111 #b000010))
       (fp #b0 #b011 #b0001))))
""",
        "RNA conversion from (4,7) to (3,5).",
        operators=("to_fp",),
        classes=("conversion-rna", "conversion-mixed-format"),
        format="(4,7)->(3,5)",
    ),
    case(
        "convert_mixed_format_chain",
        """
(assert
  (not
    (= ((_ to_fp 3 5) RNA ((_ to_fp 4 7) RNE (/ 33.0 32.0)))
       (fp #b0 #b011 #b0001))))
""",
        "Ground real-to-(4,7)-to-(3,5) conversion chain.",
        operators=("to_fp",),
        classes=("conversion-rna", "conversion-mixed-format"),
        logic="QF_FPLRA",
        format="Real->(4,7)->(3,5)",
    ),
    case(
        "convert_to_fp_bitcast",
        "(assert (not (= ((_ to_fp 3 5) #b00110000) "
        "(fp #b0 #b011 #b0000))))",
        "Bit-vector bitcast to FP.",
        operators=("to_fp",),
        classes=("conversion-bv",),
        logic="QF_BVFP",
    ),
    case(
        "convert_to_fp_signed",
        "(assert (not (= ((_ to_fp 3 5) RNE #b1101) "
        "(fp #b1 #b100 #b1000))))",
        "Signed bit-vector to FP.",
        operators=("to_fp",),
        classes=("conversion-bv",),
        logic="QF_BVFP",
    ),
    case(
        "convert_to_fp_unsigned",
        "(assert (not (= ((_ to_fp_unsigned 3 5) RNE #b1101) "
        "(fp #b0 #b110 #b1010))))",
        "Unsigned bit-vector to FP.",
        operators=("to_fp_unsigned",),
        classes=("conversion-bv",),
        logic="QF_BVFP",
    ),
    case(
        "convert_to_ubv",
        "(assert (not (= ((_ fp.to_ubv 4) RTZ "
        "(fp #b0 #b100 #b1000)) #b0011)))",
        "FP to unsigned bit-vector.",
        operators=("fp.to_ubv",),
        classes=("conversion-bv",),
        logic="QF_BVFP",
    ),
    case(
        "convert_to_sbv",
        "(assert (not (= ((_ fp.to_sbv 4) RTZ "
        "(fp #b1 #b100 #b1000)) #b1101)))",
        "FP to signed bit-vector.",
        operators=("fp.to_sbv",),
        classes=("conversion-bv",),
        logic="QF_BVFP",
    ),
    case(
        "convert_to_real_ground",
        "(assert (not (= (fp.to_real (fp #b0 #b011 #b1000)) "
        "(/ 3.0 2.0))))",
        "Ground fp.to_real evaluation.",
        operators=("fp.to_real",),
        classes=("to-real-qf-fplra",),
        logic="QF_FPLRA",
    ),
    case(
        "convert_to_real_symbolic_bridge",
        """
(declare-const x Float32)
(declare-const r Real)
(assert
  (not
    (=> (= x (_ +zero 8 24))
        (<= (+ (fp.to_real x) r) r))))
""",
        "Symbolic fp.to_real bridge to real arithmetic.",
        operators=("fp.to_real",),
        classes=("to-real-qf-fplra",),
        logic="QF_FPLRA",
        format="Float32",
    ),
    case(
        "nan_payload_equality",
        "(assert (not (= (fp #b1 #b11111 #b0000000001) "
        "(_ NaN 5 11))))",
        "SMT equality identifies a noncanonical NaN payload with NaN.",
        operators=(),
        classes=("nan-payload-equality",),
        format="(5,11)",
    ),
    *[
        case(
            f"literal_{name}",
            f"(assert (not (= (_ {special} 3 5) {triple})))",
            f"Normalize (_ {special} 3 5) to an fp triple.",
            operators=(),
            classes=("literal-normalization",),
        )
        for name, special, triple in (
            ("positive_zero", "+zero", "(fp #b0 #b000 #b0000)"),
            ("negative_zero", "-zero", "(fp #b1 #b000 #b0000)"),
            ("positive_infinity", "+oo", "(fp #b0 #b111 #b0000)"),
            ("negative_infinity", "-oo", "(fp #b1 #b111 #b0000)"),
            ("nan", "NaN", "(fp #b0 #b111 #b0001)"),
        )
    ],
]

COMPARISONS = [
    ("lt", "fp.lt", "(and (fp.lt x y) (fp.lt y x))"),
    ("gt", "fp.gt", "(and (fp.gt x y) (fp.gt y x))"),
    ("leq", "fp.leq", "(and (fp.leq x y) (fp.leq y x) (not (fp.eq x y)))"),
    ("geq", "fp.geq", "(and (fp.geq x y) (fp.geq y x) (not (fp.eq x y)))"),
    ("eq", "fp.eq", "(and (fp.eq x y) (not (fp.leq x y)))"),
]
CASES.extend(
    case(
        f"symbolic_comparison_{name}",
        f"""
(declare-const x (_ FloatingPoint 3 5))
(declare-const y (_ FloatingPoint 3 5))
(assert {formula})
""",
        f"Small-format symbolic {operator} atom conversion.",
        operators=(operator, *( ("fp.eq",) if "fp.eq" in formula and operator != "fp.eq" else () ), *( ("fp.leq",) if "fp.leq" in formula and operator != "fp.leq" else () )),
        classes=("symbolic-comparison",),
    )
    for name, operator, formula in COMPARISONS
)

CLASSIFICATIONS = [
    ("normal_subnormal", ("fp.isNormal", "fp.isSubnormal"), "(and (fp.isNormal x) (fp.isSubnormal x))"),
    ("zero_normal", ("fp.isZero", "fp.isNormal"), "(and (fp.isZero x) (fp.isNormal x))"),
    ("infinite_normal", ("fp.isInfinite", "fp.isNormal"), "(and (fp.isInfinite x) (fp.isNormal x))"),
    ("nan_positive", ("fp.isNaN", "fp.isPositive"), "(and (fp.isNaN x) (fp.isPositive x))"),
    ("negative_positive", ("fp.isNegative", "fp.isPositive"), "(and (fp.isNegative x) (fp.isPositive x))"),
]
CASES.extend(
    case(
        f"symbolic_classification_{name}",
        f"(declare-const x (_ FloatingPoint 3 5))\n(assert {formula})",
        "Small-format incompatible classification predicates.",
        operators=operators,
        classes=("symbolic-classification",),
    )
    for name, operators, formula in CLASSIFICATIONS
)
CASES.extend(
    [
        case(
            "symbolic_abs",
            "(declare-const x (_ FloatingPoint 3 5))\n"
            "(assert (fp.isNegative (fp.abs x)))",
            "Absolute value is never negative.",
            operators=("fp.abs", "fp.isNegative"),
            classes=("symbolic-abs-neg",),
        ),
        case(
            "symbolic_neg",
            "(declare-const x (_ FloatingPoint 3 5))\n"
            "(assert (not (= (fp.neg (fp.neg x)) x)))",
            "Double negation, including canonical SMT NaN equality.",
            operators=("fp.neg",),
            classes=("symbolic-abs-neg",),
        ),
    ]
)
for name, sort in (("float32", "Float32"), ("float64", "Float64"), ("float128", "Float128")):
    CASES.append(
        case(
            f"arbitrary_format_{name}",
            f"(declare-const x {sort})\n"
            "(assert (fp.isNormal x))\n"
            "(assert (fp.lt (fp.abs x) (fp.abs x)))",
            f"Cheap bit-decomposition probe on {sort}.",
            operators=("fp.isNormal", "fp.lt", "fp.abs"),
            classes=("arbitrary-format",),
            format=sort,
        )
    )
CASES.extend(
    [
        case(
            "scale_lt_asymmetry_float32",
            """
(declare-const x Float32)
(declare-const y Float32)
(assert (fp.lt x y))
(assert (fp.lt y x))
""",
            "Float32 comparison scale probe.",
            operators=("fp.lt",),
            classes=("symbolic-comparison",),
            format="Float32",
        ),
        case(
            "scale_mul_identity_float16",
            """
(declare-const x Float16)
(assert
  (not
    (= (fp.mul RNE x (fp #b0 #b01111 #b0000000000)) x)))
""",
            "Float16 symbolic multiplication scale probe.",
            operators=("fp.mul",),
            classes=("ground-arithmetic",),
            format="Float16",
        ),
        case(
            "d12_add_commutativity_tiny",
            """
(declare-const x (_ FloatingPoint 3 5))
(declare-const y (_ FloatingPoint 3 5))
(assert
  (not
    (= (fp.add RNE x y)
       (fp.add RNE y x))))
""",
            "D12 exemplar: symbolic add only on the tiny (3,5) format.",
            operators=("fp.add",),
            classes=("d12-tiny-add",),
            format="(3,5)",
        ),
    ]
)


def write_case(item: Case) -> pathlib.Path:
    path = ROOT / "inputs" / f"{item.case_id}.smt2"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"""(set-option :produce-proofs true)
(set-logic {item.logic})
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
        manifest_cases.append(
            {
                "id": item.case_id,
                "path": str(path.relative_to(ROOT)),
                "description": item.description,
                "expected_result": "unsat",
                "operators": list(item.operators),
                "classes": list(item.classes),
                "format": item.format,
            }
        )
    manifest = {
        "schema": "holsmt-z3-fp-proof-corpus-v1",
        "description": (
            "Phase 5 fpa2bv rewrite corpus across every supported Z3 4.x."
        ),
        "supported_z3_versions": VERSIONS,
        "required_classes": REQUIRED_CLASSES,
        "forbidden_rule_occurrences": [
            "th-lemma-fp",
            "th-lemma-fpa",
            "th-lemma-floating-point",
        ],
        "cases": manifest_cases,
        "metadata_only_cases": [
            {
                "id": "d12_add_commutativity_float32",
                "description": (
                    "Float32 symbolic fp.add commutativity; payload excluded "
                    "by task mandate because the drafting run was 891 MiB."
                ),
                "format": "Float32",
                "operator": "fp.add",
                "proof_recorded": False,
                "proof_size_mib": 891,
                "solve_seconds": 65,
                "measurement": "Phase 5 plan drafting, Z3 4.15.3",
            }
        ],
    }
    (ROOT / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
