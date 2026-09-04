#!/usr/bin/env python3
"""Reproduce the cvc5-1.3.4 String/RegLan/Seq RARE name fixture."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import os
import re
import sys
import tempfile
import urllib.request
from pathlib import Path

sys.dont_write_bytecode = True

COMMIT = "f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341"
FILES = {
    "rewrites": (
        158,
        "17bac2be55ec7ceae74c5dc1d3fdb815ecc61cb5bffc9d9255ae2ee2e7928448",
    ),
    "rewrites-regexp-membership": (
        11,
        "b51f9aaeae45818b9b5ef72c78abe0a806d8a05b6921b0566ba1d6f0e8f3e051",
    ),
}
NAMES_SHA256 = (
    "93bb14fc27bf70bea2ed39ddd34f091f5b9d8ef5c8ecd32c4b20ad56ba65fc78"
)
RULE = re.compile(r"^\(define(?:-cond)?-rule\*?\s+(\S+)")
HOL_FIXTURE_START = "val cvc134_authoritative_string_rare_names = ["
HOL_FIXTURE_END = "]\n\nfun cpc_rare_inventory_part2_source_sweep"
HOL_PUBLIC_LIST_START = "  val list_bearing_proved_names = ["
HOL_PUBLIC_LIST_END = "]\n  val former_legacy_names = ["
LIST_AGGREGATE_SHA256 = (
    "4648895120c301155f8f7bb306c7938d349e159446d4fbf57bea70639c185f81"
)
LIST_AGGREGATES = {"str.++", "re.++", "re.union", "re.inter"}
HOL_AGGREGATES = {
    "RareSourceSeqConcat": "str.++",
    "RareSourceRegexConcat": "re.++",
    "RareSourceRegexUnion": "re.union",
    "RareSourceRegexInter": "re.inter",
}
FIRST_TRANCHE_LIST_FORMALS = {
    ("str-contains-concat-find", "xs"),
    ("str-contains-concat-find", "zs"),
    ("str-contains-concat-find-contra", "xs"),
    ("str-contains-concat-find-contra", "zs"),
    ("str-contains-split-char", "z"),
    ("str-len-concat-rec", "s3"),
    ("str-len-eq-zero-concat-rec", "s3"),
}
TOKEN = re.compile(r'"(?:[^"]|"")*"|[()]|[^\s()]+')


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_sexps(text: str) -> list[object]:
    text = "\n".join(line.split(";", 1)[0] for line in text.splitlines())
    tokens = TOKEN.findall(text)
    position = 0

    def parse() -> object:
        nonlocal position
        token = tokens[position]
        position += 1
        if token != "(":
            return token
        result = []
        while tokens[position] != ")":
            result.append(parse())
        position += 1
        return result

    result = []
    while position < len(tokens):
        result.append(parse())
    return result


def source_list_aggregates(text: str) -> dict[tuple[str, str], str]:
    result = {}
    for expression in parse_sexps(text):
        if not (
            isinstance(expression, list)
            and expression
            and isinstance(expression[0], str)
            and re.fullmatch(r"define(?:-cond)?-rule\*?", expression[0])
        ):
            continue
        rule = expression[1]
        for formal in expression[2]:
            if not (isinstance(formal, list) and ":list" in formal):
                continue
            name = formal[0]
            parents = []

            def visit(item: object, parent: str | None = None) -> None:
                if item == name:
                    parents.append(parent)
                if isinstance(item, list):
                    head = (
                        item[0]
                        if item and isinstance(item[0], str)
                        else None
                    )
                    for child in item[1:]:
                        visit(child, head)

            for body in expression[3:]:
                visit(body)
            aggregates = set(parents)
            if len(aggregates) != 1 or not aggregates <= LIST_AGGREGATES:
                raise SystemExit(
                    f"{rule}/{name}: ambiguous source aggregates {aggregates}"
                )
            result[(rule, name)] = aggregates.pop()
    return result


def hol_list_aggregates(text: str) -> dict[tuple[str, str], str]:
    table = text.split("val cvc134_rare_source_recipe_table", 1)[1].split(
        "val cvc134_rare_unsupported_source_reasons", 1
    )[0]
    result = {}
    entries = re.finditer(
        r"rare_entry .*?\(RareSourceRecipe \{(.*?)\}\)\s*\"([^\"]+)\"",
        table,
        re.DOTALL,
    )
    for entry in entries:
        body, rule = entry.groups()
        for formal, aggregate in re.findall(
            r'\("([^\"]+)",\s*RareSourceList\s+(RareSource\w+),\s*'
            r"RareSource\w+\)",
            body,
        ):
            result[(rule, formal)] = HOL_AGGREGATES[aggregate]
    return result


def obtain(name: str, source_dir: Path | None, temporary: Path) -> bytes:
    if source_dir is not None:
        path = source_dir / "src" / "theory" / "strings" / name
        return path.read_bytes()
    url = (
        "https://raw.githubusercontent.com/cvc5/cvc5/"
        f"{COMMIT}/src/theory/strings/{name}"
    )
    destination = temporary / name
    urllib.request.urlretrieve(url, destination)
    return destination.read_bytes()


def has_embedded_fixture(root: Path) -> bool:
    """Return whether root is the HOL tree this checker can audit."""
    unittest = root / "src" / "HolSmt" / "Unittest.sml"
    proof = root / "src" / "HolSmt" / "CPC_Proof.sml"
    try:
        unittest_text = unittest.read_text(encoding="utf-8")
        proof_text = proof.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return False
    return (
        HOL_FIXTURE_START in unittest_text
        and HOL_FIXTURE_END in unittest_text
        and HOL_PUBLIC_LIST_START in unittest_text
        and HOL_PUBLIC_LIST_END in unittest_text
        and "val cvc134_rare_source_recipe_table" in proof_text
        and "val cvc134_rare_unsupported_source_reasons" in proof_text
    )


def discover_hol_root(explicit: Path | None) -> Path:
    """Resolve override, environment, then a marked cwd ancestor."""
    candidates: list[tuple[str, Path]] = []
    if explicit is not None:
        candidates.append(("--hol-root", explicit))
    elif "HOLSMT_ROOT" in os.environ:
        candidates.append(("HOLSMT_ROOT", Path(os.environ["HOLSMT_ROOT"])))
    else:
        cwd = Path.cwd().resolve()
        candidates.extend(("cwd ancestor", path) for path in (cwd, *cwd.parents))

    for source, candidate in candidates:
        candidate = candidate.expanduser().resolve()
        if has_embedded_fixture(candidate):
            return candidate
        if source != "cwd ancestor":
            raise SystemExit(
                f"{source} does not name a HOL tree with the required "
                f"HolSmt embedded fixture markers: {candidate}"
            )
    raise SystemExit(
        "cannot locate a HOL tree with the required HolSmt embedded fixture "
        "markers from cwd ancestors; pass --hol-root or set HOLSMT_ROOT"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source-dir",
        type=Path,
        help=(
            "existing cvc5 checkout/export at the pinned commit "
            "(offline mode)"
        ),
    )
    parser.add_argument(
        "--fixture",
        type=Path,
        default=Path(__file__).with_name(
            "cvc5-1.3.4-string-rare-names.txt"
        ),
    )
    parser.add_argument(
        "--hol-root",
        type=Path,
        help="HOL tree whose embedded closure fixture is checked",
    )
    args = parser.parse_args()
    args.hol_root = discover_hol_root(args.hol_root)

    names: list[str] = []
    source_aggregates: dict[tuple[str, str], str] = {}
    with tempfile.TemporaryDirectory(prefix="cvc5-rare-") as raw_tmp:
        temporary = Path(raw_tmp)
        for name, (expected_count, expected_sha) in FILES.items():
            data = obtain(name, args.source_dir, temporary)
            actual_sha = sha256(data)
            if actual_sha != expected_sha:
                raise SystemExit(
                    f"{name}: SHA-256 {actual_sha}, expected {expected_sha}"
                )
            extracted = [
                match.group(1)
                for line in data.decode("utf-8").splitlines()
                if (match := RULE.match(line))
            ]
            if len(extracted) != expected_count:
                raise SystemExit(
                    f"{name}: {len(extracted)} rules, expected "
                    f"{expected_count}"
                )
            names.extend(extracted)
            source_aggregates.update(
                source_list_aggregates(data.decode("utf-8"))
            )
            print(f"{name}: sha256={actual_sha} rules={len(extracted)}")

    if len(names) != 169 or len(set(names)) != 169:
        raise SystemExit(
            f"combined inventory is not 169 unique names: "
            f"total={len(names)} unique={len(set(names))}"
        )
    rendered = "\n".join(sorted(names)) + "\n"
    actual_names_sha = sha256(rendered.encode("utf-8"))
    if actual_names_sha != NAMES_SHA256:
        raise SystemExit(
            f"name SHA-256 {actual_names_sha}, expected {NAMES_SHA256}"
        )
    fixture = args.fixture.read_text(encoding="utf-8")
    if fixture != rendered:
        raise SystemExit(f"fixture differs: {args.fixture}")

    aggregate_rendered = "".join(
        f"{rule}\t{formal}\t{aggregate}\n"
        for (rule, formal), aggregate in sorted(source_aggregates.items())
    )
    aggregate_sha = sha256(aggregate_rendered.encode("utf-8"))
    aggregate_counts = Counter(source_aggregates.values())
    if len(source_aggregates) != 70 or aggregate_sha != LIST_AGGREGATE_SHA256:
        raise SystemExit(
            "source list-aggregate metadata drifted: "
            f"count={len(source_aggregates)} sha256={aggregate_sha}"
        )

    unittest = (
        args.hol_root / "src" / "HolSmt" / "Unittest.sml"
    ).read_text(encoding="utf-8")
    try:
        embedded = unittest.split(HOL_FIXTURE_START, 1)[1].split(
            HOL_FIXTURE_END, 1
        )[0]
    except IndexError as error:
        raise SystemExit(
            "embedded HOL closure fixture markers not found"
        ) from error
    proof_source = (
        args.hol_root / "src" / "HolSmt" / "CPC_Proof.sml"
    ).read_text(encoding="utf-8")
    hol_aggregates = hol_list_aggregates(proof_source)
    expected_hol = {
        key: aggregate
        for key, aggregate in source_aggregates.items()
        if key not in FIRST_TRANCHE_LIST_FORMALS
    }
    if hol_aggregates != expected_hol:
        missing = sorted(expected_hol.keys() - hol_aggregates.keys())
        extra = sorted(hol_aggregates.keys() - expected_hol.keys())
        wrong = sorted(
            key
            for key in expected_hol.keys() & hol_aggregates.keys()
            if expected_hol[key] != hol_aggregates[key]
        )
        raise SystemExit(
            "HOL source aggregate metadata differs: "
            f"missing={missing} extra={extra} wrong={wrong}"
        )
    unsupported_table = proof_source.split(
        "val cvc134_rare_unsupported_source_reasons", 1
    )[1].split("val cvc134_rare_source_recipes", 1)[0]
    unsupported_names = set(re.findall(r'\("([^"]+)"\s*,', unsupported_table))
    list_recipe_names = {rule for rule, _ in hol_aggregates}
    unsupported_list_names = list_recipe_names & unsupported_names
    proved_list_names = list_recipe_names - unsupported_names
    if len(list_recipe_names) != 41 or len(proved_list_names) != 28 or len(
        unsupported_list_names
    ) != 13:
        raise SystemExit(
            "HOL aggregate recipe disposition counts drifted: "
            f"total={len(list_recipe_names)} proved={len(proved_list_names)} "
            f"unsupported={len(unsupported_list_names)}"
        )
    try:
        public_list_block = unittest.split(HOL_PUBLIC_LIST_START, 1)[1].split(
            HOL_PUBLIC_LIST_END, 1
        )[0]
    except IndexError as error:
        raise SystemExit(
            "public native-aggregate coverage markers not found"
        ) from error
    public_list_names = set(re.findall(r'"([^"]+)"', public_list_block))
    sweep = unittest.split(
        "fun cpc_rare_inventory_part2_source_sweep () =", 1
    )[1].split(
        "fun cpc_rare_inventory_part2_public_replay_success () =", 1
    )[0]
    if public_list_names != proved_list_names or len(public_list_names) != 28:
        raise SystemExit(
            "public native-aggregate name set differs from source-derived "
            "proved recipes: missing="
            f"{sorted(proved_list_names - public_list_names)} "
            f"extra={sorted(public_list_names - proved_list_names)}"
        )
    if (
        "rare_source_native_cpc_for_test" not in sweep
        or "parse_cpc_rare_source_string proof" not in sweep
        or "List.length (!native_aggregate_names) = 28" not in sweep
    ):
        raise SystemExit(
            "public native-aggregate parse/replay/count assertions are missing"
        )

    embedded_names = re.findall(r'"([^"]+)"', embedded)
    embedded_rendered = "\n".join(embedded_names) + "\n"
    if embedded_rendered != fixture:
        raise SystemExit(
            "embedded Unittest closure fixture differs from "
            "authoritative fixture"
        )

    print(f"commit={COMMIT}")
    print(f"combined: total=169 unique=169 sha256={actual_names_sha}")
    print(f"fixture: MATCH {args.fixture}")
    print(
        "list aggregates: "
        f"count=70 str.++={aggregate_counts['str.++']} "
        f"re.++={aggregate_counts['re.++']} "
        f"re.union={aggregate_counts['re.union']} "
        f"re.inter={aggregate_counts['re.inter']} sha256={aggregate_sha}"
    )
    print(
        "HOL declarative aggregate metadata: MATCH "
        "(63 formals; 28 proved and 13 unsupported recipes)"
    )
    print(
        "public native-aggregate coverage: MATCH "
        "(all 28 proved list-bearing recipes; CPC parse+replay asserted)"
    )
    print("embedded Unittest fixture: MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
