#!/usr/bin/env python3
"""Capture cvc5 CPC certificates and freeze a replay vocabulary.

The recorder is deliberately independent of the HOL parser: it records raw
CPC evidence first, including syntax that a future parser version does not yet
support.  A cvc5 bump therefore produces a precise inventory instead of
silently widening the trusted/replay surface.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
from typing import Any


SCHEMA = "holsmt-cvc5-cpc-corpus-v1"
GRANULARITIES = (
    "macro", "rewrite", "theory-rewrite", "dsl-rewrite",
    "dsl-rewrite-strict",
)


def cvc5_version(executable: str) -> str:
    result = subprocess.run(
        [executable, "--version"], text=True, capture_output=True, check=False
    )
    first = result.stdout.splitlines()[0] if result.stdout else ""
    match = re.match(r"cvc5\s+([^\s]+)", first)
    return match.group(1) if match else "<undiscoverable>"


def balanced_forms(text: str) -> list[str]:
    """Return top-level parenthesized forms, ignoring comments and strings."""
    forms: list[str] = []
    start: int | None = None
    depth = 0
    quoted = False
    escaped = False
    comment = False
    for index, char in enumerate(text):
        if comment:
            if char == "\n":
                comment = False
            continue
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
            continue
        if char == ";":
            comment = True
        elif char == '"':
            quoted = True
        elif char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")" and depth:
            depth -= 1
            if depth == 0 and start is not None:
                forms.append(text[start : index + 1])
                start = None
    return forms


def proof_forms(output: str) -> list[str]:
    """CPC output may repeat a proof after get-proof; keep all raw copies."""
    return [form for form in balanced_forms(output) if "(step " in form or
            "(assume " in form]


def inventory(proof: str) -> dict[str, Any]:
    rules = collections.Counter(re.findall(r"\(step\s+\S+(?:\s+[^:()]+)?\s+:rule\s+(\S+)", proof))
    # `:args` may contain nested terms.  Its outer shape is useful evidence
    # even when detailed semantic replay has not landed yet.
    args = collections.Counter(
        "empty" if value.strip() == "" else "nonempty"
        for value in re.findall(r":args\s*\(([^()]*)\)", proof)
    )
    defines = re.findall(r"\(define\s+([^\s()]+)", proof)
    declarations = re.findall(r"\((declare-(?:const|fun|sort|datatype|datatypes))\b", proof)
    steps = re.findall(r"\(step\s+([^\s()]+)", proof)
    return {
        "rules": dict(sorted(rules.items())),
        "arg_shapes": dict(sorted(args.items())),
        "define_markers": sorted(set(defines)),
        "skolem_markers": sorted({name for name in defines if name.startswith("@")}),
        "declarations": dict(sorted(collections.Counter(declarations).items())),
        "step_count": len(steps),
        "optional_conclusions": len(re.findall(r"\(step\s+\S+\s+:rule\b", proof)),
        "trust_steps": len(re.findall(r":rule\s+trust\b", proof)),
    }


def run_one(executable: str, granularity: str, path: pathlib.Path,
            timeout: int, raw_dir: pathlib.Path) -> dict[str, Any]:
    command = [
        executable, "--produce-proofs", "--dump-proofs",
        "--proof-format-mode=cpc", f"--proof-granularity={granularity}",
        "--lang", "smt2", str(path),
    ]
    try:
        result = subprocess.run(command, text=True, capture_output=True,
                                timeout=timeout, check=False)
        timed_out = False
    except subprocess.TimeoutExpired as error:
        result = error
        timed_out = True
    # Corpus files frequently share a basename across theory directories.
    # Include a stable content identity so captures have the same name in
    # every checkout while distinct queries never overwrite one another.
    digest = hashlib.sha256(path.read_bytes()).hexdigest()[:12]
    stem = f"{path.stem}-{granularity}-{digest}"
    raw_dir.mkdir(parents=True, exist_ok=True)
    stdout = result.stdout if not timed_out else (result.stdout or "")
    stderr = result.stderr if not timed_out else (result.stderr or "")
    (raw_dir / f"{stem}.stdout").write_text(stdout, encoding="utf-8")
    (raw_dir / f"{stem}.stderr").write_text(stderr, encoding="utf-8")
    (raw_dir / f"{stem}.smt2").write_text(path.read_text(encoding="utf-8"),
                                             encoding="utf-8")
    proofs = proof_forms(stdout)
    if proofs:
        (raw_dir / f"{stem}.cpc").write_text(proofs[0], encoding="utf-8")
    first_result = next((line for line in stdout.splitlines()
                         if line in {"sat", "unsat", "unknown"}), "<none>")
    return {
        "input": str(path),
        "raw_stem": stem,
        "granularity": granularity,
        "command": command,
        "exit_code": None if timed_out else result.returncode,
        "timed_out": timed_out,
        "solver_result": first_result,
        "proof_copies": len(proofs),
        "inventory": inventory(proofs[0]) if proofs else None,
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# cvc5 CPC corpus baseline",
        "",
        f"- Schema: `{report['schema']}`",
        f"- cvc5: `{report['cvc5']['version']}` (`{report['cvc5']['executable']}`)",
        f"- Captures: {len(report['entries'])}",
        "",
        "| Granularity | Queries | Proof steps | `trust` steps | Unique rules |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for granularity, data in report["granularities"].items():
        lines.append(
            f"| `{granularity}` | {data['entries']} | {data['proof_steps']} | "
            f"{data['trust_steps']} | {len(data['rules'])} |"
        )
    lines.extend(["", "## Frozen rule inventory", ""])
    for granularity, data in report["granularities"].items():
        vocabulary = ", ".join(
            f"`{rule}` ({count})" for rule, count in data["rules"].items()
        ) or "_no CPC proofs captured_"
        lines.extend([f"### `{granularity}`", "", vocabulary, ""])
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=pathlib.Path)
    parser.add_argument("--cvc5", default=os.environ.get("HOL4_CVC_EXECUTABLE", "cvc5"))
    parser.add_argument("--out", type=pathlib.Path,
                        default=pathlib.Path("tools/cpc-corpus-out"))
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--granularity", action="append", choices=GRANULARITIES)
    args = parser.parse_args(argv)
    granularities = args.granularity or list(GRANULARITIES)
    out = args.out.resolve()
    raw = out / "raw"
    entries = [run_one(args.cvc5, granularity, path, args.timeout, raw)
               for granularity in granularities for path in args.inputs]
    by_granularity: dict[str, dict[str, Any]] = {}
    for granularity in granularities:
        selected = [entry for entry in entries if entry["granularity"] == granularity]
        rules: collections.Counter[str] = collections.Counter()
        proof_size = 0
        trust_steps = 0
        for entry in selected:
            data = entry["inventory"]
            if data:
                rules.update(data["rules"])
                proof_size += data["step_count"]
                trust_steps += data["trust_steps"]
        by_granularity[granularity] = {
            "entries": len(selected), "proof_steps": proof_size,
            "trust_steps": trust_steps,
            "rules": dict(sorted(rules.items())),
        }
    report = {
        "schema": SCHEMA,
        "cvc5": {"executable": args.cvc5, "version": cvc5_version(args.cvc5)},
        "granularities": by_granularity,
        "entries": entries,
    }
    out.mkdir(parents=True, exist_ok=True)
    (out / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                                       encoding="utf-8")
    (out / "report.md").write_text(render_markdown(report), encoding="utf-8")
    print(f"wrote {len(entries)} CPC captures to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
