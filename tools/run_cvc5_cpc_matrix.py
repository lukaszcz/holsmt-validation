#!/usr/bin/env python3
"""Run checked cvc5 CPC replay over SMT-LIB queries and write a matrix report."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
from typing import Any


SCHEMA = "holsmt-cvc5-cpc-replay-matrix-v1"
TOOLS_DIR = pathlib.Path(__file__).resolve().parent
PASS = "CVC_CPC_TAC_PASS"
RESOURCE_GATED = "CVC_CPC_TAC_RESOURCE_GATED"


def default_driver() -> pathlib.Path:
    holsmt_root = os.environ.get("HOLSMT_ROOT")
    if holsmt_root:
        return pathlib.Path(holsmt_root) / "src/HolSmt/holsmt-cvc-cpc-tac"
    return pathlib.Path("holsmt-cvc-cpc-tac")


def logic_of(path: pathlib.Path) -> str:
    match = re.search(r"^\s*\(set-logic\s+([^\s)]+)\s*\)",
                      path.read_text(encoding="utf-8"), re.MULTILINE)
    if not match:
        raise ValueError(f"{path}: missing set-logic")
    return match.group(1)


def run_one(driver: pathlib.Path, cvc5: str, path: pathlib.Path,
            timeout: int) -> dict[str, Any]:
    try:
        logic = logic_of(path)
    except (OSError, ValueError) as error:
        return {"input": str(path), "logic": None,
                "status": "CVC_CPC_TAC_FAIL", "exit_code": None,
                "timed_out": False, "result": None,
                "cvc5_version": None, "stdout": "", "stderr": str(error)}
    environment = os.environ.copy()
    environment["HOL4_CVC_EXECUTABLE"] = cvc5
    try:
        result = subprocess.run([str(driver), str(path), logic], text=True,
                                capture_output=True, timeout=timeout,
                                check=False, env=environment)
        timed_out = False
    except subprocess.TimeoutExpired as error:
        result = error
        timed_out = True
    def output_text(value: str | bytes | None) -> str:
        if isinstance(value, bytes):
            return value.decode("utf-8", errors="replace")
        return value or ""

    stdout = output_text(result.stdout)
    stderr = output_text(result.stderr)
    fields = dict(line.split("=", 1) for line in stdout.splitlines()
                  if "=" in line)
    status = next((line for line in stdout.splitlines()
                   if line.startswith("CVC_CPC_TAC_")), "<no-status>")
    return {
        "input": str(path), "logic": logic, "status": status,
        "exit_code": None if timed_out else result.returncode,
        "timed_out": timed_out, "result": fields.get("result"),
        "cvc5_version": fields.get("cvc5_version"),
        "stdout": stdout, "stderr": stderr,
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="*", type=pathlib.Path)
    parser.add_argument("--input-list", type=pathlib.Path,
                        help="newline-separated SMT-LIB query paths")
    parser.add_argument("--driver", type=pathlib.Path,
                        default=default_driver())
    parser.add_argument("--cvc5", default=os.environ.get(
                        "HOL4_CVC_EXECUTABLE", "cvc5"))
    parser.add_argument("--out", type=pathlib.Path,
                        default=TOOLS_DIR / "cvc5-cpc-matrix.json")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args(argv)
    inputs = list(args.inputs)
    if args.input_list:
        try:
            manifest = args.input_list.read_text(encoding="utf-8")
        except OSError as error:
            parser.error(f"could not read input list {args.input_list}: {error}")
        inputs.extend(pathlib.Path(line.strip()) for line in manifest.splitlines()
                      if line.strip() and not line.lstrip().startswith("#"))
    if not inputs:
        parser.error("supply one or more inputs or --input-list")
    driver = args.driver.resolve()
    if not driver.is_file():
        parser.error(f"checked CPC driver not found: {driver}")
    entries = []
    for number, path in enumerate(inputs, start=1):
        print(f"replaying {number}/{len(inputs)}: {path}", flush=True)
        entries.append(run_one(driver, args.cvc5, path.resolve(), args.timeout))
    report = {"schema": SCHEMA, "driver": str(driver),
              "cvc5": args.cvc5, "entries": entries}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
    passed = [entry for entry in entries if entry["status"] == PASS]
    gated = [entry for entry in entries if entry["status"] == RESOURCE_GATED]
    accepted = {PASS, RESOURCE_GATED}
    failed = [entry for entry in entries if entry["status"] not in accepted]
    print(
        "checked CPC replay: "
        f"{len(passed)}/{len(entries)} passed; "
        f"{len(gated)} resource-gated"
    )
    if failed:
        print("failures: " + ", ".join(entry["input"] for entry in failed),
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
