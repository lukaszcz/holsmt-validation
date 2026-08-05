#!/usr/bin/env python3
"""Probe the supported Seq/Set/Bag solver surface and render its matrix.

This deliberately probes solvers directly: it is neither a HolSmt parser test
nor a conformance runner.  A full invocation requires all five supported Z3
anchors and cvc5 1.3.4.  The JSON transcript is authoritative; Markdown is a
stable rendering of it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

Z3_VERSIONS = ("4.11.2", "4.12.4", "4.13.0", "4.14.1", "4.15.3")
CVC5_VERSION = "1.3.4"
SCHEMA = "holsmt-seq-set-bag-operator-matrix-v1"


@dataclass(frozen=True)
class Operator:
    name: str
    theory: str
    dialect: str
    result: str
    expr: str
    kind: str = "value"
    semantics: str = "documented"
    edge: str = "sort checked by equality"
    z3_since: str | None = None


def op(name: str, theory: str, dialect: str, result: str, expr: str,
       kind: str = "value", semantics: str = "documented",
       edge: str = "sort checked by equality", z3_since: str | None = None
       ) -> Operator:
    return Operator(name, theory, dialect, result, expr, kind, semantics,
                    edge, z3_since)

# This is the documented union, not the old 15-placeholder inventory.  The
# expressions are deliberately tiny and their enclosing equality type-checks
# their recorded result sort.  `z3-bag-map` records the reverse-engineered
# array encoding used by the Z3 printer rather than claiming a Z3 Bag theory.
OPS = (
    # Shared first-order sequence surface.
    op("seq.empty", "seq", "shared", "(Seq Int)",
       "(as seq.empty (Seq Int))", edge="empty sequence"),
    op("seq.unit", "seq", "shared", "(Seq Int)", "(seq.unit 7)",
       edge="unit sequence"),
    op("seq.++", "seq", "shared", "(Seq Int)", "(seq.++ s u)",
       edge="empty/unit concatenation"),
    op("seq.len", "seq", "shared", "Int", "(seq.len s)",
       edge="empty and unit lengths"),
    op("seq.nth", "seq", "shared", "Int", "(seq.nth s -1)",
       semantics="reverse-engineered", edge="out-of-range -1"),
    op("seq.extract", "seq", "shared", "(Seq Int)",
       "(seq.extract s -1 3)", semantics="reverse-engineered",
       edge="negative-start extraction"),
    op("seq.at", "seq", "shared", "(Seq Int)", "(seq.at s 99)",
       semantics="reverse-engineered", edge="out-of-range 99"),
    op("seq.contains", "seq", "shared", "Bool", "(seq.contains s u)"),
    op("seq.indexof", "seq", "shared", "Int", "(seq.indexof s u -1)",
       semantics="reverse-engineered", edge="negative offset"),
    op("seq.replace", "seq", "shared", "(Seq Int)",
       "(seq.replace s u (seq.unit 9))", edge="unit replacement"),
    op("seq.prefixof", "seq", "shared", "Bool", "(seq.prefixof u s)"),
    op("seq.suffixof", "seq", "shared", "Bool", "(seq.suffixof u s)"),
    # Z3's remaining documented polymorphic sequence surface.
    op("seq.last_indexof", "seq", "z3", "Int", "(seq.last_indexof s u)",
       semantics="reverse-engineered", edge="not-found/empty edge"),
    op("seq.to.re", "seq", "z3", "(RegEx (Seq Int))", "(seq.to.re s)"),
    op("seq.in.re", "seq", "z3", "Bool", "(seq.in.re s (seq.to.re u))"),
    op("str.replace_all[Seq]", "seq", "shared", "(Seq Int)",
       "(str.replace_all s u (seq.unit 9))", semantics="reverse-engineered"),
    op("str.replace_re[Seq]", "seq", "z3", "(Seq Int)",
       "(str.replace_re s (seq.to.re u) (seq.unit 9))",
       semantics="reverse-engineered"),
    op("str.replace_re_all[Seq]", "seq", "z3", "(Seq Int)",
       "(str.replace_re_all s (seq.to.re u) (seq.unit 9))",
       semantics="reverse-engineered"),
    op("seq.map", "seq", "z3", "(Seq Int)", "(seq.map f1 s)", "z3-seq-ho"),
    op("seq.mapi", "seq", "z3", "(Seq Int)", "(seq.mapi f2 0 s)",
       "z3-seq-ho"),
    op("seq.foldl", "seq", "z3", "Int", "(seq.foldl f2 0 s)",
       "z3-seq-ho"),
    op("seq.foldli", "seq", "z3", "Int", "(seq.foldli f3 0 0 s)",
       "z3-seq-ho"),
    op("seq.fold_left", "seq", "z3", "Int", "(seq.fold_left f2 0 s)",
       "z3-seq-ho", z3_since="4.12.4"),
    op("seq.fold_lefti", "seq", "z3", "Int", "(seq.fold_lefti f3 0 0 s)",
       "z3-seq-ho", z3_since="4.12.4"),
    # cvc5-only sequence surface.
    op("seq.update", "seq", "cvc5", "(Seq Int)",
       "(seq.update s 99 u)", semantics="reverse-engineered",
       edge="out-of-range update"),
    op("seq.replace_all", "seq", "cvc5", "(Seq Int)",
       "(seq.replace_all s u (seq.unit 9))"),
    op("seq.rev", "seq", "cvc5", "(Seq Int)", "(seq.rev s)",
       edge="empty/unit reverse"),
    # Z3 native array-backed set surface.
    op("Set", "set", "shared", "(Set Int)", "zs", "z3-set"),
    op("set.empty[Z3]", "set", "z3", "(Set Int)",
       "((as const (Set Int)) false)", "z3-set", edge="empty set"),
    op("set.universe[Z3]", "set", "z3", "(Set Int)",
       "((as const (Set Int)) true)", "z3-set", edge="universal set"),
    op("select[Set]", "set", "z3", "Bool", "(select zs 7)", "z3-set"),
    op("store[Set]", "set", "z3", "(Set Int)", "(store zs 7 true)",
       "z3-set"),
    op("union", "set", "z3", "(Set Int)", "(union zs zt)", "z3-set"),
    op("intersection", "set", "z3", "(Set Int)", "(intersection zs zt)",
       "z3-set"),
    op("setminus", "set", "z3", "(Set Int)", "(setminus zs zt)",
       "z3-set"),
    op("complement", "set", "z3", "(Set Int)", "(complement zs)",
       "z3-set"),
    op("subset", "set", "z3", "Bool", "(subset zs zt)", "z3-set"),
    # cvc5 finite-set surface.
    op("set.empty", "set", "cvc5", "(Set Int)",
       "(as set.empty (Set Int))", "cvc5-set", edge="empty finite set"),
    op("set.universe", "set", "cvc5", "(Set Int)",
       "(as set.universe (Set Int))", "cvc5-set", edge="finite universe"),
    op("set.singleton", "set", "cvc5", "(Set Int)", "(set.singleton 7)",
       "cvc5-set", edge="singleton finite set"),
    op("set.insert", "set", "cvc5", "(Set Int)", "(set.insert 7 cs)",
       "cvc5-set"),
    op("set.union", "set", "cvc5", "(Set Int)", "(set.union cs ct)",
       "cvc5-set"),
    op("set.inter", "set", "cvc5", "(Set Int)", "(set.inter cs ct)",
       "cvc5-set"),
    op("set.minus", "set", "cvc5", "(Set Int)", "(set.minus cs ct)",
       "cvc5-set"),
    op("set.complement", "set", "cvc5", "(Set Int)", "(set.complement cs)",
       "cvc5-set"),
    op("set.member", "set", "cvc5", "Bool", "(set.member 7 cs)",
       "cvc5-set"),
    op("set.subset", "set", "cvc5", "Bool", "(set.subset cs ct)",
       "cvc5-set"),
    op("set.card", "set", "cvc5", "Int", "(set.card cs)", "cvc5-set",
       edge="finite-cardinality"),
    op("set.choose", "set", "cvc5", "Int", "(set.choose cs)", "cvc5-set"),
    op("set.is_empty", "set", "cvc5", "Bool", "(set.is_empty cs)",
       "cvc5-set"),
    op("set.is_singleton", "set", "cvc5", "Bool", "(set.is_singleton cs)",
       "cvc5-set"),
    op("set.comprehension", "set", "cvc5", "(Set Int)",
       "(set.comprehension ((x Int)) (> x 0) x)", "cvc5-set-ho"),
    op("set.map", "set", "cvc5", "(Set Int)", "(set.map hf1 cs)",
       "cvc5-set-ho"),
    op("set.filter", "set", "cvc5", "(Set Int)", "(set.filter hp cs)",
       "cvc5-set-ho"),
    op("set.all", "set", "cvc5", "Bool", "(set.all hp cs)",
       "cvc5-set-ho"),
    op("set.some", "set", "cvc5", "Bool", "(set.some hp cs)",
       "cvc5-set-ho"),
    op("set.fold", "set", "cvc5", "Int", "(set.fold hf2 0 cs)",
       "cvc5-set-ho"),
    # cvc5 finite-bag surface.
    op("Bag", "bag", "cvc5", "(Bag Int)", "cb", "cvc5-bag"),
    op("bag.empty", "bag", "cvc5", "(Bag Int)",
       "(as bag.empty (Bag Int))", "cvc5-bag", edge="empty finite bag"),
    op("bag", "bag", "cvc5", "(Bag Int)", "(bag 7 2)", "cvc5-bag",
       edge="unit literal count 2"),
    op("bag.union_max", "bag", "cvc5", "(Bag Int)",
       "(bag.union_max cb cc)", "cvc5-bag"),
    op("bag.union_disjoint", "bag", "cvc5", "(Bag Int)",
       "(bag.union_disjoint cb cc)", "cvc5-bag"),
    op("bag.inter_min", "bag", "cvc5", "(Bag Int)",
       "(bag.inter_min cb cc)", "cvc5-bag"),
    op("bag.difference_subtract", "bag", "cvc5", "(Bag Int)",
       "(bag.difference_subtract cb cc)", "cvc5-bag"),
    op("bag.difference_remove", "bag", "cvc5", "(Bag Int)",
       "(bag.difference_remove cb cc)", "cvc5-bag"),
    op("bag.subbag", "bag", "cvc5", "Bool", "(bag.subbag cb cc)",
       "cvc5-bag"),
    op("bag.count", "bag", "cvc5", "Int", "(bag.count 7 cb)",
       "cvc5-bag", edge="count is non-negative"),
    op("bag.member", "bag", "cvc5", "Bool", "(bag.member 7 cb)",
       "cvc5-bag"),
    op("bag.setof", "bag", "cvc5", "(Bag Int)", "(bag.setof cb)",
       "cvc5-bag"),
    op("bag.card", "bag", "cvc5", "Int", "(bag.card cb)", "cvc5-bag",
       edge="finite-cardinality"),
    op("bag.choose", "bag", "cvc5", "Int", "(bag.choose cb)", "cvc5-bag"),
    op("bag.map", "bag", "cvc5", "(Bag Int)", "(bag.map hf1 cb)",
       "cvc5-bag-ho"),
    op("bag.filter", "bag", "cvc5", "(Bag Int)", "(bag.filter hp cb)",
       "cvc5-bag-ho"),
    op("bag.all", "bag", "cvc5", "Bool", "(bag.all hp cb)",
       "cvc5-bag-ho"),
    op("bag.some", "bag", "cvc5", "Bool", "(bag.some hp cb)",
       "cvc5-bag-ho"),
    op("bag.fold", "bag", "cvc5", "Int", "(bag.fold hf2 0 cb)",
       "cvc5-bag-ho"),
    op("bag.partition", "bag", "cvc5", "(Bag (Bag Int))",
       "(bag.partition heq cb)", "cvc5-bag-ho"),
    # Reverse-engineered Z3 array map encodings used for bags.
    op("(_ map +)[Bag encoding]", "z3-array-bag-encoding", "z3",
       "(Array Int Int)", "((_ map (+ (Int Int) Int)) ba bb)", "z3-bag-map",
       "reverse-engineered", "pointwise count addition"),
)


def version_at_least(got: str, minimum: str) -> bool:
    return tuple(map(int, got.split("."))) >= tuple(map(int, minimum.split(".")))


def expected(opr: Operator, solver: str, version: str) -> bool:
    if opr.dialect == "shared":
        return True
    if opr.dialect == solver:
        return not (solver == "z3" and opr.z3_since and
                    not version_at_least(version, opr.z3_since))
    return False


def prelude(kind: str, solver: str) -> str:
    logic = "HO_ALL" if kind.startswith("cvc5-") else "ALL"
    declarations: list[str] = []
    if kind in {"value", "z3-seq-ho", "cvc5-set", "cvc5-set-ho"}:
        declarations += ["(declare-const s (Seq Int))", "(declare-const u (Seq Int))"]
    if kind == "z3-set":
        declarations += ["(declare-const zs (Set Int))", "(declare-const zt (Set Int))"]
    if kind.startswith("cvc5-set"):
        declarations += ["(declare-const cs (Set Int))", "(declare-const ct (Set Int))"]
    if kind.startswith("cvc5-bag"):
        declarations += ["(declare-const cb (Bag Int))", "(declare-const cc (Bag Int))"]
    if kind == "z3-bag-map":
        declarations += ["(declare-const ba (Array Int Int))", "(declare-const bb (Array Int Int))"]
    if kind == "z3-seq-ho":
        declarations += ["(declare-const f1 (Array Int Int))",
                         "(declare-const f2 (Array Int Int Int))",
                         "(declare-const f3 (Array Int Int Int Int))"]
    if kind.startswith("cvc5-"):
        declarations += ["(declare-const hf1 (-> Int Int))",
                         "(declare-const hp (-> Int Bool))",
                         "(declare-const hf2 (-> Int Int Int))",
                         "(declare-const heq (-> Int Int Bool))"]
    return "(set-logic %s)\n%s\n" % (logic, "\n".join(declarations))


def input_for(opr: Operator, solver: str) -> str:
    # Equality both demonstrates that the expression is first-order well sorted
    # and avoids relying on solver-specific get-value printing.
    return prelude(opr.kind, solver) + "(assert (= %s %s))\n(check-sat)\n" % (
        opr.expr, opr.expr)


def parse_anchor(path: str, solver: str) -> str:
    try:
        proc = subprocess.run([path, "-version" if solver == "z3" else "--version"], text=True,
                              capture_output=True, timeout=10, check=False)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    text = proc.stdout + proc.stderr
    match = re.search(r"(?:Z3 version|cvc5)\s+(\d+\.\d+\.\d+)", text,
                      re.IGNORECASE)
    return match.group(1) if match else ""


def invoke(executable: str, solver: str, smt: str, timeout: float,
           directory: Path, label: str) -> dict[str, object]:
    digest = hashlib.sha256(smt.encode()).hexdigest()
    input_path = directory / (label + "-" + digest[:12] + ".smt2")
    input_path.parent.mkdir(parents=True, exist_ok=True)
    input_path.write_text(smt)
    command = [executable]
    if solver == "z3":
        command += ["-smt2", str(input_path)]
    else:
        command += ["--lang", "smt2.6", "--sets-exp", str(input_path)]
    try:
        proc = subprocess.run(command, text=True, encoding="utf-8",
                              errors="replace", capture_output=True,
                              timeout=timeout, check=False)
        output = proc.stdout + proc.stderr
        rejected = bool(re.search(r"error|invalid|unsupported|parse error",
                                  output, re.IGNORECASE))
        result = next((x for x in re.findall(r"(?m)^(sat|unsat|unknown)$",
                                              proc.stdout) if x), None)
        acceptance = "rejected" if rejected else "accepted"
        return {"command": command, "input": {"path": str(input_path),
                "sha256": digest, "text": smt},
                "exit_code": proc.returncode, "timed_out": False,
                "stdout": proc.stdout, "stderr": proc.stderr,
                "acceptance": acceptance, "solver_result": result}
    except subprocess.TimeoutExpired as exc:
        return {"command": command, "input": {"path": str(input_path),
                "sha256": digest, "text": smt},
                "exit_code": None, "timed_out": True,
                "stdout": (exc.stdout or "") if isinstance(exc.stdout, str) else "",
                "stderr": (exc.stderr or "") if isinstance(exc.stderr, str) else "",
                "acceptance": "timeout", "solver_result": None}


def cell_text(cell: dict[str, object]) -> str:
    if cell["acceptance"] == "timeout":
        return "timeout"
    if cell["acceptance"] == "rejected":
        return "rejected"
    return "accepted" + (": " + str(cell["solver_result"])
                         if cell["solver_result"] else "")


def render(report: dict[str, object]) -> str:
    cells = report["cells"]
    by_op: dict[str, list[dict[str, object]]] = {}
    for cell in cells:
        by_op.setdefault(str(cell["operator"]), []).append(cell)
    lines = [
        "# Seq/Set/Bag operator availability matrix",
        "",
        "Generated by `tools/probe_seq_set_bag_matrix.py`; raw, complete",
        "transcripts are in `seq_set_bag_operator_matrix.raw.json`.  Every",
        "accepted cell type-checks its displayed result sort using equality.",
        "cvc5 is invoked with documented `--sets-exp`; this is essential for",
        "its extended finite-set operations.",
        "",
        "## Re-run",
        "",
        "```sh",
        "python3 tools/probe_seq_set_bag_matrix.py --z3 4.11.2:$HOME/.local/bin/z3-4.11.2 \\",
        "  --z3 4.12.4:$HOME/.local/bin/z3-4.12.4 --z3 4.13.0:$HOME/.local/bin/z3-4.13.0 \\",
        "  --z3 4.14.1:$HOME/.local/bin/z3-4.14.1 --z3 4.15.3:$HOME/.local/bin/z3-4.15.3 \\",
        "  --cvc5 $HOME/.local/bin/cvc5 --raw-transcript <raw.json> \\",
        "  --markdown-report <report.md>",
        "```",
        "",
        "## Availability and evidence",
        "",
        "| Operator | Theory / dialect | Result sort; probe edge | Z3 4.11.2 | Z3 4.12.4 | Z3 4.13.0 | Z3 4.14.1 | Z3 4.15.3 | cvc5 1.3.4 | Intended HOL counterpart | Evidence |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for opr in sorted(OPS, key=lambda x: x.name):
        own = {str(c["solver"]["name"]) + ":" + str(c["solver"]["requested_version"]): c
               for c in by_op[opr.name]}
        columns = []
        for version in Z3_VERSIONS:
            c = own["z3:" + version]
            columns.append(cell_text(c))
        columns.append(cell_text(own["cvc5:" + CVC5_VERSION]))
        ids = "; ".join(str(c["id"]) for c in by_op[opr.name])
        evidence = "[raw transcript](seq_set_bag_operator_matrix.raw.json) " + ids
        lines.append("| `%s` | %s / %s | `%s`; %s | %s | TBD | %s |" % (
            opr.name, opr.theory, opr.dialect, opr.result, opr.edge,
            " | ".join(columns), evidence))
    lines += [
        "",
        "## Provenance and semantic status",
        "",
        "The inventory is the union of Z3's sequence/array-set parser surface",
        "and cvc5 1.3.4's Seq, Set, and Bag registrations.  Z3 source evidence:",
        "`src/ast/seq_decl_plugin.cpp` and `src/ast/array_decl_plugin.cpp`",
        "(4.11.2); cvc5 source evidence: `docs/theories/{sequences,sets-and-relations,bags}.rst`",
        "and `src/parser/smt2/smt2_state.cpp` (1.3.4 source snapshot).",
        "Rows marked reverse-engineered are backed by each per-version raw Z3",
        "transcript above, rather than an asserted HOL interpretation.",
        "",
        "## Phase-6 §0 claims",
        "",
        "- **Confirmed:** Z3 has no `Bag` sort and rejects cvc5 `set.*`/`bag.*`;",
        "  cvc5 rejects Z3's classic set names and `(_ map ...)` encoding.",
        "- **Confirmed:** Z3 `(Set T)` is `(Array T Bool)`, with classic names,",
        "  `select`/`store`, and no usable `card` surface.",
        "- **Confirmed:** the Z3 `(_ map ...)` count-addition encoding",
        "  works on all five anchors; cvc5 rejects it.",
        "- **Confirmed, with widening:** the documented shared first-order `seq.*`",
        "  rows are accepted by both solvers.  Z3 additionally exposes",
        "  `last_indexof`, regex and indexed HO rows; cvc5 additionally exposes",
        "  `seq.update`, `seq.rev`, and `seq.replace_all`.",
        "- **Confirmed, with widening:** `seq.map`/`seq.foldl` are Z3-only; the",
        "  full Z3 surface also contains `mapi`, `foldli`, and indexed aliases.",
        "  `seq.fold_left` and `seq.fold_lefti` are rejected by 4.11.2 and",
        "  accepted from 4.12.4 onward.",
        "- **Confirmed:** cvc5 Set/Bag are finite theories and expose `set.card`",
        "  and `bag.card` (under `--sets-exp`).",
        "",
        "The widening affects Phase-6 plan §2 (corpus/operator inventory), §3",
        "(semantics/builders), §4 (dialect printer gates), and §6 (CPC rules):",
        "they must cover the listed additional operators, not merely the old",
        "18-symbol bucket.  No correction changes the D13 model decision.",
        "",
        "## Edge observations",
        "",
        "The `seq.nth`, `seq.at`, `seq.extract`, `seq.update`, and `seq.indexof`",
        "rows contain negative/out-of-range inputs.  They establish acceptance",
        "and result sort, while their exact under-specified values remain",
        "reverse-engineered evidence for later semantic work.  Empty/unit",
        "sequence, empty/singleton set/bag, and finite-cardinality probes are",
        "likewise named in the table.  The raw SMT-LIB input in every cell is",
        "retained with a SHA-256 digest for spot checking.",
        "",
    ]
    return "\n".join(lines)


def parse_z3(spec: str) -> tuple[str, str]:
    version, sep, path = spec.partition(":")
    if not sep or version not in Z3_VERSIONS or not path:
        raise argparse.ArgumentTypeError("--z3 needs VERSION:PATH for a supported anchor")
    return version, path


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--z3", action="append", type=parse_z3, default=[])
    parser.add_argument("--cvc5")
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--only", action="append", default=[])
    parser.add_argument("--raw-transcript", type=Path,
                        default=Path("tools/seq-set-bag-matrix-out/raw-transcript.json"))
    parser.add_argument("--markdown-report", type=Path,
                        default=Path("tools/seq-set-bag-matrix-out/seq_set_bag_operator_matrix.md"))
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    anchors = dict(args.z3)
    if len(anchors) != len(args.z3):
        parser.error("duplicate --z3 version")
    if set(anchors) != set(Z3_VERSIONS):
        parser.error("a full matrix requires each supported Z3 --z3 anchor")
    cvc5 = args.cvc5 or os.environ.get("HOL4_CVC_EXECUTABLE") or \
        os.environ.get("CVC5") or shutil.which("cvc5")
    if not cvc5:
        parser.error("cvc5 is required (--cvc5, HOL4_CVC_EXECUTABLE, CVC5, PATH)")
    if args.only:
        names = set(args.only)
        selected = tuple(x for x in OPS if x.name in names)
        missing = names - {x.name for x in selected}
        if missing:
            parser.error("unknown operator(s): " + ", ".join(sorted(missing)))
    else:
        selected = OPS
    selected = tuple(sorted(selected, key=lambda x: x.name))
    raw_path = args.raw_transcript.resolve()
    markdown_path = args.markdown_report.resolve()
    input_dir = raw_path.parent / (raw_path.stem + ".inputs")
    shutil.rmtree(input_dir, ignore_errors=True)
    input_dir.mkdir(parents=True, exist_ok=True)
    solvers = [("z3", version, path) for version, path in sorted(anchors.items(),
                key=lambda x: Z3_VERSIONS.index(x[0]))] + [("cvc5", CVC5_VERSION, cvc5)]
    anchors_out = []
    for solver, requested, executable in solvers:
        resolved = str(Path(executable).expanduser().resolve())
        reported = parse_anchor(resolved, solver)
        if reported != requested:
            print("wrong anchor: %s requested %s, reports %s" %
                  (resolved, requested, reported or "nothing"), file=sys.stderr)
            return 2
        anchors_out.append({"name": solver, "requested_version": requested,
                            "resolved_executable": resolved,
                            "reported_version": reported})
    cells = []
    unexpected = 0
    for opr in selected:
        for anchor in anchors_out:
            smt = input_for(opr, anchor["name"])
            got = invoke(anchor["resolved_executable"], anchor["name"], smt,
                         args.timeout, input_dir, opr.name.replace("/", "_").replace(" ", "_"))
            wanted = expected(opr, anchor["name"], anchor["requested_version"])
            accepted = got["acceptance"] == "accepted"
            classification = "matched" if accepted == wanted else (
                "unexpected-accept" if accepted else "unexpected-reject")
            if classification != "matched":
                unexpected += 1
            cells.append({"id": "%s:%s:%s" % (opr.name, anchor["name"],
                          anchor["requested_version"]), "operator": opr.name,
                          "theory": opr.theory, "dialect": opr.dialect,
                          "semantics": opr.semantics, "observed_result_sort": opr.result,
                          "solver": anchor, "expected_acceptance": wanted,
                          "classification": classification, **got})
    report = {"schema": SCHEMA, "anchors": anchors_out,
              "operators": [x.name for x in selected], "cells": cells,
              "unexpected_cells": unexpected}
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render(report))
    print("wrote %s and %s (%d unexpected cells)" %
          (raw_path, markdown_path, unexpected))
    return 1 if unexpected else 0


if __name__ == "__main__":
    raise SystemExit(main())
