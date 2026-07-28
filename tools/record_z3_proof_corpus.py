#!/usr/bin/env python3
"""Record Z3 proof outputs and raw proof-rule histograms for HolSmt."""

from __future__ import annotations

import argparse
import collections
import fnmatch
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from typing import Iterable


SCHEMA = "holsmt-z3-proof-corpus-v1"
MATRIX_SCHEMA = "holsmt-z3-proof-corpus-matrix-v1"
STRING_CORPUS_SCHEMA = "holsmt-z3-string-proof-corpus-v1"
FP_CORPUS_SCHEMA = "holsmt-z3-fp-proof-corpus-v1"
RULE_CONTEXT_LIMIT = 3
VALIDATION_ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT_DIR = VALIDATION_ROOT / "tools" / "proof-corpus" / "out"
DEFAULT_SUPPORTED_VERSION_MANIFEST = (
    pathlib.Path(__file__).resolve().parent
    / "proof-corpus"
    / "supported_versions"
    / "manifest.json"
)
DEFAULT_COMPLETE_CORPUS_MANIFEST = (
    pathlib.Path(__file__).resolve().parent / "proof-corpus" / "complete" / "manifest.json"
)
DEFAULT_STRING_CORPUS_MANIFEST = (
    pathlib.Path(__file__).resolve().parent
    / "proof-corpus"
    / "strings"
    / "manifest.json"
)
DEFAULT_FP_CORPUS_MANIFEST = (
    pathlib.Path(__file__).resolve().parent
    / "proof-corpus"
    / "floatingpoint"
    / "manifest.json"
)
SUPPORTED_Z3_VERSIONS = ("4.12.4", "4.13.0")
COMPLETE_CORPUS_Z3_VERSIONS = (
    "4.11.2",
    "4.12.4",
    "4.13.0",
    "4.14.1",
    "4.15.3",
)
STRING_DRAFTING_PROBES = (
    "concat",
    "length",
    "regex-membership",
    "substr",
    "contains",
    "str-lt",
    "str-to-int",
    "re-loop",
    "re-comp",
    "replace-all-ground",
    "literal-escapes",
)
FP_REWRITE_OPERATORS = (
    "fp.abs",
    "fp.add",
    "fp.div",
    "fp.eq",
    "fp.fma",
    "fp.geq",
    "fp.gt",
    "fp.isInfinite",
    "fp.isNaN",
    "fp.isNegative",
    "fp.isNormal",
    "fp.isPositive",
    "fp.isSubnormal",
    "fp.isZero",
    "fp.leq",
    "fp.lt",
    "fp.max",
    "fp.min",
    "fp.mul",
    "fp.neg",
    "fp.rem",
    "fp.roundToIntegral",
    "fp.sqrt",
    "fp.sub",
    "fp.to_real",
    "fp.to_sbv",
    "fp.to_ubv",
    "to_fp",
    "to_fp_unsigned",
)
STRING_OFFICIAL_OPERATORS = (
    "str.++",
    "str.len",
    "str.<",
    "str.<=",
    "str.at",
    "str.substr",
    "str.prefixof",
    "str.suffixof",
    "str.contains",
    "str.indexof",
    "str.replace",
    "str.replace_all",
    "str.is_digit",
    "str.to_code",
    "str.from_code",
    "str.to_int",
    "str.from_int",
    "str.to_re",
    "str.in_re",
    "str.replace_re",
    "str.replace_re_all",
    "re.none",
    "re.all",
    "re.allchar",
    "re.++",
    "re.union",
    "re.inter",
    "re.diff",
    "re.*",
    "re.+",
    "re.opt",
    "re.range",
    "re.^",
    "re.loop",
)
HO_PROOF_CORPUS_CASE_IDS = (
    "proof-rule:ho:lambda-equality",
    "proof-rule:ho:beta-instance",
    "proof-rule:ho:lambda-extensionality",
    "proof-rule:ho:lambda-under-quantifier",
    "proof-rule:ho:eta-partial-application",
    "proof-rule:ho:map-valued-ite",
)
SUCCESS_STATUSES = {"pass", "passed", "success", "succeeded"}

REPLAY_SUPPORTED_RULES = {
    "and-elim",
    "asserted",
    "commutativity",
    "def-axiom",
    "elim-unused",
    "hypothesis",
    "iff-false",
    "iff-true",
    "intro-def",
    "lemma",
    "monotonicity",
    "mp",
    "mp-eq",
    "mp_eq",
    "mp~",
    "nnf-neg",
    "nnf-pos",
    "not-or-elim",
    "quant-inst",
    "quant-intro",
    "refl",
    "rewrite",
    "sk",
    "skolem",
    "symm",
    "th-lemma-arith",
    "th-lemma-array",
    "th-lemma-basic",
    "th-lemma-bv",
    "th-lemma-char",
    "th-lemma-character",
    "th-lemma-characters",
    "th-lemma-datatype",
    "th-lemma-datatypes",
    "th-lemma-dt",
    "th-lemma-floating-point",
    "th-lemma-fp",
    "th-lemma-fpa",
    "th-lemma-nia",
    "th-lemma-nla",
    "th-lemma-nonlinear",
    "th-lemma-nonlinear-arith",
    "th-lemma-nra",
    "th-lemma-re",
    "th-lemma-regex",
    "th-lemma-regexp",
    "th-lemma-seq",
    "th-lemma-sequence",
    "th-lemma-sequences",
    "th-lemma-str",
    "th-lemma-string",
    "th-lemma-strings",
    "trans",
    "trans-star",
    "trans*",
    "true-axiom",
    "unit-resolution",
}

PARSE_ONLY_RULES = {
    # Z3 wraps binder-local proof terms in proof-bind.  The current parser
    # treats legacy occurrences as transparent, but C1's higher-order corpus
    # shows that the bound proof structure is semantically relevant.  Keep
    # this known for recording and explicitly out of REPLAY_SUPPORTED_RULES
    # until the structured parser/replay work lands.
    "proof-bind",
}

KNOWN_RULES = REPLAY_SUPPORTED_RULES | PARSE_ONLY_RULES

RULE_PREMISE_KIND = {
    "and-elim": "one",
    "asserted": "zero",
    "commutativity": "zero",
    "def-axiom": "zero",
    "elim-unused": "zero",
    "hypothesis": "zero",
    "iff-false": "one",
    "iff-true": "one",
    "intro-def": "zero",
    "lemma": "one",
    "monotonicity": "list",
    "mp": "two",
    "mp-eq": "two",
    "mp_eq": "two",
    "mp~": "two",
    "nnf-neg": "list",
    "nnf-pos": "list",
    "not-or-elim": "one",
    "proof-bind": "one",
    "quant-inst": "zero",
    "quant-intro": "one",
    "refl": "zero",
    "rewrite": "zero",
    "sk": "zero",
    "skolem": "zero",
    "symm": "one",
    "th-lemma-arith": "list",
    "th-lemma-array": "list",
    "th-lemma-basic": "list",
    "th-lemma-bv": "list",
    "th-lemma-char": "list",
    "th-lemma-character": "list",
    "th-lemma-characters": "list",
    "th-lemma-datatype": "list",
    "th-lemma-datatypes": "list",
    "th-lemma-dt": "list",
    "th-lemma-floating-point": "list",
    "th-lemma-fp": "list",
    "th-lemma-fpa": "list",
    "th-lemma-nia": "list",
    "th-lemma-nla": "list",
    "th-lemma-nonlinear": "list",
    "th-lemma-nonlinear-arith": "list",
    "th-lemma-nra": "list",
    "th-lemma-re": "list",
    "th-lemma-regex": "list",
    "th-lemma-regexp": "list",
    "th-lemma-seq": "list",
    "th-lemma-sequence": "list",
    "th-lemma-sequences": "list",
    "th-lemma-str": "list",
    "th-lemma-string": "list",
    "th-lemma-strings": "list",
    "trans": "two",
    "trans-star": "list",
    "trans*": "list",
    "true-axiom": "zero",
    "unit-resolution": "list",
}
SOLVER_RESULTS = {"sat", "unsat", "unknown"}
NONLINEAR_ARITH_LOGICS = {
    "ANIA",
    "ANIRA",
    "AUFNIA",
    "AUFNIRA",
    "NIA",
    "NIRA",
    "NRA",
    "QF_ANIA",
    "QF_ANRA",
    "QF_AUFNIA",
    "QF_AUFNIRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_SNIA",
    "QF_UFNIA",
    "QF_UFNIRA",
    "QF_UFNRA",
    "UFNIA",
    "UFNIRA",
    "UFNRA",
}


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class Atom:
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class ListNode:
    items: list["Node"]
    start: int
    end: int


Node = Atom | ListNode


class SexpParseError(Exception):
    def __init__(self, message: str, offset: int):
        super().__init__(message)
        self.message = message
        self.offset = offset


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as infile:
        for chunk in iter(lambda: infile.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def json_dump(path: pathlib.Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as outfile:
        json.dump(value, outfile, indent=2, sort_keys=True)
        outfile.write("\n")


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def tokenize(text: str) -> Iterable[Token]:
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "(":
            yield Token("lparen", c, i, i + 1)
            i += 1
        elif c == ")":
            yield Token("rparen", c, i, i + 1)
            i += 1
        elif c == '"':
            start = i
            i += 1
            while i < n:
                if text[i] == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        i += 2
                    else:
                        i += 1
                        break
                else:
                    i += 1
            else:
                raise SexpParseError("unterminated SMT-LIB string", start)
            yield Token("atom", text[start:i], start, i)
        elif c == "|":
            start = i
            i += 1
            value = []
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    value.append(text[i + 1])
                    i += 2
                elif text[i] == "|":
                    i += 1
                    break
                else:
                    value.append(text[i])
                    i += 1
            else:
                raise SexpParseError("unterminated quoted symbol", start)
            yield Token("atom", "".join(value), start, i)
        else:
            start = i
            while i < n and not text[i].isspace() and text[i] not in "();":
                i += 1
            yield Token("atom", text[start:i], start, i)


def parse_sexps(text: str) -> list[Node]:
    """Parse SMT-LIB without using the Python call stack.

    fpa2bv proofs contain deeply nested SAT terms; the old recursive parser
    overflowed on the required Float16 and tiny-format arithmetic probes.
    """

    nodes: list[Node] = []
    stack: list[tuple[int, list[Node]]] = []
    for token in tokenize(text):
        if token.kind == "lparen":
            stack.append((token.start, []))
        elif token.kind == "atom":
            node: Node = Atom(token.text, token.start, token.end)
            if stack:
                stack[-1][1].append(node)
            else:
                nodes.append(node)
        else:
            if not stack:
                raise SexpParseError("unexpected ')'", token.start)
            start, items = stack.pop()
            node = ListNode(items, start, token.end)
            if stack:
                stack[-1][1].append(node)
            else:
                nodes.append(node)
    if stack:
        raise SexpParseError("missing ')'", stack[-1][0])
    return nodes


def line_col(text: str, offset: int) -> dict[str, int]:
    prefix = text[:offset]
    line = prefix.count("\n") + 1
    last_newline = prefix.rfind("\n")
    column = offset + 1 if last_newline < 0 else offset - last_newline
    return {"line": line, "column": column}


def context_for(text: str, start: int, end: int, radius: int = 96) -> str:
    left = max(0, start - radius)
    right = min(len(text), end + radius)
    context = text[left:right].replace("\n", "\\n")
    if left > 0:
        context = "..." + context
    if right < len(text):
        context += "..."
    return context


def atom_text(node: Node) -> str | None:
    return node.text if isinstance(node, Atom) else None


def normalize_rule_head(head: Node) -> str | None:
    if isinstance(head, Atom):
        return head.text
    if not isinstance(head, ListNode) or len(head.items) < 2:
        return None
    first = atom_text(head.items[0])
    base = atom_text(head.items[1])
    if first != "_" or base is None:
        return None
    if base == "th-lemma":
        theory = atom_text(head.items[2]) if len(head.items) >= 3 else None
        return f"th-lemma-{theory}" if theory else "th-lemma"
    if base == "rewrite":
        return "rewrite"
    return base


def th_lemma_metadata_from_head(head: Node) -> dict[str, object] | None:
    if not isinstance(head, ListNode) or len(head.items) < 3:
        return None
    first = atom_text(head.items[0])
    base = atom_text(head.items[1])
    theory = atom_text(head.items[2])
    if first != "_" or base != "th-lemma" or theory is None:
        return None
    index_atoms = [atom_text(item) for item in head.items[3:]]
    indices = [item for item in index_atoms if item is not None]
    subkind = indices[0] if indices else None
    return {
        "theory": theory,
        "subkind": subkind,
        "indices": indices,
        "key": f"{theory}:{subkind}" if subkind is not None else f"{theory}:<none>",
        "rule": f"th-lemma-{theory}",
    }


def parsed_dag_summary(nodes: list[Node]) -> dict[str, object]:
    summary = {
        "top_level_sexp_count": len(nodes),
        "list_node_count": 0,
        "atom_count": 0,
        "let_binding_count": 0,
        "proof_wrapper_count": 0,
        "max_list_depth": 0,
    }

    work = [(node, 1) for node in reversed(nodes)]
    while work:
        node, depth = work.pop()
        if isinstance(node, Atom):
            summary["atom_count"] += 1
            continue
        summary["list_node_count"] += 1
        summary["max_list_depth"] = max(int(summary["max_list_depth"]), depth)
        head = atom_text(node.items[0]) if node.items else None
        if head == "proof":
            summary["proof_wrapper_count"] += 1
        if head == "let" and len(node.items) >= 2 and isinstance(node.items[1], ListNode):
            summary["let_binding_count"] += sum(
                1
                for item in node.items[1].items
                if isinstance(item, ListNode) and len(item.items) == 2
            )
        work.extend((child, depth + 1) for child in reversed(node.items))
    return summary


def malformed_item(
    text: str,
    message: str,
    start: int,
    end: int,
) -> dict[str, object]:
    loc = line_col(text, start)
    return {
        "message": message,
        "line": loc["line"],
        "column": loc["column"],
        "context": context_for(text, start, end),
    }


def extract_ho_shape_metadata(
    proof_text: str,
    nodes: list[Node],
) -> dict[str, object]:
    lambda_count = 0
    lambda_def_count = 0
    proof_bind_count = 0
    lambda_contexts: list[dict[str, object]] = []
    lambda_defs: list[dict[str, object]] = []
    proof_binds: list[dict[str, object]] = []
    named_lambdas: set[str] = set()
    bind_consumers: collections.Counter[str] = collections.Counter()

    def location(node: ListNode, *, exact: bool = False) -> dict[str, object]:
        loc = line_col(proof_text, node.start)
        result: dict[str, object] = {
            "line": loc["line"],
            "column": loc["column"],
            "context": context_for(proof_text, node.start, node.end),
        }
        if exact:
            result["shape"] = proof_text[node.start:node.end]
        return result

    def contains_lambda_def_annotation(node: ListNode) -> bool:
        qid = False
        lambda_def = False
        work: list[Node] = [node]
        while work and not (qid and lambda_def):
            value = work.pop()
            if isinstance(value, Atom):
                qid = qid or value.text == ":qid"
                lambda_def = lambda_def or value.text == ":lambda-def"
            else:
                work.extend(value.items)
        return qid and lambda_def

    work = [(node, None) for node in reversed(nodes)]
    while work:
        node, parent_head = work.pop()
        if isinstance(node, Atom):
            if re.fullmatch(r"z3name![0-9]+", node.text):
                named_lambdas.add(node.text)
            continue
        head = normalize_rule_head(node.items[0]) if node.items else None
        if head == "lambda":
            lambda_count += 1
            if len(lambda_contexts) < RULE_CONTEXT_LIMIT:
                lambda_contexts.append(location(node))
        if head == "!" and contains_lambda_def_annotation(node):
            lambda_def_count += 1
            lambda_defs.append(location(node, exact=True))
        if head == "proof-bind":
            proof_bind_count += 1
            proof_binds.append(location(node, exact=True))
            bind_consumers[parent_head or "<root>"] += 1
        work.extend((child, head) for child in reversed(node.items))

    return {
        "lambda_term_count": lambda_count,
        "lambda_contexts": lambda_contexts,
        "named_lambda_symbols": sorted(named_lambdas),
        "lambda_def_axiom_count": lambda_def_count,
        "lambda_def_axioms": lambda_defs,
        "proof_bind_count": proof_bind_count,
        "proof_binds": proof_binds,
        "proof_bind_consumers": dict(sorted(bind_consumers.items())),
    }


def extract_string_shape_metadata(nodes: list[Node]) -> dict[str, object]:
    """Collect exact Z3 string-internal spellings and printed literals."""

    symbol_counts: collections.Counter[str] = collections.Counter()
    indexed_counts: collections.Counter[str] = collections.Counter()
    prefix_counts: collections.Counter[str] = collections.Counter()
    char_literal_counts: collections.Counter[str] = collections.Counter()
    char_bit_indices: set[str] = set()
    string_literal_counts: collections.Counter[str] = collections.Counter()

    tracked_atoms = {
        "Char",
        "aut.accept",
        "char.is_digit",
        "seq.digit",
        "seq.digit2int",
        "seq.eq",
        "seq.nth_i",
        "seq.stoi",
        "seq.tail",
        "seq.unit",
    }

    work = list(reversed(nodes))
    while work:
        node = work.pop()
        if isinstance(node, Atom):
            if node.text in tracked_atoms:
                symbol_counts[node.text] += 1
            if node.text.startswith('"'):
                string_literal_counts[node.text] += 1
            continue

        if len(node.items) >= 2:
            first = atom_text(node.items[0])
            base = atom_text(node.items[1])
            if first == "_" and base is not None:
                exact = "(" + " ".join(
                    child.text if isinstance(child, Atom) else "<list>"
                    for child in node.items
                ) + ")"
                if base == "Char" and len(node.items) == 3:
                    char_literal_counts[exact] += 1
                if (
                    base in {"aut.accept", "char.bit", "seq.eq", "seq.tail"}
                    or base.startswith("seq.prefix.")
                ):
                    indexed_counts[exact] += 1
                    if base not in tracked_atoms:
                        symbol_counts[base] += 1
                if base.startswith("seq.prefix."):
                    prefix_counts[base] += 1
                if base == "char.bit" and len(node.items) >= 4:
                    index = atom_text(node.items[-1])
                    if index is not None:
                        char_bit_indices.add(index)
        work.extend(reversed(node.items))

    return {
        "symbols": dict(sorted(symbol_counts.items())),
        "indexed_symbols": dict(sorted(indexed_counts.items())),
        "seq_prefix_symbols": dict(sorted(prefix_counts.items())),
        "char_literals": dict(sorted(char_literal_counts.items())),
        "char_bit_indices": sorted(char_bit_indices, key=version_sort_key),
        "string_literals": dict(sorted(string_literal_counts.items())),
    }


def extract_fp_shape_metadata(
    proof_text: str,
    nodes: list[Node],
) -> dict[str, object]:
    """Pin fpa2bv rewrite payloads without duplicating large formulas."""

    fp_variables = set(
        re.findall(
            r"\(declare-fun\s+([^\s()]+)\s+\(\)\s+"
            r"(?:Float(?:16|32|64|128)|\(_\s+FloatingPoint\s+"
            r"[0-9]+\s+[0-9]+\))\)",
            proof_text,
        )
    )
    bv_skolems = [
        {"name": name, "width": int(width)}
        for name, width in re.findall(
            r"\(declare-fun\s+(k![0-9]+)\s+\(\)\s+"
            r"\(_\s+BitVec\s+([0-9]+)\)\)",
            proof_text,
        )
    ]
    bool_skolems = re.findall(
        r"\(declare-fun\s+(k![0-9]+)\s+\(\)\s+Bool\)",
        proof_text,
    )
    operator_pattern = re.compile(
        r"\bfp\.(?:abs|add|div|eq|fma|geq|gt|isInfinite|isNaN|"
        r"isNegative|isNormal|isPositive|isSubnormal|isZero|leq|lt|"
        r"max|min|mul|neg|rem|roundToIntegral|sqrt|sub|to_real)\b|"
        r"\(_\s+(?:fp\.to_[us]bv|to_fp|to_fp_unsigned)\b"
    )
    special_pattern = re.compile(
        r"\(_\s+(?:NaN|[+-](?:oo|zero))\s+[0-9]+\s+[0-9]+\)"
    )
    triple_pattern = re.compile(
        r"\(fp\s+#b([01]+)\s+#b([01]+)\s+#b([01]+)\)"
    )
    bv_triple_pattern = re.compile(
        r"\(fp\s+\(_\s+bv[0-9]+\s+1\)\s+"
        r"\(_\s+bv[0-9]+\s+([0-9]+)\)\s+"
        r"\(_\s+bv[0-9]+\s+([0-9]+)\)\)"
    )

    bindings: dict[str, Node] = {}
    binding_work = list(reversed(nodes))
    while binding_work:
        binding_node = binding_work.pop()
        if isinstance(binding_node, Atom):
            continue
        binding_work.extend(reversed(binding_node.items))
        if (
            binding_node.items
            and atom_text(binding_node.items[0]) == "let"
            and len(binding_node.items) >= 2
            and isinstance(binding_node.items[1], ListNode)
        ):
            for binding in binding_node.items[1].items:
                if isinstance(binding, ListNode) and len(binding.items) == 2:
                    name = atom_text(binding.items[0])
                    if name is not None:
                        bindings[name] = binding.items[1]

    def related_text(formula: str) -> tuple[str, list[dict[str, object]]]:
        pieces = [formula]
        roots: list[dict[str, object]] = []
        pending = re.findall(r"[?$]x[0-9]+", formula)
        seen: set[str] = set()
        while pending and len(seen) < 256:
            name = pending.pop()
            if name in seen or name not in bindings:
                continue
            seen.add(name)
            value = bindings[name]
            raw = proof_text[value.start:value.end]
            pieces.append(raw)
            pending.extend(re.findall(r"[?$]x[0-9]+", raw))
            encoded = raw.encode("utf-8")
            roots.append(
                {
                    "name": name,
                    "start_offset": value.start,
                    "end_offset": value.end,
                    "formula_bytes": len(encoded),
                    "formula_sha256": sha256_bytes(encoded),
                }
            )
        return "\n".join(pieces), roots

    def expand_decomposition(node: Node, formula: str) -> str:
        """Expand the three shallow extract bindings in (= x (fp ...))."""

        if not isinstance(node, ListNode) or len(node.items) != 3:
            return formula
        rhs = node.items[2]
        if (
            atom_text(node.items[0]) != "="
            or not isinstance(rhs, ListNode)
            or len(rhs.items) != 4
            or atom_text(rhs.items[0]) != "fp"
        ):
            return formula

        def field_text(field: Node) -> str:
            if isinstance(field, Atom) and field.text in bindings:
                value = bindings[field.text]
                return proof_text[value.start:value.end]
            return proof_text[field.start:field.end]

        lhs = proof_text[node.items[1].start:node.items[1].end]
        fields = " ".join(field_text(field) for field in rhs.items[1:])
        return f"(= {lhs} (fp {fields}))"

    rewrites: list[dict[str, object]] = []
    decompositions: list[dict[str, object]] = []
    work = list(reversed(nodes))
    while work:
        node = work.pop()
        if isinstance(node, Atom):
            continue
        work.extend(reversed(node.items))
        if not node.items or normalize_rule_head(node.items[0]) != "rewrite":
            continue
        conclusion = node.items[-1]
        formula = proof_text[conclusion.start:conclusion.end]
        searchable, formula_roots = related_text(formula)
        operators = sorted(
            {
                match.group(0).replace("(_ ", "").strip()
                for match in operator_pattern.finditer(searchable)
            }
        )
        has_special = special_pattern.search(searchable) is not None
        has_fp_triple = (
            triple_pattern.search(searchable) is not None
            or bv_triple_pattern.search(searchable) is not None
        )
        has_skolem = re.search(r"\bk![0-9]+\b", searchable) is not None
        expanded = expand_decomposition(conclusion, formula)
        decomposition = re.search(
            r"\(=\s+([^\s()]+)\s+\(fp\s+"
            r"\(\(_\s+extract\s+[0-9]+\s+[0-9]+\)\s+(k![0-9]+)\)",
            expanded,
        )
        if decomposition is not None:
            category = "bit-decomposition"
        elif has_skolem and operators:
            category = "atom-conversion"
        elif has_special and has_fp_triple:
            category = "literal-normalization"
        elif operators and (
            any(
                re.search(
                    rf"(?<![A-Za-z0-9_!?$]){re.escape(name)}"
                    rf"(?![A-Za-z0-9_!?$])",
                    searchable,
                )
                is not None
                for name in fp_variables
            )
            or re.search(
                r"(?<![A-Za-z0-9_!?$])(?:x|y|z)"
                r"(?![A-Za-z0-9_!?$])",
                searchable,
            )
            is not None
        ):
            category = "symbolic-normalization"
        elif operators or has_fp_triple or has_special:
            category = "ground-evaluation"
        else:
            continue

        formats = {
            f"({len(exponent)},{len(significand) + 1})"
            for _, exponent, significand in triple_pattern.findall(searchable)
        }
        formats.update(
            f"({exponent},{int(significand) + 1})"
            for exponent, significand in bv_triple_pattern.findall(searchable)
        )
        formats.update(
            f"({eb},{sb})"
            for eb, sb in re.findall(
                r"\(_\s+(?:NaN|[+-](?:oo|zero))\s+"
                r"([0-9]+)\s+([0-9]+)\)",
                searchable,
            )
        )
        encoded = formula.encode("utf-8")
        item: dict[str, object] = {
            "category": category,
            "operators": operators,
            "formats": sorted(formats),
            "start_offset": conclusion.start,
            "end_offset": conclusion.end,
            "formula_bytes": len(encoded),
            "formula_sha256": sha256_bytes(encoded),
            "formula_roots": formula_roots,
        }
        if len(formula) <= 8192:
            item["formula"] = formula
        else:
            item["formula_prefix"] = formula[:4096]
            item["formula_suffix"] = formula[-4096:]
        rewrites.append(item)
        if category == "bit-decomposition":
            decomposition_item = {
                "variable": decomposition.group(1),
                "skolem": decomposition.group(2),
                **item,
            }
            if len(expanded) <= 8192:
                decomposition_item["expanded_formula"] = expanded
            decompositions.append(decomposition_item)

    return {
        "bv_skolems": bv_skolems,
        "bool_skolem_count": len(bool_skolems),
        "bool_skolems": bool_skolems[:64],
        "bool_skolems_truncated": len(bool_skolems) > 64,
        "bit_decompositions": decompositions,
        "rewrites": rewrites,
    }


def extract_rule_report(proof_text: str) -> dict[str, object]:
    histogram: collections.Counter[str] = collections.Counter()
    theory_lemma_histogram: collections.Counter[str] = collections.Counter()
    rule_contexts: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    theory_lemma_metadata: list[dict[str, object]] = []
    unknown_contexts: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    malformed: list[dict[str, object]] = []
    dag_summary: dict[str, object] = {
        "top_level_sexp_count": 0,
        "list_node_count": 0,
        "atom_count": 0,
        "let_binding_count": 0,
        "proof_wrapper_count": 0,
        "max_list_depth": 0,
        "proof_rule_application_count": 0,
        "distinct_rule_count": 0,
    }

    try:
        nodes = parse_sexps(proof_text)
    except SexpParseError as exc:
        malformed.append(
            malformed_item(
                proof_text,
                exc.message,
                exc.offset,
                min(len(proof_text), exc.offset + 1),
            )
        )
        return {
            "rule_histogram": {},
            "rule_contexts": {},
            "parsed_dag_summary": dag_summary,
            "theory_lemma_histogram": {},
            "theory_lemma_metadata": [],
            "ho_shape": {
                "lambda_term_count": 0,
                "lambda_contexts": [],
                "named_lambda_symbols": [],
                "lambda_def_axiom_count": 0,
                "lambda_def_axioms": [],
                "proof_bind_count": 0,
                "proof_binds": [],
                "proof_bind_consumers": {},
            },
            "string_shape": {
                "symbols": {},
                "indexed_symbols": {},
                "seq_prefix_symbols": {},
                "char_literals": {},
                "char_bit_indices": [],
                "string_literals": {},
            },
            "fp_shape": {
                "bv_skolems": [],
                "bool_skolem_count": 0,
                "bool_skolems": [],
                "bool_skolems_truncated": False,
                "bit_decompositions": [],
                "rewrites": [],
            },
            "unknown_rules": [],
            "malformed_fragments": malformed,
        }
    dag_summary = parsed_dag_summary(nodes)
    ho_shape = extract_ho_shape_metadata(proof_text, nodes)
    string_shape = extract_string_shape_metadata(nodes)
    fp_shape = extract_fp_shape_metadata(proof_text, nodes)

    def context_item(node: ListNode) -> dict[str, object]:
        loc = line_col(proof_text, node.start)
        return {
            "line": loc["line"],
            "column": loc["column"],
            "context": context_for(proof_text, node.start, node.end),
        }

    def record_rule_context(rule: str, node: ListNode) -> None:
        if len(rule_contexts[rule]) >= RULE_CONTEXT_LIMIT:
            return
        rule_contexts[rule].append(context_item(node))

    def record_unknown(rule: str, node: ListNode) -> None:
        if len(unknown_contexts[rule]) >= RULE_CONTEXT_LIMIT:
            return
        unknown_contexts[rule].append(context_item(node))

    def scan(initial: list[tuple[Node, bool]]) -> None:
        work = list(reversed(initial))
        while work:
            node, proof_expected = work.pop()
            if isinstance(node, Atom):
                continue
            if not node.items:
                if proof_expected:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            "empty proof fragment",
                            node.start,
                            node.end,
                        )
                    )
                continue

            head_name = normalize_rule_head(node.items[0])
            if head_name == "proof":
                work.extend(
                    (child, True) for child in reversed(node.items[1:])
                )
                continue
            if not proof_expected:
                work.extend(
                    (child, False) for child in reversed(node.items)
                )
                continue
            if head_name == "let":
                if len(node.items) < 3:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            "malformed proof let",
                            node.start,
                            node.end,
                        )
                    )
                    continue
                bindings = node.items[1]
                if isinstance(bindings, ListNode):
                    for binding in reversed(bindings.items):
                        if (
                            isinstance(binding, ListNode)
                            and len(binding.items) == 2
                        ):
                            bound_name = atom_text(binding.items[0])
                            if (
                                bound_name is not None
                                and bound_name.startswith("@x")
                            ):
                                work.append((binding.items[1], True))
                        else:
                            malformed.append(
                                malformed_item(
                                    proof_text,
                                    "malformed proof let binding",
                                    binding.start,
                                    binding.end,
                                )
                            )
                else:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            "proof let bindings are not a list",
                            bindings.start,
                            bindings.end,
                        )
                    )
                work.extend(
                    (body, True) for body in reversed(node.items[2:])
                )
                continue
            if head_name == "!":
                if len(node.items) >= 2:
                    work.append((node.items[1], True))
                else:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            "malformed annotated proof",
                            node.start,
                            node.end,
                        )
                    )
                continue
            if head_name is None:
                malformed.append(
                    malformed_item(
                        proof_text,
                        "proof rule head is not a symbol",
                        node.start,
                        node.end,
                    )
                )
                continue

            histogram[head_name] += 1
            record_rule_context(head_name, node)
            th_metadata = th_lemma_metadata_from_head(node.items[0])
            if th_metadata is not None:
                th_metadata = {
                    **th_metadata,
                    "line": line_col(proof_text, node.start)["line"],
                    "column": line_col(proof_text, node.start)["column"],
                    "context": context_for(
                        proof_text, node.start, node.end
                    ),
                }
                theory_lemma_metadata.append(th_metadata)
                theory_lemma_histogram[str(th_metadata["key"])] += 1
            if head_name not in KNOWN_RULES:
                record_unknown(head_name, node)

            premise_kind = RULE_PREMISE_KIND.get(head_name, "unknown")
            args = node.items[1:]
            premises: list[Node] = []
            if premise_kind == "one":
                if args:
                    premises = args[:1]
                else:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            f"proof rule '{head_name}' is missing its premise",
                            node.start,
                            node.end,
                        )
                    )
            elif premise_kind == "two":
                premises = args[:2]
                if len(args) < 2:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            f"proof rule '{head_name}' is missing a premise",
                            node.start,
                            node.end,
                        )
                    )
            elif premise_kind == "list":
                premises = args[:-1]
                if not args:
                    malformed.append(
                        malformed_item(
                            proof_text,
                            f"proof rule '{head_name}' is missing a conclusion",
                            node.start,
                            node.end,
                        )
                    )
            elif premise_kind != "zero":
                premises = args[:-1]
            work.extend((child, True) for child in reversed(premises))

    scan([(node, False) for node in nodes])
    if not histogram and len(nodes) == 1:
        scan([(nodes[0], True)])
    dag_summary["proof_rule_application_count"] = sum(histogram.values())
    dag_summary["distinct_rule_count"] = len(histogram)

    unknown_rules = [
        {
            "rule": rule,
            "count": histogram[rule],
            "contexts": contexts,
        }
        for rule, contexts in sorted(unknown_contexts.items())
    ]

    return {
        "rule_histogram": dict(sorted(histogram.items())),
        "rule_contexts": dict(sorted(rule_contexts.items())),
        "parsed_dag_summary": dag_summary,
        "theory_lemma_histogram": dict(sorted(theory_lemma_histogram.items())),
        "theory_lemma_metadata": theory_lemma_metadata,
        "ho_shape": ho_shape,
        "string_shape": string_shape,
        "fp_shape": fp_shape,
        "unknown_rules": unknown_rules,
        "malformed_fragments": malformed,
    }


def detect_solver_result(stdout: str) -> tuple[str, str]:
    lines = stdout.splitlines(keepends=True)
    offset = 0
    for line in lines:
        stripped = line.strip()
        if stripped in SOLVER_RESULTS:
            proof_text = stdout[offset + len(line) :]
            return stripped, proof_text
        offset += len(line)
    return "no-result", ""


def z3_version(z3_executable: str) -> str:
    try:
        completed = subprocess.run(
            [z3_executable, "-version"],
            check=False,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
        )
    except OSError as exc:
        return f"unavailable: {exc}"
    output = (completed.stdout or completed.stderr).strip()
    match = re.search(r"Z3 version\s+(\S+)", output)
    return match.group(1) if match else output


def version_sort_key(version: str) -> tuple[int, ...]:
    """Order Z3 version strings numerically, so e.g. "4.8.x" precedes
    "4.13.x" instead of sorting lexicographically. Versions with no numeric
    components (e.g. "<undiscoverable>") sort first."""
    return tuple(int(n) for n in re.findall(r"\d+", version))


def proof_options_for(version: str) -> list[str]:
    if version.startswith("4."):
        return ["proof=true", "pp.simplify_implies=false"]
    return ["PROOF_MODE=2"]


def command_line_for(z3_executable: str, version: str, extra_options: list[str], path: pathlib.Path) -> list[str]:
    return [z3_executable, *proof_options_for(version), *extra_options, "-smt2", str(path)]


def prepare_input(original: pathlib.Path, append_get_proof: bool) -> tuple[pathlib.Path, tempfile.TemporaryDirectory[str] | None, str | None]:
    if not append_get_proof:
        return original, None, None
    data = original.read_text(encoding="utf-8")
    tempdir = tempfile.TemporaryDirectory(prefix="holsmt-proof-corpus-")
    prepared = pathlib.Path(tempdir.name) / original.name
    suffix = ""
    if "(check-sat" not in data:
        suffix += "\n(check-sat)\n"
    if "(get-proof" not in data:
        suffix += "\n(get-proof)\n"
    if "(exit" not in data:
        suffix += "(exit)\n"
    prepared.write_text(data.rstrip() + "\n" + suffix, encoding="utf-8")
    return prepared, tempdir, sha256_bytes(prepared.read_bytes())


def declared_logic(text: str) -> str | None:
    match = re.search(r"\(\s*set-logic\s+([A-Za-z0-9_]+)\s*\)", text)
    return match.group(1) if match is not None else None


def has_symbolic_nonlinear_product(text: str) -> bool:
    symbols: set[str] = set()
    for match in re.finditer(r"\(\s*declare-(?:const|fun)\s+([^\s()]+)", text):
        symbols.add(match.group(1))
    if not symbols:
        return False
    for match in re.finditer(r"\(\s*\*\s+([^()]*)\)", text):
        operands = match.group(1).split()
        if sum(1 for operand in operands if operand in symbols) >= 2:
            return True
    return False


def inferred_rule_histogram(
    input_path: pathlib.Path,
    proof_report: dict[str, object],
) -> dict[str, int]:
    rule_histogram = proof_report.get("rule_histogram", {})
    if (
        not isinstance(rule_histogram, dict)
        or not isinstance(rule_histogram.get("th-lemma-arith"), int)
        or rule_histogram["th-lemma-arith"] <= 0
    ):
        return {}
    try:
        text = input_path.read_text(encoding="utf-8")
    except OSError:
        return {}
    logic = declared_logic(text)
    if logic in NONLINEAR_ARITH_LOGICS and has_symbolic_nonlinear_product(text):
        return {"th-lemma-nonlinear-arith": rule_histogram["th-lemma-arith"]}
    return {}


def record_one(
    input_path: pathlib.Path,
    out_dir: pathlib.Path,
    z3_executable: str,
    version: str,
    extra_options: list[str],
    append_get_proof: bool,
    timeout: int,
) -> dict[str, object]:
    input_path = input_path.resolve()
    input_hash = sha256_file(input_path)
    run_path, tempdir, effective_hash = prepare_input(input_path, append_get_proof)
    command = command_line_for(z3_executable, version, extra_options, run_path)
    stdout = ""
    stderr = ""
    timed_out = False
    exit_code: int | None = None
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
        stdout = completed.stdout
        stderr = completed.stderr
        exit_code = completed.returncode
    except OSError as exc:
        stderr = str(exc)
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
    finally:
        elapsed_seconds = time.monotonic() - started
        if tempdir is not None:
            tempdir.cleanup()

    solver_result, proof_text = detect_solver_result(stdout)
    stem = f"{input_path.stem}-{input_hash[:12]}"
    stdout_path = out_dir / "raw" / f"{stem}.stdout"
    stderr_path = out_dir / "raw" / f"{stem}.stderr"
    write_text(stdout_path, stdout)
    write_text(stderr_path, stderr)

    proof_path: str | None = None
    proof_hash: str | None = None
    proof_report = {
        "rule_histogram": {},
        "rule_contexts": {},
        "parsed_dag_summary": {
            "top_level_sexp_count": 0,
            "list_node_count": 0,
            "atom_count": 0,
            "let_binding_count": 0,
            "proof_wrapper_count": 0,
            "max_list_depth": 0,
            "proof_rule_application_count": 0,
            "distinct_rule_count": 0,
        },
        "theory_lemma_histogram": {},
        "theory_lemma_metadata": [],
        "ho_shape": {
            "lambda_term_count": 0,
            "lambda_contexts": [],
            "named_lambda_symbols": [],
            "lambda_def_axiom_count": 0,
            "lambda_def_axioms": [],
            "proof_bind_count": 0,
            "proof_binds": [],
            "proof_bind_consumers": {},
        },
        "string_shape": {
            "symbols": {},
            "indexed_symbols": {},
            "seq_prefix_symbols": {},
            "char_literals": {},
            "char_bit_indices": [],
            "string_literals": {},
        },
        "fp_shape": {
            "bv_skolems": [],
            "bool_skolem_count": 0,
            "bool_skolems": [],
            "bool_skolems_truncated": False,
            "bit_decompositions": [],
            "rewrites": [],
        },
        "unknown_rules": [],
        "malformed_fragments": [],
    }
    if proof_text.strip():
        proof_hash = sha256_bytes(proof_text.encode("utf-8"))
        raw_path = out_dir / "proofs" / f"{stem}.proof"
        write_text(raw_path, proof_text)
        proof_path = str(raw_path)
        proof_report = extract_rule_report(proof_text)
    inferred_rules = inferred_rule_histogram(input_path, proof_report)

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-entry",
        "input": {
            "path": str(input_path),
            "sha256": input_hash,
            "effective_sha256": effective_hash or input_hash,
            "append_get_proof": append_get_proof,
        },
        "z3": {
            "executable": z3_executable,
            "version": version,
            "command_line": command,
            "exit_code": exit_code,
            "timed_out": timed_out,
            "stdout_path": str(stdout_path),
            "stderr_path": str(stderr_path),
            "elapsed_seconds": round(elapsed_seconds, 6),
            "stdout_bytes": len(stdout.encode("utf-8")),
            "stderr_bytes": len(stderr.encode("utf-8")),
        },
        "solver": {
            "result": solver_result,
            "z3_failure": bool(timed_out or (exit_code not in (0, None))),
        },
        "proof": {
            "available": bool(proof_text.strip()),
            "raw_path": proof_path,
            "raw_sha256": proof_hash,
            "raw_bytes": len(proof_text.encode("utf-8")),
            **proof_report,
            "inferred_rule_histogram": inferred_rules,
        },
        "holsmt": {
            "proof_parse_status": "not-run",
            "proof_replay_status": "not-run",
            "replay_result": {
                "status": "not-run",
                "checked": False,
                "detail": "HolSmt replay is not executed by the raw Z3 proof recorder",
            },
            "failure": None,
        },
        "theorem": {
            "tag_summary": {
                "status": "not-run",
                "checked": False,
                "oracle_tags": [],
                "axiom_tags": [],
                "unexpected_tags": [],
                "has_oracles": False,
                "has_axioms": False,
            }
        },
    }


def build_summary(entries: Iterable[dict[str, object]]) -> dict[str, object]:
    entries = list(entries)
    aggregate: collections.Counter[str] = collections.Counter()
    inferred_aggregate: collections.Counter[str] = collections.Counter()
    theory_lemma_aggregate: collections.Counter[str] = collections.Counter()
    aggregate_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    inferred_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    theory_lemma_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    string_symbols_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    indexed_symbols_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    seq_prefixes_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    char_literals_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    char_bits_by_version: dict[str, set[str]] = collections.defaultdict(set)
    string_literals_by_version: dict[
        str, collections.Counter[str]
    ] = collections.defaultdict(collections.Counter)
    version_entries: collections.Counter[str] = collections.Counter()
    version_proofs: collections.Counter[str] = collections.Counter()
    unknown: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    malformed_count = 0
    for entry in entries:
        proof = entry["proof"]  # type: ignore[index]
        version = entry["z3"]["version"]  # type: ignore[index]
        version_entries[version] += 1
        if proof["available"]:  # type: ignore[index]
            version_proofs[version] += 1
        for rule, count in proof["rule_histogram"].items():  # type: ignore[index, union-attr]
            aggregate[rule] += count
            aggregate_by_version[version][rule] += count
        inferred = proof.get("inferred_rule_histogram", {})
        if isinstance(inferred, dict):
            for rule, count in inferred.items():
                inferred_aggregate[rule] += count
                inferred_by_version[version][rule] += count
        for key, count in proof.get("theory_lemma_histogram", {}).items():  # type: ignore[union-attr]
            theory_lemma_aggregate[key] += count
            theory_lemma_by_version[version][key] += count
        string_shape = proof.get("string_shape", {})
        if isinstance(string_shape, dict):
            for field, target in (
                ("symbols", string_symbols_by_version[version]),
                ("indexed_symbols", indexed_symbols_by_version[version]),
                ("seq_prefix_symbols", seq_prefixes_by_version[version]),
                ("char_literals", char_literals_by_version[version]),
                ("string_literals", string_literals_by_version[version]),
            ):
                values = string_shape.get(field, {})
                if isinstance(values, dict):
                    target.update(
                        {
                            key: count
                            for key, count in values.items()
                            if isinstance(key, str) and isinstance(count, int)
                        }
                    )
            bit_indices = string_shape.get("char_bit_indices", [])
            if isinstance(bit_indices, list):
                char_bits_by_version[version].update(
                    item for item in bit_indices if isinstance(item, str)
                )
        for item in proof["unknown_rules"]:  # type: ignore[index, union-attr]
            unknown[item["rule"]].append(  # type: ignore[index]
                {
                    "input": entry["input"]["path"],  # type: ignore[index]
                    "z3_version": version,
                    "count": item["count"],  # type: ignore[index]
                    "contexts": item["contexts"],  # type: ignore[index]
                }
            )
        malformed_count += len(proof["malformed_fragments"])  # type: ignore[arg-type, index]

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-summary",
        "entry_count": len(entries),
        "proof_count": sum(1 for entry in entries if entry["proof"]["available"]),  # type: ignore[index]
        "z3_versions": [
            {
                "version": version,
                "entry_count": version_entries[version],
                "proof_count": version_proofs[version],
            }
            for version in sorted(version_entries, key=version_sort_key)
        ],
        "discovered_rules": sorted(aggregate),
        "aggregate_rule_histogram": dict(sorted(aggregate.items())),
        "inferred_rules": sorted(inferred_aggregate),
        "aggregate_inferred_rule_histogram": dict(sorted(inferred_aggregate.items())),
        "theory_lemma_subkinds": sorted(theory_lemma_aggregate),
        "aggregate_theory_lemma_histogram": dict(sorted(theory_lemma_aggregate.items())),
        "rules_by_version": [
            {
                "z3_version": version,
                "rules": sorted(histogram),
                "rule_histogram": dict(sorted(histogram.items())),
                "inferred_rules": sorted(inferred_by_version.get(version, {})),
                "inferred_rule_histogram": dict(
                    sorted(inferred_by_version.get(version, {}).items())
                ),
                "theory_lemma_subkinds": sorted(theory_lemma_by_version.get(version, {})),
                "theory_lemma_histogram": dict(
                    sorted(theory_lemma_by_version.get(version, {}).items())
                ),
                **(
                    {
                        "string_internal_symbols": dict(
                            sorted(
                                string_symbols_by_version.get(
                                    version, {}
                                ).items()
                            )
                        ),
                        "indexed_string_internal_symbols": dict(
                            sorted(
                                indexed_symbols_by_version.get(
                                    version, {}
                                ).items()
                            )
                        ),
                        "seq_prefix_symbols": dict(
                            sorted(
                                seq_prefixes_by_version.get(version, {}).items()
                            )
                        ),
                        "char_literals": dict(
                            sorted(
                                char_literals_by_version.get(version, {}).items()
                            )
                        ),
                        "char_bit_indices": sorted(
                            char_bits_by_version.get(version, set()),
                            key=version_sort_key,
                        ),
                        "string_literals": dict(
                            sorted(
                                string_literals_by_version.get(
                                    version, {}
                                ).items()
                            )
                        ),
                    }
                    if (
                        string_symbols_by_version.get(version)
                        or indexed_symbols_by_version.get(version)
                        or seq_prefixes_by_version.get(version)
                        or char_literals_by_version.get(version)
                        or char_bits_by_version.get(version)
                        or string_literals_by_version.get(version)
                    )
                    else {}
                ),
            }
            for version, histogram in sorted(
                aggregate_by_version.items(),
                key=lambda item: version_sort_key(item[0]),
            )
        ],
        "unknown_rule_coverage": [
            {
                "rule": rule,
                "occurrences": sum(item["count"] for item in items),
                "inputs": items,
            }
            for rule, items in sorted(unknown.items())
        ],
        "proof_rule_support": {
            "replay_supported": sorted(REPLAY_SUPPORTED_RULES),
            "parse_only": sorted(PARSE_ONLY_RULES),
        },
        "malformed_fragment_count": malformed_count,
        "entries": [entry["input"]["path"] for entry in entries],  # type: ignore[index]
    }


def load_expected_rule_manifest(path: pathlib.Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def load_json(path: pathlib.Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def resolve_manifest_path(manifest_path: pathlib.Path, value: str) -> pathlib.Path:
    path = pathlib.Path(value)
    if path.is_absolute():
        return path
    root_path = VALIDATION_ROOT / path
    if root_path.exists():
        return root_path
    return manifest_path.parent / path


def validation_relative_path(path: pathlib.Path) -> pathlib.Path:
    """Normalize recorded absolute paths across validation worktrees."""

    parts = path.resolve().parts
    for index, part in enumerate(parts):
        if part == "tools":
            return pathlib.Path(*parts[index:])
    return path.resolve()


def complete_manifest_cases(manifest_path: pathlib.Path) -> list[dict[str, object]]:
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict):
        raise ValueError("complete corpus manifest root must be an object")
    cases = manifest.get("cases", [])
    if not isinstance(cases, list):
        raise ValueError("complete corpus manifest cases must be a list")
    result = []
    for item in cases:
        if isinstance(item, dict):
            result.append(item)
    return result


def complete_manifest_supported_versions(manifest_path: pathlib.Path) -> set[str]:
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict):
        raise ValueError("complete corpus manifest root must be an object")
    versions = manifest.get("supported_z3_versions", [])
    if not isinstance(versions, list) or not all(isinstance(item, str) for item in versions):
        raise ValueError("complete corpus manifest supported_z3_versions must be a string list")
    if sorted(versions) != sorted(COMPLETE_CORPUS_Z3_VERSIONS):
        raise ValueError(
            "complete corpus manifest supported_z3_versions mismatch: expected "
            + ", ".join(COMPLETE_CORPUS_Z3_VERSIONS)
        )
    return set(versions)


def inputs_from_complete_manifest(
    manifest_path: pathlib.Path,
    case_ids: list[str],
) -> list[pathlib.Path]:
    cases = complete_manifest_cases(manifest_path)
    selected_ids = set(case_ids)
    selected_paths: list[pathlib.Path] = []
    known_ids: set[str] = set()
    for item in cases:
        case_id = item.get("id")
        path_value = item.get("path")
        if isinstance(case_id, str):
            known_ids.add(case_id)
        if selected_ids and case_id not in selected_ids:
            continue
        if isinstance(path_value, str) and path_value:
            selected_paths.append(resolve_manifest_path(manifest_path, path_value))
    missing = sorted(selected_ids - known_ids)
    if missing:
        raise ValueError("complete corpus manifest has no case id(s): " + ", ".join(missing))
    if not selected_paths:
        raise ValueError("complete corpus manifest selection is empty")
    return selected_paths


def inputs_from_string_manifest(
    manifest_path: pathlib.Path,
) -> tuple[set[str], list[pathlib.Path]]:
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict):
        raise ValueError("string corpus manifest root must be an object")
    if manifest.get("schema") != STRING_CORPUS_SCHEMA:
        raise ValueError(
            f"string corpus manifest schema must be {STRING_CORPUS_SCHEMA}"
        )

    versions = manifest.get("supported_z3_versions", [])
    if not isinstance(versions, list) or not all(
        isinstance(item, str) for item in versions
    ):
        raise ValueError(
            "string corpus manifest supported_z3_versions must be a string list"
        )
    if sorted(versions) != sorted(COMPLETE_CORPUS_Z3_VERSIONS):
        raise ValueError(
            "string corpus manifest supported_z3_versions mismatch: expected "
            + ", ".join(COMPLETE_CORPUS_Z3_VERSIONS)
        )

    cases = manifest.get("cases", [])
    if not isinstance(cases, list) or not cases:
        raise ValueError(
            "string corpus manifest cases must be a non-empty list"
        )

    inputs: list[pathlib.Path] = []
    drafting_probes: set[str] = set()
    operators: set[str] = set()
    for index, item in enumerate(cases, 1):
        if not isinstance(item, dict):
            raise ValueError(f"string corpus case {index} must be an object")
        path_value = item.get("path")
        if not isinstance(path_value, str) or not path_value:
            raise ValueError(f"string corpus case {index} is missing path")
        path = resolve_manifest_path(manifest_path, path_value)
        if not path.is_file():
            raise ValueError(f"string corpus input does not exist: {path_value}")
        inputs.append(path)

        probe = item.get("drafting_probe")
        if isinstance(probe, str):
            drafting_probes.add(probe)
        case_operators = item.get("operators", [])
        if not isinstance(case_operators, list) or not all(
            isinstance(operator, str) for operator in case_operators
        ):
            raise ValueError(
                f"string corpus case {index} operators must be a string list"
            )
        operators.update(case_operators)

    missing_probes = sorted(set(STRING_DRAFTING_PROBES) - drafting_probes)
    extra_probes = sorted(drafting_probes - set(STRING_DRAFTING_PROBES))
    if missing_probes or extra_probes:
        raise ValueError(
            "string corpus drafting-probe coverage mismatch: missing "
            + (", ".join(missing_probes) or "<none>")
            + "; extra "
            + (", ".join(extra_probes) or "<none>")
        )

    missing_operators = sorted(set(STRING_OFFICIAL_OPERATORS) - operators)
    extra_operators = sorted(operators - set(STRING_OFFICIAL_OPERATORS))
    if missing_operators or extra_operators:
        raise ValueError(
            "string corpus operator coverage mismatch: missing "
            + (", ".join(missing_operators) or "<none>")
            + "; extra "
            + (", ".join(extra_operators) or "<none>")
        )
    return set(versions), inputs


def inputs_from_fp_manifest(
    manifest_path: pathlib.Path,
) -> tuple[set[str], list[pathlib.Path]]:
    manifest = load_json(manifest_path)
    if not isinstance(manifest, dict):
        raise ValueError("FP corpus manifest root must be an object")
    if manifest.get("schema") != FP_CORPUS_SCHEMA:
        raise ValueError(f"FP corpus manifest schema must be {FP_CORPUS_SCHEMA}")
    versions = manifest.get("supported_z3_versions", [])
    if not isinstance(versions, list) or not all(
        isinstance(item, str) for item in versions
    ):
        raise ValueError(
            "FP corpus manifest supported_z3_versions must be a string list"
        )
    if sorted(versions) != sorted(COMPLETE_CORPUS_Z3_VERSIONS):
        raise ValueError(
            "FP corpus manifest supported_z3_versions mismatch: expected "
            + ", ".join(COMPLETE_CORPUS_Z3_VERSIONS)
        )
    cases = manifest.get("cases", [])
    if not isinstance(cases, list) or not cases:
        raise ValueError("FP corpus manifest cases must be a non-empty list")
    inputs: list[pathlib.Path] = []
    operators: set[str] = set()
    classes: set[str] = set()
    for index, item in enumerate(cases, 1):
        if not isinstance(item, dict):
            raise ValueError(f"FP corpus case {index} must be an object")
        path_value = item.get("path")
        if not isinstance(path_value, str) or not path_value:
            raise ValueError(f"FP corpus case {index} is missing path")
        path = resolve_manifest_path(manifest_path, path_value)
        if not path.is_file():
            raise ValueError(f"FP corpus input does not exist: {path_value}")
        inputs.append(path)
        case_operators = item.get("operators", [])
        case_classes = item.get("classes", [])
        if not isinstance(case_operators, list) or not all(
            isinstance(operator, str) for operator in case_operators
        ):
            raise ValueError(
                f"FP corpus case {index} operators must be a string list"
            )
        if not isinstance(case_classes, list) or not all(
            isinstance(value, str) for value in case_classes
        ):
            raise ValueError(
                f"FP corpus case {index} classes must be a string list"
            )
        operators.update(case_operators)
        classes.update(case_classes)
    missing_operators = sorted(set(FP_REWRITE_OPERATORS) - operators)
    extra_operators = sorted(operators - set(FP_REWRITE_OPERATORS))
    required_classes = manifest.get("required_classes", [])
    if not isinstance(required_classes, list) or not all(
        isinstance(value, str) for value in required_classes
    ):
        raise ValueError("FP corpus required_classes must be a string list")
    missing_classes = sorted(set(required_classes) - classes)
    if missing_operators or extra_operators or missing_classes:
        raise ValueError(
            "FP corpus coverage mismatch: missing operators "
            + (", ".join(missing_operators) or "<none>")
            + "; extra operators "
            + (", ".join(extra_operators) or "<none>")
            + "; missing classes "
            + (", ".join(missing_classes) or "<none>")
        )
    metadata = manifest.get("metadata_only_cases", [])
    if not isinstance(metadata, list) or not any(
        isinstance(item, dict)
        and item.get("id") == "d12_add_commutativity_float32"
        and item.get("proof_recorded") is False
        for item in metadata
    ):
        raise ValueError(
            "FP corpus must pin the metadata-only Float32 fp.add exemplar"
        )
    return set(versions), inputs


def classify_ho_shape(entry: dict[str, object]) -> str:
    proof = entry.get("proof", {})
    shape = proof.get("ho_shape", {}) if isinstance(proof, dict) else {}
    if not isinstance(shape, dict):
        return "invalid"
    lambda_count = shape.get("lambda_term_count", 0)
    named = shape.get("named_lambda_symbols", [])
    lambda_defs = shape.get("lambda_def_axiom_count", 0)
    proof_binds = shape.get("proof_bind_count", 0)
    if (
        isinstance(lambda_count, int)
        and lambda_count > 0
        and named == []
        and lambda_defs == 0
        and proof_binds == 0
    ):
        return "verbatim-lambda"
    if (
        isinstance(lambda_count, int)
        and lambda_count > 0
        and isinstance(named, list)
        and bool(named)
        and isinstance(lambda_defs, int)
        and lambda_defs > 0
        and isinstance(proof_binds, int)
        and proof_binds > 0
    ):
        return "named-lambda-def"
    return "mixed-or-missing"


def validate_ho_shape_matrix(
    entries: list[dict[str, object]],
    manifest_path: pathlib.Path,
) -> list[str]:
    errors: list[str] = []
    selected_cases = {
        str(item.get("id")): item
        for item in complete_manifest_cases(manifest_path)
        if item.get("id") in HO_PROOF_CORPUS_CASE_IDS
    }
    if set(selected_cases) != set(HO_PROOF_CORPUS_CASE_IDS):
        missing = sorted(set(HO_PROOF_CORPUS_CASE_IDS) - set(selected_cases))
        return ["complete corpus manifest is missing HO cases: " + ", ".join(missing)]

    case_by_path: dict[pathlib.Path, tuple[str, dict[str, object]]] = {}
    for case_id, item in selected_cases.items():
        path_value = item.get("path")
        if not isinstance(path_value, str):
            errors.append(f"{case_id}: missing path")
            continue
        case_by_path[
            validation_relative_path(
                resolve_manifest_path(manifest_path, path_value)
            )
        ] = (
            case_id,
            item,
        )

    seen: set[str] = set()
    for entry in entries:
        input_info = entry.get("input", {})
        input_path = input_info.get("path") if isinstance(input_info, dict) else None
        if not isinstance(input_path, str):
            errors.append("HO corpus entry is missing input.path")
            continue
        case_info = case_by_path.get(
            validation_relative_path(pathlib.Path(input_path))
        )
        if case_info is None:
            errors.append(f"unexpected HO corpus input: {input_path}")
            continue
        case_id, case = case_info
        seen.add(case_id)

        z3_info = entry.get("z3", {})
        version = z3_info.get("version") if isinstance(z3_info, dict) else None
        expectations = case.get("expected_shape_families", {})
        expected = expectations.get(version) if isinstance(expectations, dict) else None
        actual = classify_ho_shape(entry)
        if not isinstance(expected, str):
            errors.append(f"{case_id} has no shape expectation for Z3 {version}")
        elif actual != expected:
            errors.append(
                f"{case_id} on Z3 {version}: expected {expected}, got {actual}"
            )

        solver = entry.get("solver", {})
        proof = entry.get("proof", {})
        if not isinstance(solver, dict) or solver.get("result") != "unsat":
            errors.append(f"{case_id} on Z3 {version}: expected unsat")
        if not isinstance(proof, dict) or not proof.get("available"):
            errors.append(f"{case_id} on Z3 {version}: proof is unavailable")
            continue
        if proof.get("unknown_rules"):
            errors.append(f"{case_id} on Z3 {version}: unknown proof rules")
        if proof.get("malformed_fragments"):
            errors.append(f"{case_id} on Z3 {version}: malformed proof fragments")
        histogram = proof.get("rule_histogram", {})
        required = case.get("required_rules", [])
        if isinstance(histogram, dict) and isinstance(required, list):
            missing_rules = sorted(set(required) - set(histogram))
            if missing_rules:
                errors.append(
                    f"{case_id} on Z3 {version}: missing required rules "
                    + ", ".join(missing_rules)
                )

    missing_cases = sorted(set(HO_PROOF_CORPUS_CASE_IDS) - seen)
    if missing_cases:
        errors.append(
            "HO corpus recording is missing cases: "
            + ", ".join(missing_cases)
        )
    return errors


def _rule_list(value: object) -> set[str]:
    if value is None:
        return set()
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError("expected proof-rule manifest entries must be string lists")
    return set(value)


def expected_rules_for_version(manifest: object, version: str) -> set[str]:
    if isinstance(manifest, list):
        return _rule_list(manifest)
    if not isinstance(manifest, dict):
        raise ValueError("expected proof-rule manifest must be a list or object")

    rules = _rule_list(manifest.get("default"))
    rules.update(_rule_list(manifest.get("rules")))
    versions = manifest.get("versions", {})
    if versions is None:
        versions = {}
    if not isinstance(versions, dict):
        raise ValueError("expected proof-rule manifest 'versions' must be an object")

    for key, value in versions.items():
        if not isinstance(key, str):
            raise ValueError("expected proof-rule manifest version keys must be strings")
        if key == version or (key.endswith("*") and version.startswith(key[:-1])):
            rules.update(_rule_list(value))
    return rules


def build_rule_gate_report(
    entries: Iterable[dict[str, object]],
    expected_manifest: object | None,
) -> dict[str, object]:
    unseen: list[dict[str, object]] = []
    replay_unknown: list[dict[str, object]] = []
    parse_only: list[dict[str, object]] = []
    malformed: list[dict[str, object]] = []

    def artifact_refs(entry: dict[str, object]) -> dict[str, object]:
        input_info = entry.get("input", {})
        z3_info = entry.get("z3", {})
        proof_info = entry.get("proof", {})
        artifacts: dict[str, object] = {}
        if isinstance(input_info, dict):
            for source, target in (
                ("sha256", "input_sha256"),
                ("effective_sha256", "effective_input_sha256"),
            ):
                value = input_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        if isinstance(z3_info, dict):
            for source, target in (
                ("stdout_path", "stdout_path"),
                ("stderr_path", "stderr_path"),
            ):
                value = z3_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        if isinstance(proof_info, dict):
            for source, target in (
                ("raw_path", "proof_path"),
                ("raw_sha256", "proof_sha256"),
            ):
                value = proof_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        return artifacts

    for entry in entries:
        input_path = entry["input"]["path"]  # type: ignore[index]
        version = entry["z3"]["version"]  # type: ignore[index]
        proof = entry["proof"]  # type: ignore[index]
        artifacts = artifact_refs(entry)
        expected = (
            expected_rules_for_version(expected_manifest, version)
            if expected_manifest is not None
            else None
        )
        contexts = proof.get("rule_contexts", {})  # type: ignore[union-attr]

        for rule, count in sorted(proof["rule_histogram"].items()):  # type: ignore[index, union-attr]
            if rule in PARSE_ONLY_RULES:
                parse_only.append(
                    {
                        "z3_version": version,
                        "input": input_path,
                        "rule": rule,
                        "count": count,
                        "contexts": contexts.get(rule, []),  # type: ignore[union-attr]
                        "artifacts": artifacts,
                    }
                )

        if expected is not None:
            for rule, count in sorted(proof["rule_histogram"].items()):  # type: ignore[index, union-attr]
                if rule not in expected:
                    unseen.append(
                        {
                            "z3_version": version,
                            "input": input_path,
                            "rule": rule,
                            "count": count,
                            "contexts": contexts.get(rule, []),  # type: ignore[union-attr]
                            "artifacts": artifacts,
                        }
                    )

        for item in proof["unknown_rules"]:  # type: ignore[index, union-attr]
            replay_unknown.append(
                {
                    "z3_version": version,
                    "input": input_path,
                    "rule": item["rule"],  # type: ignore[index]
                    "count": item["count"],  # type: ignore[index]
                    "contexts": item["contexts"],  # type: ignore[index]
                    "artifacts": artifacts,
                }
            )

        fragments = proof["malformed_fragments"]  # type: ignore[index]
        if fragments:
            malformed.append(
                {
                    "z3_version": version,
                    "input": input_path,
                    "fragments": fragments,
                    "artifacts": artifacts,
                }
            )

    return {
        "schema": SCHEMA,
        "kind": "proof-rule-discovery-gate",
        "passed": not unseen and not replay_unknown and not malformed,
        "unseen_rules": unseen,
        "replay_unknown_rules": replay_unknown,
        "parse_only_rules": parse_only,
        "malformed_fragments": malformed,
    }


def entry_rule_histogram(entry: dict[str, object]) -> dict[str, int]:
    proof = entry.get("proof", {})
    if not isinstance(proof, dict):
        return {}
    histogram = proof.get("rule_histogram", {})
    if not isinstance(histogram, dict):
        return {}
    return {
        rule: count
        for rule, count in histogram.items()
        if isinstance(rule, str) and isinstance(count, int)
    }


def entry_inferred_rule_histogram(entry: dict[str, object]) -> dict[str, int]:
    proof = entry.get("proof", {})
    if not isinstance(proof, dict):
        return {}
    histogram = proof.get("inferred_rule_histogram", {})
    if not isinstance(histogram, dict):
        return {}
    return {
        rule: count
        for rule, count in histogram.items()
        if isinstance(rule, str) and isinstance(count, int)
    }


def entry_theory_lemma_histogram(entry: dict[str, object]) -> dict[str, int]:
    proof = entry.get("proof", {})
    if not isinstance(proof, dict):
        return {}
    histogram = proof.get("theory_lemma_histogram", {})
    if not isinstance(histogram, dict):
        return {}
    return {
        key: count
        for key, count in histogram.items()
        if isinstance(key, str) and isinstance(count, int)
    }


def replay_status(entry: dict[str, object]) -> str:
    holsmt = entry.get("holsmt", {})
    if not isinstance(holsmt, dict):
        return "missing"
    replay_result = holsmt.get("replay_result", {})
    if isinstance(replay_result, dict) and isinstance(replay_result.get("status"), str):
        return str(replay_result["status"])
    status = holsmt.get("proof_replay_status")
    return status if isinstance(status, str) else "missing"


def theorem_tag_summary(entry: dict[str, object]) -> dict[str, object]:
    theorem = entry.get("theorem", {})
    if not isinstance(theorem, dict):
        return {}
    tags = theorem.get("tag_summary", {})
    return tags if isinstance(tags, dict) else {}


def has_unexpected_theorem_tags(tags: dict[str, object]) -> bool:
    for field in ("has_oracles", "has_axioms"):
        if tags.get(field) is True:
            return True
    for field in ("oracle_tags", "axiom_tags", "unexpected_tags"):
        value = tags.get(field)
        if isinstance(value, list) and value:
            return True
    return False


def build_requirement_report(
    entries: Iterable[dict[str, object]],
    *,
    required_rules: Iterable[str],
    required_theory_subkinds: Iterable[str],
    require_replay_success: bool,
    require_no_oracles: bool,
    forbidden_rules: Iterable[str] = (),
    require_unsat_proofs: bool = False,
) -> dict[str, object]:
    entries = list(entries)
    aggregate_rules: collections.Counter[str] = collections.Counter()
    aggregate_subkinds: collections.Counter[str] = collections.Counter()
    for entry in entries:
        aggregate_rules.update(entry_rule_histogram(entry))
        aggregate_rules.update(entry_inferred_rule_histogram(entry))
        aggregate_subkinds.update(entry_theory_lemma_histogram(entry))

    missing_rules = [
        {"rule": rule}
        for rule in sorted(set(required_rules))
        if aggregate_rules.get(rule, 0) <= 0
    ]
    forbidden_occurrences = [
        {"rule": rule, "count": aggregate_rules[rule]}
        for rule in sorted(set(forbidden_rules))
        if aggregate_rules.get(rule, 0) > 0
    ]
    missing_subkinds = [
        {"theory_subkind": item}
        for item in sorted(set(required_theory_subkinds))
        if not any(
            count > 0 and fnmatch.fnmatchcase(observed, item)
            for observed, count in aggregate_subkinds.items()
        )
    ]

    unsat_proof_failures: list[dict[str, object]] = []
    if require_unsat_proofs:
        for entry in entries:
            solver = entry.get("solver", {})
            proof = entry.get("proof", {})
            z3 = entry.get("z3", {})
            result = solver.get("result") if isinstance(solver, dict) else None
            available = (
                proof.get("available") if isinstance(proof, dict) else None
            )
            exit_code = z3.get("exit_code") if isinstance(z3, dict) else None
            timed_out = z3.get("timed_out") if isinstance(z3, dict) else None
            if (
                result != "unsat"
                or available is not True
                or exit_code != 0
                or timed_out is not False
            ):
                unsat_proof_failures.append(
                    {
                        "input": (
                            entry.get("input", {}).get("path")
                            if isinstance(entry.get("input"), dict)
                            else None
                        ),
                        "z3_version": (
                            z3.get("version")
                            if isinstance(z3, dict)
                            else None
                        ),
                        "result": result,
                        "proof_available": available,
                        "exit_code": exit_code,
                        "timed_out": timed_out,
                    }
                )

    replay_failures: list[dict[str, object]] = []
    if require_replay_success:
        for entry in entries:
            status = replay_status(entry)
            if status.lower() not in SUCCESS_STATUSES:
                replay_failures.append(
                    {
                        "input": entry.get("input", {}).get("path") if isinstance(entry.get("input"), dict) else None,
                        "z3_version": entry.get("z3", {}).get("version") if isinstance(entry.get("z3"), dict) else None,
                        "proof_replay_status": status,
                    }
                )

    oracle_failures: list[dict[str, object]] = []
    if require_no_oracles:
        for entry in entries:
            tags = theorem_tag_summary(entry)
            if has_unexpected_theorem_tags(tags):
                oracle_failures.append(
                    {
                        "input": entry.get("input", {}).get("path") if isinstance(entry.get("input"), dict) else None,
                        "z3_version": entry.get("z3", {}).get("version") if isinstance(entry.get("z3"), dict) else None,
                        "tag_summary": tags,
                    }
                )

    return {
        "required_rule_occurrences": sorted(set(required_rules)),
        "required_theory_subkinds": sorted(set(required_theory_subkinds)),
        "forbidden_rule_occurrences": sorted(set(forbidden_rules)),
        "require_replay_success": require_replay_success,
        "require_unsat_proofs": require_unsat_proofs,
        "require_no_oracles": require_no_oracles,
        "missing_rule_occurrences": missing_rules,
        "missing_theory_subkinds": missing_subkinds,
        "observed_forbidden_rule_occurrences": forbidden_occurrences,
        "unsat_proof_failures": unsat_proof_failures,
        "replay_failures": replay_failures,
        "oracle_failures": oracle_failures,
        "passed": (
            not missing_rules
            and not missing_subkinds
            and not forbidden_occurrences
            and not unsat_proof_failures
            and not replay_failures
            and not oracle_failures
        ),
    }


def write_minimized_repros(
    repro_dir: pathlib.Path,
    entries: Iterable[dict[str, object]],
    failure_report: dict[str, object],
) -> None:
    repro_dir.mkdir(parents=True, exist_ok=True)
    json_dump(repro_dir / "failure-report.json", failure_report)
    for index, entry in enumerate(entries, 1):
        entry_dir = repro_dir / f"case-{index:03d}"
        entry_dir.mkdir(parents=True, exist_ok=True)
        json_dump(entry_dir / "proof-corpus-entry.json", entry)
        input_info = entry.get("input", {})
        if isinstance(input_info, dict) and isinstance(input_info.get("path"), str):
            source = pathlib.Path(str(input_info["path"]))
            if source.exists():
                shutil.copyfile(source, entry_dir / "input.smt2")
        z3_info = entry.get("z3", {})
        if isinstance(z3_info, dict):
            command_line = z3_info.get("command_line")
            if isinstance(command_line, list):
                write_text(entry_dir / "command.txt", " ".join(str(part) for part in command_line) + "\n")
            for source_field, target_name in (("stdout_path", "stdout.txt"), ("stderr_path", "stderr.txt")):
                source_value = z3_info.get(source_field)
                if isinstance(source_value, str):
                    source = pathlib.Path(source_value)
                    if source.exists():
                        shutil.copyfile(source, entry_dir / target_name)
        proof_info = entry.get("proof", {})
        if isinstance(proof_info, dict) and isinstance(proof_info.get("raw_path"), str):
            source = pathlib.Path(str(proof_info["raw_path"]))
            if source.exists():
                shutil.copyfile(source, entry_dir / "proof.raw")


def _as_string_list(value: object, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        errors.append(f"{label} must be a list of strings")
        return []
    return value


def _read_version_entry(
    manifest_path: pathlib.Path,
    item: dict[str, object],
    input_by_id: dict[str, dict[str, object]],
    errors: list[str],
) -> dict[str, object] | None:
    version = item.get("version")
    input_id = item.get("input")
    if not isinstance(version, str) or not version:
        errors.append("version entry is missing version")
        return None
    if not isinstance(input_id, str) or input_id not in input_by_id:
        errors.append(f"version {version} references unknown input {input_id!r}")
        return None

    input_item = input_by_id[input_id]
    input_path_value = input_item.get("path")
    if not isinstance(input_path_value, str) or not input_path_value:
        errors.append(f"input {input_id} is missing path")
        return None
    input_path = resolve_manifest_path(manifest_path, input_path_value)
    if not input_path.exists():
        errors.append(f"input {input_id} path does not exist: {input_path_value}")
        return None
    expected_input_hash = input_item.get("sha256")
    actual_input_hash = sha256_file(input_path)
    if expected_input_hash != actual_input_hash:
        errors.append(
            f"input {input_id} sha256 mismatch: expected {expected_input_hash}, got {actual_input_hash}"
        )

    def read_artifact(field: str) -> tuple[pathlib.Path | None, str]:
        value = item.get(field)
        if not isinstance(value, str) or not value:
            errors.append(f"version {version} is missing {field}")
            return None, ""
        path = resolve_manifest_path(manifest_path, value)
        if not path.exists():
            errors.append(f"version {version} artifact does not exist: {value}")
            return path, ""
        actual_hash = sha256_file(path)
        expected_hash = item.get(f"{field}_sha256")
        if expected_hash != actual_hash:
            errors.append(
                f"version {version} {field} sha256 mismatch: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        return path, path.read_text(encoding="utf-8")

    stdout_path, stdout = read_artifact("stdout")
    stderr_path, stderr = read_artifact("stderr")
    proof_path, proof_text = read_artifact("proof")
    if stdout_path is None or stderr_path is None or proof_path is None:
        return None

    solver_result, stdout_proof = detect_solver_result(stdout)
    if solver_result != "unsat":
        errors.append(f"version {version} expected unsat stdout, got {solver_result}")
    if stdout_proof != proof_text:
        errors.append(f"version {version} stdout proof payload does not match proof artifact")

    proof_report = extract_rule_report(proof_text)
    expected_rule_sets = item.get("expected_rule_sets")
    if not isinstance(expected_rule_sets, dict):
        errors.append(f"version {version} expected_rule_sets must be an object")
        expected_rule_sets = {}
    histogram = proof_report["rule_histogram"]
    assert isinstance(histogram, dict)
    actual_rule_sets = {
        "replay_supported": sorted(rule for rule in histogram if rule in REPLAY_SUPPORTED_RULES),
        "parse_only": sorted(rule for rule in histogram if rule in PARSE_ONLY_RULES),
        "unsupported": sorted(rule for rule in histogram if rule not in KNOWN_RULES),
        "unknown": sorted(item["rule"] for item in proof_report["unknown_rules"]),  # type: ignore[index]
    }
    for field, actual in actual_rule_sets.items():
        expected = expected_rule_sets.get(field, [])
        if expected != actual:
            errors.append(
                f"version {version} expected_rule_sets.{field} mismatch: "
                f"expected {expected}, got {actual}"
            )

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-entry",
        "input": {
            "path": input_path_value,
            "sha256": actual_input_hash,
            "effective_sha256": actual_input_hash,
            "append_get_proof": False,
        },
        "z3": {
            "executable": str(item.get("z3_executable", "z3")),
            "version": version,
            "command_line": [
                str(item.get("z3_executable", "z3")),
                *_as_string_list(item.get("proof_options", []), f"version {version} proof_options", errors),
                "-smt2",
                input_path_value,
            ],
            "exit_code": int(item.get("exit_code", 0)),
            "timed_out": bool(item.get("timed_out", False)),
            "stdout_path": str(item.get("stdout")),
            "stderr_path": str(item.get("stderr")),
        },
        "solver": {
            "result": solver_result,
            "z3_failure": bool(item.get("z3_failure", False)),
        },
        "proof": {
            "available": bool(proof_text.strip()),
            "raw_path": str(item.get("proof")),
            "raw_sha256": sha256_bytes(proof_text.encode("utf-8")),
            **proof_report,
            "inferred_rule_histogram": {},
        },
        "holsmt": {
            "proof_parse_status": "not-run",
            "proof_replay_status": "not-run",
            "failure": None,
        },
    }


def validate_corpus_manifest(manifest_path: pathlib.Path) -> list[str]:
    errors: list[str] = []
    manifest_obj = load_json(manifest_path)
    if not isinstance(manifest_obj, dict):
        return ["proof corpus manifest root must be an object"]
    if manifest_obj.get("schema") != MATRIX_SCHEMA:
        errors.append(f"proof corpus manifest schema must be {MATRIX_SCHEMA}")

    supported_versions = _as_string_list(
        manifest_obj.get("supported_z3_versions"),
        "supported_z3_versions",
        errors,
    )
    if sorted(supported_versions) != sorted(SUPPORTED_Z3_VERSIONS):
        errors.append(
            "supported_z3_versions mismatch: expected "
            + ", ".join(SUPPORTED_Z3_VERSIONS)
            + "; got "
            + ", ".join(supported_versions)
        )

    inputs = manifest_obj.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        errors.append("inputs must be a non-empty list")
        inputs = []
    input_by_id: dict[str, dict[str, object]] = {}
    for index, input_item in enumerate(inputs, 1):
        if not isinstance(input_item, dict):
            errors.append(f"inputs[{index}] must be an object")
            continue
        input_id = input_item.get("id")
        if not isinstance(input_id, str) or not input_id:
            errors.append(f"inputs[{index}] is missing id")
            continue
        input_by_id[input_id] = input_item

    versions = manifest_obj.get("versions")
    if not isinstance(versions, list) or not versions:
        errors.append("versions must be a non-empty list")
        versions = []

    entries = []
    seen_versions: set[str] = set()
    for index, version_item in enumerate(versions, 1):
        if not isinstance(version_item, dict):
            errors.append(f"versions[{index}] must be an object")
            continue
        entry = _read_version_entry(manifest_path, version_item, input_by_id, errors)
        if entry is None:
            continue
        seen_versions.add(str(entry["z3"]["version"]))  # type: ignore[index]
        entries.append(entry)

    if sorted(seen_versions) != sorted(SUPPORTED_Z3_VERSIONS):
        errors.append(
            "versions must contain exactly the supported Z3 versions: "
            + ", ".join(SUPPORTED_Z3_VERSIONS)
        )

    expected_rules_path = manifest_obj.get("expected_rules")
    expected_rules = None
    if not isinstance(expected_rules_path, str) or not expected_rules_path:
        errors.append("expected_rules must point to an expected-rule manifest")
    else:
        resolved_expected_rules = resolve_manifest_path(manifest_path, expected_rules_path)
        if not resolved_expected_rules.exists():
            errors.append(f"expected_rules path does not exist: {expected_rules_path}")
        else:
            expected_rules = load_expected_rule_manifest(resolved_expected_rules)

    if entries:
        summary = build_summary(entries)
        expected_summary_path = manifest_obj.get("expected_summary")
        if not isinstance(expected_summary_path, str) or not expected_summary_path:
            errors.append("expected_summary must point to a checked-in summary")
        else:
            expected_summary = load_json(resolve_manifest_path(manifest_path, expected_summary_path))
            if expected_summary != summary:
                errors.append("checked-in proof corpus summary is stale")

        if expected_rules is not None:
            gate = build_rule_gate_report(entries, expected_rules)
            expected_gate_path = manifest_obj.get("expected_gate")
            if not isinstance(expected_gate_path, str) or not expected_gate_path:
                errors.append("expected_gate must point to a checked-in gate report")
            else:
                expected_gate = load_json(resolve_manifest_path(manifest_path, expected_gate_path))
                if expected_gate != gate:
                    errors.append("checked-in proof-rule gate report is stale")
            if not gate["passed"]:  # type: ignore[index]
                errors.append("proof-rule gate fails for checked-in corpus")

        discovered_rules = set(summary["discovered_rules"])  # type: ignore[index]
        replay_missing = sorted(REPLAY_SUPPORTED_RULES - discovered_rules)
        replay_justifications = manifest_obj.get("missing_replay_supported_justifications", {})
        if not isinstance(replay_justifications, dict):
            errors.append("missing_replay_supported_justifications must be an object")
            replay_justifications = {}
        for rule in replay_missing:
            if not isinstance(replay_justifications.get(rule), str) or not replay_justifications[rule]:
                errors.append(f"missing replay-supported rule lacks justification: {rule}")
        for rule in replay_justifications:
            if rule not in REPLAY_SUPPORTED_RULES:
                errors.append(f"justification names an unknown replay-supported rule: {rule}")

        parse_only_missing = sorted(PARSE_ONLY_RULES - discovered_rules)
        parse_only_justifications = manifest_obj.get("missing_parse_only_justifications", {})
        if not isinstance(parse_only_justifications, dict):
            errors.append("missing_parse_only_justifications must be an object")
            parse_only_justifications = {}
        for rule in parse_only_missing:
            if (
                not isinstance(parse_only_justifications.get(rule), str)
                or not parse_only_justifications[rule]
            ):
                errors.append(f"missing parse-only rule lacks justification: {rule}")

    return errors


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Z3 on SMT-LIB inputs and record raw proof-rule histograms."
    )
    parser.add_argument("inputs", nargs="*", help="SMT-LIB files to run through Z3")
    parser.add_argument(
        "--z3",
        default=os.environ.get("HOL4_Z3_EXECUTABLE") or "z3",
        help="Z3 executable, defaulting to HOL4_Z3_EXECUTABLE or z3",
    )
    parser.add_argument(
        "--z3-version",
        help="override detected Z3 version for version-selected corpus recording",
    )
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=DEFAULT_OUTPUT_DIR,
        help="output directory for JSON and raw solver artifacts",
    )
    parser.add_argument(
        "--entries",
        default="entries.jsonl",
        help="JSONL file name inside --out",
    )
    parser.add_argument(
        "--summary",
        default="summary.json",
        help="summary JSON file name inside --out",
    )
    parser.add_argument(
        "--append-get-proof",
        action="store_true",
        help="run a temporary copy with check-sat/get-proof/exit appended when missing",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="per-input Z3 timeout in seconds",
    )
    parser.add_argument(
        "--z3-option",
        action="append",
        default=[],
        help="additional option passed to Z3 before -smt2",
    )
    parser.add_argument(
        "--expected-rules",
        type=pathlib.Path,
        help=(
            "JSON manifest of expected proof rules. A list applies to every Z3 "
            "version; an object may contain default/rules and versions entries."
        ),
    )
    parser.add_argument(
        "--gate-report",
        default="rule-gate.json",
        help="rule-discovery gate JSON file name inside --out",
    )
    parser.add_argument(
        "--fail-on-unseen-rules",
        action="store_true",
        help="return nonzero if a discovered proof rule is absent from --expected-rules",
    )
    parser.add_argument(
        "--fail-on-unknown-rules",
        action="store_true",
        help="return nonzero if a discovered proof rule is not replay-supported by HolSmt",
    )
    parser.add_argument(
        "--validate-corpus-manifest",
        nargs="?",
        const=DEFAULT_SUPPORTED_VERSION_MANIFEST,
        type=pathlib.Path,
        help=(
            "validate a checked-in proof-corpus matrix manifest without running Z3; "
            "defaults to the supported-version corpus manifest"
        ),
    )
    parser.add_argument(
        "--complete-corpus-manifest",
        nargs="?",
        const=DEFAULT_COMPLETE_CORPUS_MANIFEST,
        type=pathlib.Path,
        help=(
            "load complete proof-corpus case metadata; when no input files are "
            "provided, record the selected --case-id entries from this manifest"
        ),
    )
    parser.add_argument(
        "--string-corpus",
        nargs="?",
        const=DEFAULT_STRING_CORPUS_MANIFEST,
        type=pathlib.Path,
        help=(
            "record the Phase 4 string/regex corpus; an optional argument "
            "selects a non-default manifest"
        ),
    )
    parser.add_argument(
        "--fp-corpus",
        nargs="?",
        const=DEFAULT_FP_CORPUS_MANIFEST,
        type=pathlib.Path,
        help=(
            "record the Phase 5 FloatingPoint corpus; an optional argument "
            "selects a non-default manifest"
        ),
    )
    parser.add_argument(
        "--case-id",
        action="append",
        default=[],
        help="case id to select from --complete-corpus-manifest; may be repeated",
    )
    parser.add_argument(
        "--ho-corpus",
        action="store_true",
        help=(
            "record the Phase 3 C1 higher-order proof-shape cases from the "
            "complete corpus manifest"
        ),
    )
    parser.add_argument(
        "--require-rule-occurrence",
        action="append",
        default=[],
        metavar="RULE",
        help="return nonzero unless the recorded corpus contains RULE",
    )
    parser.add_argument(
        "--forbid-rule-occurrence",
        action="append",
        default=[],
        metavar="RULE",
        help="return nonzero if the recorded corpus contains RULE",
    )
    parser.add_argument(
        "--require-theory-subkind",
        action="append",
        default=[],
        metavar="THEORY:SUBKIND",
        help="return nonzero unless a th-lemma with THEORY:SUBKIND metadata is recorded",
    )
    parser.add_argument(
        "--require-unsat-proofs",
        action="store_true",
        help=(
            "return nonzero unless every solver run produced an unsat proof "
            "without timeout or Z3 failure"
        ),
    )
    parser.add_argument(
        "--require-replay-success",
        action="store_true",
        help="return nonzero unless every entry has successful HolSmt replay metadata",
    )
    parser.add_argument(
        "--require-no-oracles",
        action="store_true",
        help="return nonzero if theorem tag metadata reports oracle or axiom tags",
    )
    parser.add_argument(
        "--minimized-repro-dir",
        type=pathlib.Path,
        help="write minimized input/command/stdout/stderr/proof repros for failing proof cases",
    )
    args = parser.parse_args(argv)
    if args.fp_corpus is not None:
        args.require_unsat_proofs = True
    if args.validate_corpus_manifest is not None:
        return args
    if args.ho_corpus and args.complete_corpus_manifest is None:
        args.complete_corpus_manifest = DEFAULT_COMPLETE_CORPUS_MANIFEST
    corpus_selectors = sum(
        value is not None
        for value in (
            args.string_corpus,
            args.fp_corpus,
            args.complete_corpus_manifest,
        )
    )
    if corpus_selectors > 1:
        parser.error(
            "--string-corpus, --fp-corpus, and "
            "--complete-corpus-manifest are mutually exclusive"
        )
    if args.case_id and args.complete_corpus_manifest is None:
        parser.error("--case-id requires --complete-corpus-manifest")
    malformed_subkinds = [item for item in args.require_theory_subkind if ":" not in item]
    if malformed_subkinds:
        parser.error("--require-theory-subkind values must have THEORY:SUBKIND shape")
    if (
        not args.inputs
        and args.complete_corpus_manifest is None
        and args.string_corpus is None
        and args.fp_corpus is None
    ):
        parser.error(
            "SMT-LIB input files, --complete-corpus-manifest, "
            "--string-corpus, or --fp-corpus is required"
        )
    if args.fail_on_unseen_rules and args.expected_rules is None:
        parser.error("--fail-on-unseen-rules requires --expected-rules")
    return args


def print_gate_findings(report: dict[str, object]) -> None:
    unseen = report["unseen_rules"]  # type: ignore[index]
    replay_unknown = report["replay_unknown_rules"]  # type: ignore[index]
    malformed = report["malformed_fragments"]  # type: ignore[index]
    if unseen:
        print("unseen proof rules:")
        for item in unseen[:10]:  # type: ignore[index]
            print(
                f"  {item['z3_version']} {item['input']}: "  # type: ignore[index]
                f"{item['rule']} ({item['count']})"  # type: ignore[index]
            )
    if replay_unknown:
        print("HolSmt replay-unknown proof rules:")
        for item in replay_unknown[:10]:  # type: ignore[index]
            print(
                f"  {item['z3_version']} {item['input']}: "  # type: ignore[index]
                f"{item['rule']} ({item['count']})"  # type: ignore[index]
            )
    if malformed:
        print("malformed proof fragments:")
        for item in malformed[:10]:  # type: ignore[index]
            print(f"  {item['z3_version']} {item['input']}")  # type: ignore[index]


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.validate_corpus_manifest is not None:
        errors = validate_corpus_manifest(args.validate_corpus_manifest)
        if errors:
            print("proof corpus manifest validation failed:")
            for error in errors:
                print(f"  {error}")
            return 1
        print(f"validated proof corpus manifest {args.validate_corpus_manifest}")
        return 0

    out_dir = args.out.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    try:
        if args.complete_corpus_manifest is not None:
            supported_versions = complete_manifest_supported_versions(args.complete_corpus_manifest)
            if args.z3_version is not None and args.z3_version not in supported_versions:
                print(
                    f"selected Z3 version {args.z3_version} is not listed in "
                    f"{args.complete_corpus_manifest}",
                    file=sys.stderr,
                )
                return 2
            if not args.inputs:
                args.inputs = [
                    str(path)
                    for path in inputs_from_complete_manifest(
                        args.complete_corpus_manifest,
                        [
                            *args.case_id,
                            *(
                                HO_PROOF_CORPUS_CASE_IDS
                                if args.ho_corpus
                                else ()
                            ),
                        ],
                    )
                ]
        elif args.string_corpus is not None:
            supported_versions, inputs = inputs_from_string_manifest(
                args.string_corpus
            )
            if (
                args.z3_version is not None
                and args.z3_version not in supported_versions
            ):
                print(
                    f"selected Z3 version {args.z3_version} is not listed in "
                    f"{args.string_corpus}",
                    file=sys.stderr,
                )
                return 2
            if not args.inputs:
                args.inputs = [str(path) for path in inputs]
        elif args.fp_corpus is not None:
            supported_versions, inputs = inputs_from_fp_manifest(
                args.fp_corpus
            )
            if (
                args.z3_version is not None
                and args.z3_version not in supported_versions
            ):
                print(
                    f"selected Z3 version {args.z3_version} is not listed in "
                    f"{args.fp_corpus}",
                    file=sys.stderr,
                )
                return 2
            if not args.inputs:
                args.inputs = [str(path) for path in inputs]
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"proof corpus manifest error: {exc}", file=sys.stderr)
        return 2

    detected_version = z3_version(args.z3)
    if args.z3_version is not None and detected_version != args.z3_version:
        print(
            f"selected Z3 version {args.z3_version} does not match executable "
            f"version {detected_version}",
            file=sys.stderr,
        )
        return 2
    version = args.z3_version or detected_version

    entries = [
        record_one(
            pathlib.Path(path),
            out_dir,
            args.z3,
            version,
            args.z3_option,
            args.append_get_proof,
            args.timeout,
        )
        for path in args.inputs
    ]

    entries_path = out_dir / args.entries
    with entries_path.open("w", encoding="utf-8") as outfile:
        for entry in entries:
            json.dump(entry, outfile, sort_keys=True)
            outfile.write("\n")

    summary = build_summary(entries)
    json_dump(out_dir / args.summary, summary)

    print(f"wrote {len(entries)} corpus entries to {entries_path}")
    print(f"wrote summary to {out_dir / args.summary}")

    ho_entries = [
        entry
        for entry in entries
        if isinstance(entry.get("input"), dict)
        and pathlib.Path(str(entry["input"].get("path", ""))).stem.startswith(
            "proof_rule_ho_"
        )
    ]
    should_validate_ho = args.ho_corpus or (
        args.complete_corpus_manifest is not None
        and len(ho_entries) == len(HO_PROOF_CORPUS_CASE_IDS)
    )
    if should_validate_ho:
        assert args.complete_corpus_manifest is not None
        shape_errors = validate_ho_shape_matrix(
            ho_entries,
            args.complete_corpus_manifest,
        )
        if shape_errors:
            print("higher-order proof-shape matrix validation failed:")
            for error in shape_errors:
                print(f"  {error}")
            return 1

    expected_manifest = None
    if args.expected_rules is not None:
        expected_manifest = load_expected_rule_manifest(args.expected_rules)

    has_requirements = bool(
        args.require_rule_occurrence
        or args.forbid_rule_occurrence
        or args.require_theory_subkind
        or args.require_unsat_proofs
        or args.require_replay_success
        or args.require_no_oracles
    )
    should_write_gate = args.expected_rules is not None or args.fail_on_unknown_rules or has_requirements
    if not should_write_gate:
        return 0

    gate_report = build_rule_gate_report(entries, expected_manifest)
    requirement_report = build_requirement_report(
        entries,
        required_rules=args.require_rule_occurrence,
        required_theory_subkinds=args.require_theory_subkind,
        require_replay_success=args.require_replay_success,
        require_no_oracles=args.require_no_oracles,
        forbidden_rules=args.forbid_rule_occurrence,
        require_unsat_proofs=args.require_unsat_proofs,
    )
    if has_requirements:
        gate_report["requirements"] = requirement_report
        gate_report["passed"] = bool(gate_report["passed"]) and bool(requirement_report["passed"])
    gate_path = out_dir / args.gate_report
    json_dump(gate_path, gate_report)
    print(f"wrote proof-rule gate report to {gate_path}")

    fail_unseen = bool(gate_report["unseen_rules"]) or bool(gate_report["malformed_fragments"])
    fail_unknown = bool(gate_report["replay_unknown_rules"])
    fail_requirements = has_requirements and not requirement_report["passed"]
    if (
        (args.fail_on_unseen_rules and fail_unseen)
        or (args.fail_on_unknown_rules and fail_unknown)
        or fail_requirements
    ):
        print_gate_findings(gate_report)
        if fail_requirements:
            print("proof corpus requirement failures:")
            for field in (
                "missing_rule_occurrences",
                "missing_theory_subkinds",
                "replay_failures",
                "oracle_failures",
            ):
                items = requirement_report[field]
                if items:
                    print(f"  {field}: {len(items)}")
        if args.minimized_repro_dir is not None:
            write_minimized_repros(args.minimized_repro_dir, entries, gate_report)
            print(f"wrote minimized repros to {args.minimized_repro_dir}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
