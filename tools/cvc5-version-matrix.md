# cvc5 CPC version matrix

Corpus capture uses native CPC output with:

```
--produce-proofs --dump-proofs --proof-format-mode=cpc \
--proof-granularity=dsl-rewrite --lang smt
```

The corpus recorder additionally uses `--proof-print-conclusion`.  The live
checked driver instead requests exactly one proof with the query's
`(get-proof)` command and omits `--dump-proofs`; combining both mechanisms
prints two wrappers, which the exact CPC stream grammar correctly rejects.
The inspection option is deliberately not enabled by the live driver:
existing non-string handlers reconstruct their certificate conclusions in
HOL-normal forms.

| cvc5 version | CPC mode | Checked corpus result | Status |
| --- | --- | --- | --- |
| 1.3.4 | `dsl-rewrite` | 60/60 captured queries; 6/6 datatype conformance cases | supported |

| cvc5 version | HO logics and surface | CPC HO export | Checked HO replay |
| --- | --- | --- | --- |
| 1.3.4 | `HO_*`; arrows, lambda, `@`, omission/partial-application extension | 9/9 native queries, 155 steps, 30 rules | 9/9 native queries plus the `thm_CVCp` selftest band |

| cvc5 version | String corpus | CPC string export | Checked status |
| --- | --- | --- | --- |
| 1.3.4 | 52 D2/D5 queries; 48 proofs; 2,130 steps | 3 `string_*` rules, 24 string RARE rewrites, 0 `trust`; `str` not observed | 17/38 normalized ground inputs replay; remaining certificate blockers are named below |

| cvc5 version | FloatingPoint corpus | CPC FP export | Checked status |
| --- | --- | --- | --- |
| 1.3.4 | 44 queries, `--fp-exp`, 3,591,281 proof bytes | 22,118 steps, 50 rules, 88 `trust` (0.40%), 0 proof-size gates | 28 replay; 1 D12 gate; 13 `trust` obligations; 2 parse-time obligations |

The FP inventory is frozen at `dsl-rewrite` granularity.  All 42 observed
`ProofRule` names and all eight observed `RareRewrite` names are registered.
The FP-specific additions are checked handlers for `equiv_elim1`,
`bool-eq-true`, `bool-xor-comm`, `bool-xor-false`, and `bool-xor-true`;
the live matrix additionally required `bool-impl-true1`.  The `trust`
handler routes FP conclusions through `SmtFpProve` with no oracle fallback.

| FP obligation | Cases | 1.3.4 status |
| --- | ---: | --- |
| `trust`: cvc5 private `@fp.*` bit decomposition | 11 | parsed as free HOL bit-vectors; the missing relationship to the source FP term is rejected with `rule=trust; theory=fp` |
| `trust`: underspecified `fp.min_total` / `fp.max_total` | 2 | parsed as free HOL functions; the missing public/private operator bridge is rejected with `rule=trust; theory=fp` |
| CPC scale-certificate parsing | 2 | 0.75 MB / 1.31 MB proofs exceed both the 60 s matrix timeout and a 180 s audit timeout; tracked performance obligations |
| `trust`: symbolic add circuit residue | 1 | `CVC_CPC_TAC_RESOURCE_GATED`; D12 term-size diagnostic, 200001 observed / 200000 maximum |

The 28 checked cases cover arbitrary formats, every ground arithmetic
operator, all five FP literals and NaN payload equality, mixed-format and
Real/BV conversions, and symbolic negation/to-real normalization.  Every
successful theorem is kernel checked; the driver and selftests run
`Library.check_oracle_tags`.

The explicitly labeled `cvc5-oracle` conformance band has 38/38 passing FP
logic rows (SAT and UNSAT for each of 19 accepted FP-bearing logics).  Those
rows record solver answers only and do not create HOL theorems.

## Complete cvc5-1.3.4 String/RegLan/Seq RARE inventory

The observed 1.3.4 String corpus above contains 24 String RARE names.  It is
corpus evidence, not a complete support inventory.  Independently, the two
pinned cvc5 source files contain 169 unique active RARE definitions (158 in
`rewrites` and 11 in `rewrites-regexp-membership`).  All 169 have executable,
name-specific dispositions: 134 checked proofs and 35 exact unsupported
diagnostics.  The latter are two `str.indexof_re` rules, eight case-conversion
rules, and 25 intensional-regex equality rules.  There is no generic fallback.
Public CPC parse/replay preserves each exact diagnostic even when the rejected
conclusion contains an operator that the HOL term parser does not support.
A CPC-only proof tokenizer preserves String and quoted-symbol identity; the Z3
proof tokenizer is unchanged. Raw String text is printable ASCII (Unicode uses
`\\u` escapes), while quoted symbols permit valid extended UTF-8 but reject
controls, backslash, vertical bar, and malformed UTF-8. General SMT-LIB
lexing is unchanged. String tokens are decoded only for cvc5 `@var` names.
Ordinary and quoted user spellings share one canonical key, including
occurrence provenance through definitions, lets, binder shadowing, and CPC
`@list` aliases; quoted reserved/builtin spellings remain isolated. Native
aggregate RARE replays exercise definitions, lets, and binders in both spelling
directions. Baseline, source/query, and proof provenance prevents builtin
shadowing, duplicates, arity changes, and incompatible signatures. The
semantic bypass occurs only after a syntax-only
CST grammar validates every complete conclusion and argument term. It checks
simple-symbol and literal lexing,
context-specific simple/indexed/qualified identifiers, index atoms, sorts,
binders, constructor patterns, lets, matches, annotations, and core arities.
Premise-list syntax and existing live-scope IDs, known step attributes,
balanced input, and the final delimiter remain mandatory. Command IDs are
unique in each live scope; post-pop reuse is accepted only for a
normalized-identical step signature. Datatype declarations must match the
complete source constructor family and each selector's ordered constructor
ownership and type. Positive recursive, parametric, mutual, and translated
Option cases and negative omitted/extra-constructor and same-typed-selector
swaps pin this structural identity. Unsupported steps add no dummy proof node:
the first exact diagnostic is retained while later commands and wrappers
are consumed through true EOF. A later lexical or structural error takes
precedence; otherwise the pending diagnostic is issued after parsing.

The 70 upstream `:list` formals have one unambiguous aggregate in the pinned
source: 48 `str.++`, 10 `re.++`, seven `re.union`, and five `re.inter`.  The
63 formals in the declarative source table record those operations explicitly
across 41 recipes: the 28 proved recipes from this review and 13 exact
unsupported recipes (the other seven source formals belong to the earlier
specialized tranche).  Native cvc5 aggregate substitutions are the public
contract: a bare aggregate identity is
empty, a matching variadic application contributes its lexical operands, and
another carrier term is a singleton.  All 28 proved list-bearing recipes are
asserted by exact name and exercise actual CPC text parsing plus replay with
native multi-operand aggregates (21
polymorphic recipes use `(Seq Int)` and seven fixed String/RegLan recipes use
their source carrier).  Their results replace, rather than duplicate, the
direct HOL-list sweep work.  Separate String and Seq zero/one/multiple cases,
regex concat/union/intersection cases, and reduced reproductions of frozen
`draft_length` line 105 and `draft_re_loop` lines 206/209 remain permanent
public parser/replay tests.  Mismatched aggregates and carriers are rejected.

The independently maintained fixture is
`tools/cvc5-1.3.4-string-rare-names.txt`. Reproduce it from upstream commit
`f3b21c4483d3b88dc63cb7cd3e5eb092eee5e341` (the `cvc5-1.3.4` release) with:

```sh
python3 tools/check_cvc5_rare_inventory.py --hol-root "$HOLSMT_ROOT"
# Offline, against an existing source export:
python3 tools/check_cvc5_rare_inventory.py --hol-root "$HOLSMT_ROOT" \
  --source-dir /path/to/cvc5
```

Root selection is, in order: explicit `--hol-root`, `HOLSMT_ROOT`, then the
current working directory and its ancestors.  A candidate must contain the
required embedded HolSmt fixture markers; the checker never guesses a HOL
path from the companion checkout's installation path.  Thus no override is
needed when invoked from the HolSmt worktree, while `--hol-root` works from
any directory.  If no marked tree is found, the diagnostic asks for one of
the two overrides.  The checker disables Python bytecode generation so
inventory runs cannot add cache files to retained evidence.
The checker verifies both upstream file SHA-256 values, recognizes
`define-rule`, `define-cond-rule`, and starred forms, checks the 158/11 counts,
checks uniqueness and the combined sorted-name SHA-256, compares exact
fixture contents, derives the authoritative list-aggregate map (SHA-256
`4648895120c301155f8f7bb306c7938d349e159446d4fbf57bea70639c185f81`),
compares all 63 declarative HOL metadata entries by rule and formal name, and
checks the 28-proved/13-unsupported aggregate-recipe disposition split.

| Namespace | Scope | 1.3.4 checked status |
| --- | --- | --- |
| ProofRule | `str` | registered; no corpus occurrence |
| ProofRule | `string_eager_reduction` | Boolean target routed to checked string re-prover |
| ProofRule | `string_length_pos` | reconstruction [1] |
| ProofRule | `string_reduction` | Boolean target routed to checked string re-prover |
| RareRewrite | all 169 names | complete disposition [2] |

[1]: The omitted target requires rule-specific reconstruction.
[2]: 134 exact kernel proofs and 35 exact unsupported diagnostics cover the
complete String/RegLan/Seq fixture.

The normalized ground replay pass also records two surrounding CPC-core
obligations rather than attributing them to a string RARE handler:

- `trans` composes an equality with cvc5's Boolean equality-normalization in
  12 ground certificates; the existing trans handler rejects the reversed
  intermediate orientation.
- `evaluate` in `extra_char_constant` leaves a normalized string-character
  hypothesis that the final CPC hypothesis check cannot match to the source
  assertion.

The 1.3.4 corpus was captured on 2026-07-14 and replayed again on
2026-07-15 against the current checker: all 60 retained post-preprocessing
queries and all 6 datatype conformance cases passed.  It has no CPC `trust`
steps at the pinned granularity.
The datatype conformance slice covers constructor disjointness, mutual,
parametric, and recursive declarations, selectors, and constructor/tester
terms.  Its QF_DT disjointness seed declares `Color` with `red` and `blue`,
asserts `(= red blue)`, and replays to the HOL theorem `~(red = blue)`.

The higher-order row is recorded under `tools/cpc-ho-corpus/`.  Its two
exported `trust` steps are not oracle admissions: the HOL CPC `trust`
handler independently reproves their explicit propositions and the final
theorems pass `Library.check_oracle_tags`.  cvc5 1.3.4 rejects standard
SMT-LIB 2.7 `(_ f x)` application syntax and accepts its `(@ f x)`
extension; the HOL cvc5 boundary therefore emits `@` while the shared parser
continues to accept both standard spellings.

For a cvc5 upgrade, capture the generated SMT-LIB inputs and run:

```
python3 "$HOLSMT_VALIDATION_DIR/tools/record_cvc5_cpc_corpus.py" \
  --cvc5 "$HOL4_CVC_EXECUTABLE" --out /tmp/cvc5-cpc-corpus <queries>/*.smt2
"$HOLSMT_VALIDATION_DIR/tools/run_cvc5_cpc_gate.sh" \
  --out /tmp/cvc5-cpc-matrix.json <queries>/*.smt2
```

For the HO row, use `tools/cpc-ho-corpus/inputs.txt` and the exact commands
in its README.  Recheck logic acceptance, `@` application, partial
application, lambda export, the CPC inventory, and checked replay together.
For the string row, use `tools/cpc-string-corpus/README.md`, compare all named
rows above, run the checked `thm_CVCp` selftest band, and run the
`cvc5-oracle` conformance mode as an explicitly labeled solver-result check.
For the FP row, use `tools/cpc-fp-corpus/README.md`.  A version bump must
recapture with `--solver-arg=--fp-exp`, compare both rule namespaces, trust
density, and proof sizes against the 16 MB pre-parse gate, then rerun the
44-case checked matrix and the labeled FP `cvc5-oracle` conformance rows.

Only promote a new version after every matrix entry is a checked pass, an
enumerated D12 resource gate, or a named certificate-shape obligation in this
file, and after the version is added to the CPC rule registry.  Unknown rules
or an unregistered dialect are version-gated replay obligations, not
candidates for unchecked fallback.
