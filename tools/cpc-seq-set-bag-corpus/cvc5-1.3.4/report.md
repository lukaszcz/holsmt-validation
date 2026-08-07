# cvc5 CPC corpus baseline

- Schema: `holsmt-cvc5-cpc-corpus-v1`
- cvc5: `1.3.4` (`/home/lukasz/.local/bin/cvc5`)
- Captures: 58

| Granularity | Queries | Proof bytes | Proof steps | `trust` steps | D12 gates | Unique rules |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `dsl-rewrite` | 58 | 68291 | 826 | 41 | 0 | 36 |

## Frozen rule inventory

### `dsl-rewrite`

`absorb` (3), `aci_norm` (3), `alpha_equiv` (4), `and_elim` (66), `beta-reduce` (8), `bool-double-not-elim` (6), `cong` (139), `contra` (8), `distinct-elim` (4), `eq-refl` (10), `eq-symm` (6), `eq_resolve` (64), `evaluate` (93), `ite-then-true` (3), `ite-true-cond` (2), `nary_cong` (14), `refl` (64), `seq-eval-op` (52), `sets-card-singleton` (1), `sets-choose-singleton` (2), `sets-eval-op` (1), `sets-insert-elim` (2), `sets-is-empty-elim` (2), `sets-is-singleton-elim` (1), `sets-member-emp` (1), `sets-member-singleton` (8), `sets-minus-member` (1), `sets-minus-self` (1), `sets-subset-elim` (1), `sets-union-comm` (3), `sets-union-member` (2), `str-at-elim` (1), `symm` (10), `trans` (198), `true_intro` (1), `trust` (41)
