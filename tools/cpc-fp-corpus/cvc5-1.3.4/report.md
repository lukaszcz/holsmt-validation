# cvc5 CPC corpus baseline

- Schema: `holsmt-cvc5-cpc-corpus-v1`
- cvc5: `1.3.4` (`/home/lukasz/.local/bin/cvc5`)
- Captures: 44

| Granularity | Queries | Proof bytes | Proof steps | `trust` steps | D12 gates | Unique rules |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `dsl-rewrite` | 44 | 3591281 | 22118 | 88 | 0 | 50 |

## Frozen rule inventory

### `dsl-rewrite`

`absorb` (266), `aci_norm` (1541), `and_elim` (25), `and_intro` (1), `arith-elim-leq` (1), `arith_poly_norm` (2), `arith_poly_norm_rel` (1), `bool-double-not-elim` (191), `bool-eq-false` (401), `bool-eq-true` (200), `bool-xor-comm` (58), `bool-xor-false` (103), `bool-xor-true` (46), `bv_bitblast_step` (1787), `chain_m_resolution` (1524), `cnf_and_neg` (199), `cnf_and_pos` (1554), `cnf_equiv_neg1` (58), `cnf_equiv_neg2` (39), `cnf_equiv_pos1` (62), `cnf_equiv_pos2` (61), `cnf_or_neg` (270), `cnf_or_pos` (366), `cnf_xor_neg1` (42), `cnf_xor_neg2` (16), `cnf_xor_pos1` (47), `cnf_xor_pos2` (15), `cong` (1359), `eq-refl` (23), `eq-symm` (413), `eq_resolve` (221), `equiv_elim1` (68), `equiv_elim2` (29), `evaluate` (71), `factoring` (1), `implies_elim` (1), `modus_ponens` (1), `nary_cong` (3279), `not_and` (2), `not_implies_elim1` (1), `not_implies_elim2` (1), `not_or_elim` (4), `process_scope` (2), `refl` (918), `reordering` (2485), `resolution` (1), `scope` (4), `symm` (3), `trans` (4271), `trust` (88)
