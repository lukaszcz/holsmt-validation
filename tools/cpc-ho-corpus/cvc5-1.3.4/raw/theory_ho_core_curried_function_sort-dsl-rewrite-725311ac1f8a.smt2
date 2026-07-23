(set-logic HO_UFLRA)
(declare-const f (-> Real (-> Bool Bool)))
(assert (distinct f f))
(check-sat)
