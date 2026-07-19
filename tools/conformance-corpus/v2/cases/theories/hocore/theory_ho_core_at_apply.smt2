(set-logic HO_QF_UFLRA)
(declare-const f (-> Real Real))
(assert (distinct (@ f 0.0) (@ f 0.0)))
(check-sat)
