(set-logic HO_UFLIA)
(declare-const f (-> Int Int))
(assert (distinct (_ f 0) (_ f 0)))
(check-sat)
