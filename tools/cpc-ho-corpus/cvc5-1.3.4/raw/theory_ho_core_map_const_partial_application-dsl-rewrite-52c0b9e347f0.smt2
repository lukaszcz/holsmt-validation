(set-logic HO_QF_AUFLIA)
(declare-const f (-> Int (-> Bool Bool)))
(assert (distinct (f 0) (f 0)))
(check-sat)
