(set-logic HO_AUFLIA)
(declare-const f (-> Int Bool))
(assert (distinct (f 0) (f 0)))
(check-sat)
