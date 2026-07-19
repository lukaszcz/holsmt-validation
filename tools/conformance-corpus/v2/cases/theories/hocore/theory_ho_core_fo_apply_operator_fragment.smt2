(set-logic QF_AUFLIA)
(declare-const f (-> Int Bool))
(assert (_ f 0))
(check-sat)
