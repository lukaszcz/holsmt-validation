(set-logic QF_FPLRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
