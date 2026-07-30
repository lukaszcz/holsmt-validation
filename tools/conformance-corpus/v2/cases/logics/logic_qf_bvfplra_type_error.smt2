(set-logic QF_BVFPLRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
