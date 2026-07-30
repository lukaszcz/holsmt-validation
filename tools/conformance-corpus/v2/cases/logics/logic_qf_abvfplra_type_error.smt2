(set-logic QF_ABVFPLRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
