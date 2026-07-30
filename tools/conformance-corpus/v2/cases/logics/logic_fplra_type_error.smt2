(set-logic FPLRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
