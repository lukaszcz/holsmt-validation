(set-logic SNIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
