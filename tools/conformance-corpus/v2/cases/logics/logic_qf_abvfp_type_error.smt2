(set-logic QF_ABVFP)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
