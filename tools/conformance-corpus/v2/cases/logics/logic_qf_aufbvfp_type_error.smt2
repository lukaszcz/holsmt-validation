(set-logic QF_AUFBVFP)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
