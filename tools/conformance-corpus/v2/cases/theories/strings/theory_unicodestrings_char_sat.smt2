(set-logic QF_SLIA)
(assert (= (_ char #x41) (_ char #x41)))
(check-sat)
