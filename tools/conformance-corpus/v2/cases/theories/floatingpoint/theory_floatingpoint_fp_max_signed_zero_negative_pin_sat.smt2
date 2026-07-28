(set-logic QF_FP)
(assert (= (fp.max (_ +zero 3 5) (_ -zero 3 5)) (_ -zero 3 5)))
(check-sat)
(exit)
