(set-logic QF_FP)
(assert (= (fp.min (_ +zero 3 5) (_ -zero 3 5)) (_ +zero 3 5)))
(check-sat)
(exit)
