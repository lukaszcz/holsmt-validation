(set-logic QF_FP)
(assert (= (fp #b1 #b11111 #b0000000001) (_ NaN 5 11)))
(check-sat)
(exit)
