(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 5))
(assert
  (not
    (= (fp.add RNE x (fp #b0 #b011 #b0000))
       (fp.add RNE (fp #b0 #b011 #b0000) x))))
(check-sat)
(exit)
