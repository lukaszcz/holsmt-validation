(set-logic QF_FP)
(declare-const x Float32)
(assert
  (not
    (= (fp.add RNE x (fp #b0 #x7f #b00000000000000000000000))
       (fp.add RNE (fp #b0 #x7f #b00000000000000000000000) x))))
(check-sat)
(exit)
