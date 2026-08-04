(set-option :produce-proofs true)
(set-logic QF_FP)
(assert
  (not
    (= (fp.roundToIntegral RNA (fp #b1 #b100 #b0100))
       (fp #b1 #b100 #b1000))))
(check-sat)
(get-proof)
(exit)
