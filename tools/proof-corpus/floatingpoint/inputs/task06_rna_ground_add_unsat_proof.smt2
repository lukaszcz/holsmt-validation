(set-option :produce-proofs true)
(set-logic QF_FP)
(assert
  (not
    (= (fp.add RNA (fp #b0 #b011 #b0000)
                    (fp #b0 #b000 #b0010))
       (fp #b0 #b011 #b0001))))
(check-sat)
(get-proof)
(exit)
