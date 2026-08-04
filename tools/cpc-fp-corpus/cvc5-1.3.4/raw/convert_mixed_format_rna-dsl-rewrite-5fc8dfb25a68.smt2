(set-option :produce-proofs true)
(set-logic QF_FP)
(assert
  (not
    (= ((_ to_fp 3 5) RNA (fp #b0 #b0111 #b000010))
       (fp #b0 #b011 #b0001))))
(check-sat)
(get-proof)
(exit)
