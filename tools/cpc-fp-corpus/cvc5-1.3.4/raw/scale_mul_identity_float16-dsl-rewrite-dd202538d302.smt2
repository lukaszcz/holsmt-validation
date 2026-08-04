(set-option :produce-proofs true)
(set-logic QF_FP)
(declare-const x Float16)
(assert
  (not
    (= (fp.mul RNE x (fp #b0 #b01111 #b0000000000)) x)))
(check-sat)
(get-proof)
(exit)
