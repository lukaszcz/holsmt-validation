(set-option :produce-proofs true)
(set-logic QF_FPLRA)
(assert
  (not
    (= ((_ to_fp 3 5) RNA
          ((_ to_fp 4 7) RNE
            (fp #b0 #b011 #b0001)))
       (fp #b0 #b011 #b0001))))
(check-sat)
(get-proof)
(exit)
