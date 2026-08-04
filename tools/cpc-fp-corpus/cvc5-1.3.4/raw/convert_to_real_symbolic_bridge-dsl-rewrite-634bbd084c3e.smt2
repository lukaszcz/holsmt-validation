(set-option :produce-proofs true)
(set-logic QF_FPLRA)
(declare-const x Float32)
(declare-const r Real)
(assert
  (not
    (=> (= x (_ +zero 8 24))
        (<= (+ (fp.to_real x) r) r))))
(check-sat)
(get-proof)
(exit)
