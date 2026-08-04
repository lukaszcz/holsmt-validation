(set-option :produce-proofs true)
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 5))
(declare-const y (_ FloatingPoint 3 5))
(assert
  (not
    (= (fp.add RNE x y)
       (fp.add RNE y x))))
(check-sat)
(get-proof)
(exit)
