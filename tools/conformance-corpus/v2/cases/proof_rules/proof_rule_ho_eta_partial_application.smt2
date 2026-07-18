(set-option :produce-proofs true)
(set-logic ALL)
(declare-const h (Array Int (Array Int Int)))
(declare-const a Int)
(assert (distinct
  (select h a)
  (lambda ((y Int)) (select (select h a) y))))
(check-sat)
(get-proof)
