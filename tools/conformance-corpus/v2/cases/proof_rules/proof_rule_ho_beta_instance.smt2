(set-option :produce-proofs true)
(set-logic ALL)
(declare-const k Int)
(assert (distinct
  (select (lambda ((x Int)) (+ x k)) 7)
  (+ 7 k)))
(check-sat)
(get-proof)
