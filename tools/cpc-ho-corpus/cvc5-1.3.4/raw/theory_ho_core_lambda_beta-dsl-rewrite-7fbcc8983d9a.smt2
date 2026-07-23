(set-logic HO_QF_UFLIA)
(assert (distinct
  (let ((f (lambda ((x Int)) (+ x 1)))) (f 2))
  3))
(check-sat)
