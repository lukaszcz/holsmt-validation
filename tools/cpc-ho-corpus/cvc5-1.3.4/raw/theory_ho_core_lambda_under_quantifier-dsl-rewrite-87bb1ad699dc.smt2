(set-logic HO_AUFLIRA)
(assert (exists ((a Int))
  (distinct
    (lambda ((x Real)) (= x (to_real a)))
    (lambda ((y Real)) (= y (to_real a))))))
(check-sat)
