(set-logic HO_UF)
(declare-const f (-> Bool Bool))
(declare-const g (-> Bool Bool))
(assert (forall ((x Bool)) (= (f x) (g x))))
(assert (distinct
  (lambda ((x Bool)) (f x))
  (lambda ((x Bool)) (g x))))
(check-sat)
