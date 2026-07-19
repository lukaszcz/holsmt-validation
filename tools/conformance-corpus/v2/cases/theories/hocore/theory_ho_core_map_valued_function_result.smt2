(set-logic HO_ALL)
(declare-fun make (Int) (-> Bool Bool))
(assert (distinct (make 0) (make 0)))
(check-sat)
