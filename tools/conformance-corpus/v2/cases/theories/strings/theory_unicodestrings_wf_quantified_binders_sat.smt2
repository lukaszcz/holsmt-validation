(set-logic ALL)
(assert (forall ((s String))
  (exists ((t String)) (= t s))))
(check-sat)
