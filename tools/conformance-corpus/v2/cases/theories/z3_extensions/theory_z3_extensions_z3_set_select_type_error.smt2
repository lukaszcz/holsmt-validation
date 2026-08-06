(set-logic ALL)
(assert (and (select (store ((as const (Set Int)) false) 7 true) 7) (= 1 true)))
(check-sat)
