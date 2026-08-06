(set-logic ALL)
(assert (and (select (complement ((as const (Set Int)) false)) 7) (= 1 true)))
(check-sat)
