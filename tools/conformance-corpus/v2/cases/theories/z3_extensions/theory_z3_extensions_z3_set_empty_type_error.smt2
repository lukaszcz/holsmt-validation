(set-logic ALL)
(assert (and (not (select ((as const (Set Int)) false) 7)) (= 1 true)))
(check-sat)
