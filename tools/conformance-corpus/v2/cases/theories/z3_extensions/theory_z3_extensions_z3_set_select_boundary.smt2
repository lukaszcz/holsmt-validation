(set-logic ALL)
(assert (select (store ((as const (Set Int)) false) 7 true) 7))
(check-sat)
