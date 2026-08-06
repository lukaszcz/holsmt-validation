(set-logic ALL)
(assert (select (complement ((as const (Set Int)) false)) 7))
(check-sat)
