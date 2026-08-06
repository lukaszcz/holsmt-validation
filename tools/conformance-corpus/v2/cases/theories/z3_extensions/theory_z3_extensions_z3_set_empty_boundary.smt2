(set-logic ALL)
(assert (not (select ((as const (Set Int)) false) 7)))
(check-sat)
