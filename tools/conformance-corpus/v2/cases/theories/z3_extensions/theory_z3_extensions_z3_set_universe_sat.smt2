(set-logic ALL)
(assert (select ((as const (Set Int)) true) 7))
(check-sat)
