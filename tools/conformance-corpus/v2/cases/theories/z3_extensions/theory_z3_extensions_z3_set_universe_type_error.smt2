(set-logic ALL)
(assert (and (select ((as const (Set Int)) true) 7) (= 1 true)))
(check-sat)
