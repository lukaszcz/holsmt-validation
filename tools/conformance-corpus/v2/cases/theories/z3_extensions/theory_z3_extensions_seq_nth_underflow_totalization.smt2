(set-logic ALL)
(declare-const s (Seq Int))
(assert (= (seq.nth s -1) (seq.nth s -2)))
(check-sat)
