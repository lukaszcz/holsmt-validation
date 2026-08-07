(set-logic ALL)
(declare-const s (Seq Int))
(assert (= (seq.nth s (seq.len s)) (seq.nth s (+ (seq.len s) 1))))
(check-sat)
