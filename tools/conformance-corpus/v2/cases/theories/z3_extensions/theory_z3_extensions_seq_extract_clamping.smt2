(set-logic ALL)
(assert (and (= (seq.extract (seq.unit 7) -1 2) (as seq.empty (Seq Int))) (= (seq.extract (seq.unit 7) 0 99) (seq.unit 7))))
(check-sat)
