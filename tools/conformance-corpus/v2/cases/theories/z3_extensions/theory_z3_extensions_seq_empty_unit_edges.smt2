(set-logic ALL)
(assert (and (= (seq.len (as seq.empty (Seq Int))) 0) (= (seq.len (seq.unit 7)) 1) (= (seq.++ (as seq.empty (Seq Int)) (seq.unit 7)) (seq.unit 7))))
(check-sat)
