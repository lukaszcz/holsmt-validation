(set-logic ALL)
(declare-const ch Char)
(assert (= (seq.unit ch) (_ char #x61)))
(check-sat)
