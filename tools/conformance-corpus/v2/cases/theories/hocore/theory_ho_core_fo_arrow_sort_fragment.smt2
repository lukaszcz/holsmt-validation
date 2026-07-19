(set-logic QF_LIA)
(declare-const f (-> Int Int))
(assert (= f f))
(check-sat)
