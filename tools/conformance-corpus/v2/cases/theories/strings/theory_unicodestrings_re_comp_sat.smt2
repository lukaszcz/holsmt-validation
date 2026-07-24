(set-logic QF_SLIA)
(assert (= (re.comp (str.to_re "a")) (re.comp (str.to_re "a"))))
(check-sat)
