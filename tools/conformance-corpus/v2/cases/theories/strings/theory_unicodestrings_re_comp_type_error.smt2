(set-logic QF_SLIA)
(assert (= (re.comp (str.to_re "a")) "type-error"))
(check-sat)
