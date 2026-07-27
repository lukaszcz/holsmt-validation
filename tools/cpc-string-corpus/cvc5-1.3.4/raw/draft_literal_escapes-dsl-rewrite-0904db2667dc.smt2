(set-logic QF_S)
(set-option :produce-proofs true)
(assert
  (not
    (and
      (= "\u0007" "\u{7}")
      (= "\u0022" """")
      (= "\u005c" "\")
      (= "\u0041\u{1f642}" "A\u{1F642}")
      (= "\u{2ffff}" "\u{2FFFF}"))))
(check-sat)
(get-proof)
(exit)
