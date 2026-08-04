; holsmt-expected: {"typecheck-only": {"status": "pass"}}
(set-logic QF_FP)
(assert
  (fp.isZero
    (fp.add RNE (_ +zero 3 5) (_ -zero 3 5))))
(check-sat)
(exit)
