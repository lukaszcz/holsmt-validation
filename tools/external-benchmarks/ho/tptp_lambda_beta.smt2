; family: ho
; holsmt-expected: {"cvc5-oracle": {"status": "pass"}, "z3-tac": {"status": "pass"}}
(set-info :smt-lib-version 2.7)
(set-logic HO_QF_UFLIA)
(set-info :source |
  TPTP-derived beta-reduction benchmark, curated from the
  SMT-LIB benchmark-submission 2026 HO family.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)
(assert (distinct
  (let ((successor (lambda ((x Int)) (+ x 1)))) (successor 41))
  42))
(check-sat)
(exit)
