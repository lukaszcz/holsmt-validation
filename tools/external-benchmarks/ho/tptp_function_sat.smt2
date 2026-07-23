; family: ho
; holsmt-expected: {"cvc5-oracle": {"status": "pass"}}
(set-info :smt-lib-version 2.7)
(set-logic HO_QF_UFLIA)
(set-info :source |
  TPTP-derived function-application satisfiability control, curated from
  the SMT-LIB benchmark-submission 2026 HO family.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status sat)
(declare-const f (-> Int Int))
(assert (= (f 0) 1))
(assert (= (f 1) 2))
(check-sat)
(exit)
