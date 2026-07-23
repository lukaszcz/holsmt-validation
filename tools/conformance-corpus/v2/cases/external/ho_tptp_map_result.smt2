; family: ho
; holsmt-expected: {"cvc5-oracle": {"status": "pass"}}
(set-info :smt-lib-version 2.7)
(set-logic HO_ALL)
(set-info :source |
  TPTP-derived map-valued function benchmark, curated from the
  SMT-LIB benchmark-submission 2026 HO family.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun make (Int) (-> Bool Bool))
(assert (distinct
  (make 0)
  (lambda ((x Bool)) (@ (make 0) x))))
(check-sat)
(exit)
