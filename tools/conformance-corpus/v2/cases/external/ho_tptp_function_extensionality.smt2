; family: ho
; holsmt-expected: {"cvc5-oracle": {"status": "pass"}, "z3-tac": {"status": "pass"}}
(set-info :smt-lib-version 2.7)
(set-logic HO_UF)
(set-info :source |
  TPTP-derived function extensionality benchmark, curated from the
  SMT-LIB benchmark-submission 2026 HO family.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)
(declare-const f (-> Bool Bool))
(declare-const g (-> Bool Bool))
(assert (forall ((x Bool)) (= (f x) (g x))))
(assert (distinct
  (lambda ((x Bool)) (f x))
  (lambda ((x Bool)) (g x))))
(check-sat)
(exit)
