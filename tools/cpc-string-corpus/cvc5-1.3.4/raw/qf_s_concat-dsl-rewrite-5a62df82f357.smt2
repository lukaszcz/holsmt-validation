; family: strings
; holsmt-expected: parser-only pass
; holsmt-expected: typecheck-only pass
; holsmt-expected: z3-oracle pass
; holsmt-expected: proof-parse unsupported proof modes require unsat input
; holsmt-expected: proof-replay unsupported proof modes require unsat input
; holsmt-expected: z3-tac pass
(set-logic QF_S)
(declare-const s String)
(assert (= (str.++ s "") s))
(check-sat)
(exit)
