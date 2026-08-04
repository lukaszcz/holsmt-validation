; Source: Z3Prover/z3test regressions/smt2/fp-nan.smt2
; Pin: 3929b6717d78478179234afe79c860fd8712b7be
; Copyright (c) 2015 Microsoft Corporation
(set-info :smt-lib-version 2.7)
(set-logic QF_FP)
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ FloatingPoint 11 53))
(assert (= X (_ NaN 11 53)))

(check-sat)
(exit)
