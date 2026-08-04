; Source: Z3Prover/z3test regressions/smt2/fp-conversions-13.smt2
; Pin: 3929b6717d78478179234afe79c860fd8712b7be
; Copyright (c) 2015 Microsoft Corporation
(set-info :smt-lib-version 2.7)
(set-option :produce-proofs true)
(set-logic QF_BVFP)
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(assert
  (not
    (= ((_ to_fp 3 3) RTZ #b00001)
       (fp #b0 #b011 #b00))))

(check-sat)
(get-proof)
(exit)
