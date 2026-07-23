(set-logic HO_QF_UF)
(assert (distinct
  (lambda ((x Bool)) x)
  (lambda ((y Bool)) y)))
(check-sat)
