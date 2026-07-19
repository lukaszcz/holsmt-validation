(set-logic QF_UF)
(assert (=
  (lambda ((x Bool)) x)
  (lambda ((y Bool)) y)))
(check-sat)
