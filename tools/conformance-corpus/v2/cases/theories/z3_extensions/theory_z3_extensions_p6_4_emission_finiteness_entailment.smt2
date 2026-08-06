(set-logic HO_ALL)
(assert (and (= (set.card (set.singleton 7)) 1)
             (= (bag.card (bag 7 2)) 2)))
(check-sat)
