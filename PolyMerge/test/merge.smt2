(set-logic QF_LRA)
(declare-fun xA () Real)
(declare-fun xB () Real)
(assert (and 
(<= (+ xA xB) 2)
(>= (+ xA 2) xB) 
(>= xB 0)
))
(assert (or (> xA 1) (<= xA 1)))
(assert (or (> xB 1) (<= xB 1)))
(assert (or (> xA 0) (<= xA 0)))
(assert (or (> xA (- 1)) (<= xA (- 1))))
(check-sat)
(exit)
