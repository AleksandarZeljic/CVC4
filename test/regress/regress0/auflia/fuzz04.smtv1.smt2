(set-option :incremental false)
(set-info :status sat)
(set-logic QF_AUFLIA)
(declare-fun p1 ((Array Int Int) (Array Int Int)) Bool)
(declare-fun f1 ((Array Int Int) (Array Int Int) (Array Int Int)) (Array Int Int))
(declare-fun v3 () (Array Int Int))
(check-sat-assuming ( (p1 (f1 v3 v3 v3) (f1 v3 (f1 v3 v3 (store v3 0 0)) v3)) ))
