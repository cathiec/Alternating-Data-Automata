(set-option :produce-interpolants true)     

(declare-fun q1 ((Int)) Bool)
(declare-fun q2 ((Int)) Bool)
(declare-fun q3 ((Int)) Bool)
(declare-fun q4 ((Int)) Bool)

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)

(declare-const y1 Int)
(declare-const y2 Int)
(declare-const y3 Int)
(declare-const y4 Int)

(compute-interpolant
	(q1 0)
	(forall ((y Int)) (implies (q1 y) (and (>= x1 0) (q2 (+ x1 y)))))
	(forall ((y Int)) (implies (q2 y) (and (>= x2 0) (q3 (+ x2 y)))))
	(forall ((y Int)) (implies (q3 y) (and (>= x3 0) (q4 (+ x3 y)))))
	(forall ((y Int)) (implies (q4 y) false))
)

(compute-interpolant
	(and (q1 0) (= y1 0))
	(implies (q1 y1) (and (>= x1 0) (q2 y2) (= y2 (+ y1 x1))))
	(implies (q2 y2) (and (>= x2 0) (q3 y3) (= y3 (+ y2 x2))))
	(implies (q3 y3) (and (>= x3 0) (q4 y4) (= y4 (+ y3 x3))))
	(implies (q4 y4) (< y4 0))
)