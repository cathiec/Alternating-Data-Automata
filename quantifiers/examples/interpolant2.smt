(set-option :produce-interpolants true)

(declare-fun p1_0 ((Int)) Bool)
(declare-fun p2_1 ((Int)) Bool)
(declare-fun p2_2 ((Int)) Bool)
(declare-fun p3_2 ((Int)) Bool)
(declare-fun p2_3 ((Int)) Bool)
(declare-fun p3_3 ((Int)) Bool)
(declare-fun q1_0 ((Int) (Int)) Bool)
(declare-fun q2_1 ((Int) (Int)) Bool)
(declare-fun q2_2 ((Int) (Int)) Bool)
(declare-fun q3_2 ((Int) (Int)) Bool)
(declare-fun q2_3 ((Int) (Int)) Bool)
(declare-fun q3_3 ((Int) (Int)) Bool)

(declare-const x_0 Int)
(declare-const x_1 Int)
(declare-const x_2 Int)
(declare-const x_3 Int)

(compute-interpolant
(and (p1_0 0) (q1_0 0 0))
(and
(forall ((y Int)) (implies (p1_0 y) (and (= x_1 x_0) (p2_1 x_1))))
(forall ((y1 Int) (y2 Int)) (implies (q1_0 y1 y2) (forall ((y Int)) (or (distinct x_1 x_0) (distinct y (+ x_0 1)) (q2_1 x_1 y)))))
)
(and
(forall ((y Int)) (implies (p2_1 y) (or (and (= x_2 (+ y 1)) (p2_2 x_2)) (and (= x_2 y) (p3_2 x_2)))))
(forall ((y1 Int) (y2 Int)) (implies (q2_1 y1 y2) (forall ((y Int)) (and (or (distinct x_2 y2) (distinct y (+ y2 1)) (q2_2 x_2 y)) (or (distinct x_2 y1) (distinct y y2) (q3_2 x_2 y))))))
)
(and
(forall ((y Int)) (implies (p2_2 y) (or (and (= x_3 (+ y 1)) (p2_3 x_3)) (and (= x_3 y) (p3_3 x_3)))))
(forall ((y Int)) (implies (p3_2 y) false))
(forall ((y1 Int) (y2 Int)) (implies (q2_2 y1 y2) (forall ((y Int)) (and (or (distinct x_3 y2) (distinct y (+ y2 1)) (q2_3 x_3 y)) (or (distinct x_3 y1) (distinct y y2) (q3_3 x_3 y))))))
(forall ((y1 Int) (y2 Int)) (implies (q3_2 y1 y2) false))
)
(and
(forall ((y Int)) (implies (p2_3 y) false))
(forall ((y1 Int) (y2 Int)) (implies (q3_3 y1 y2) false))
)
)
