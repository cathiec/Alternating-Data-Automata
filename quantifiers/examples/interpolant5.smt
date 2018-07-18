(set-option :produce-interpolants true)

(declare-fun p1 ((Int)) Bool)
(declare-fun p2 ((Int)) Bool)
(declare-fun p3 ((Int)) Bool)

(declare-fun q1 ((Int) (Int)) Bool)
(declare-fun q2 ((Int) (Int)) Bool)
(declare-fun q3 ((Int) (Int)) Bool)

(declare-fun p1_0 ((Int)) Bool)
(declare-fun p2_1 ((Int)) Bool)
(declare-fun p2_2 ((Int)) Bool)
(declare-fun p3_2 ((Int)) Bool)
(declare-fun p2_3 ((Int)) Bool)
(declare-fun p3_3 ((Int)) Bool)
(declare-fun p2_4 ((Int)) Bool)
(declare-fun p3_4 ((Int)) Bool)
(declare-fun p2_5 ((Int)) Bool)
(declare-fun p3_5 ((Int)) Bool)
(declare-fun p2_6 ((Int)) Bool)
(declare-fun p3_6 ((Int)) Bool)

(declare-fun q1_0 ((Int) (Int)) Bool)
(declare-fun q2_1 ((Int) (Int)) Bool)
(declare-fun q2_2 ((Int) (Int)) Bool)
(declare-fun q3_2 ((Int) (Int)) Bool)
(declare-fun q2_3 ((Int) (Int)) Bool)
(declare-fun q3_3 ((Int) (Int)) Bool)
(declare-fun q2_4 ((Int) (Int)) Bool)
(declare-fun q3_4 ((Int) (Int)) Bool)
(declare-fun q2_5 ((Int) (Int)) Bool)
(declare-fun q3_5 ((Int) (Int)) Bool)
(declare-fun q2_6 ((Int) (Int)) Bool)
(declare-fun q3_6 ((Int) (Int)) Bool)

(declare-const x_0 Int)
(declare-const x_1 Int)
(declare-const x_2 Int)
(declare-const x_3 Int)
(declare-const x_4 Int)
(declare-const x_5 Int)
(declare-const x_6 Int)

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
	(forall ((y Int)) (implies (p2_3 y) (or (and (= x_4 (+ y 1)) (p2_4 x_4)) (and (= x_4 y) (p3_4 x_4)))))
	(forall ((y Int)) (implies (p3_3 y) false))
	(forall ((y1 Int) (y2 Int)) (implies (q2_3 y1 y2) (forall ((y Int)) (and (or (distinct x_4 y2) (distinct y (+ y2 1)) (q2_4 x_4 y)) (or (distinct x_4 y1) (distinct y y2) (q3_4 x_4 y))))))
	(forall ((y1 Int) (y2 Int)) (implies (q3_3 y1 y2) false))
)
(and
	(forall ((y Int)) (implies (p2_4 y) (or (and (= x_5 (+ y 1)) (p2_5 x_5)) (and (= x_5 y) (p3_5 x_5)))))
	(forall ((y Int)) (implies (p3_4 y) false))
	(forall ((y1 Int) (y2 Int)) (implies (q2_4 y1 y2) (forall ((y Int)) (and (or (distinct x_5 y2) (distinct y (+ y2 1)) (q2_5 x_5 y)) (or (distinct x_5 y1) (distinct y y2) (q3_5 x_5 y))))))
	(forall ((y1 Int) (y2 Int)) (implies (q3_4 y1 y2) false))
)
(and
	(forall ((y Int)) (implies (p2_5 y) (or (and (= x_6 (+ y 1)) (p2_6 x_6)) (and (= x_6 y) (p3_6 x_6)))))
	(forall ((y Int)) (implies (p3_5 y) false))
	(forall ((y1 Int) (y2 Int)) (implies (q2_5 y1 y2) (forall ((y Int)) (and (or (distinct x_6 y2) (distinct y (+ y2 1)) (q2_6 x_6 y)) (or (distinct x_6 y1) (distinct y y2) (q3_6 x_6 y))))))
	(forall ((y1 Int) (y2 Int)) (implies (q3_5 y1 y2) false))
)
(and
	(forall ((y Int)) (implies (p2_6 y) false))
	(forall ((y1 Int) (y2 Int)) (implies (q3_6 y1 y2) false))
))

;; checking entailment between interpolants

(define-fun I1 () Bool
 (exists ((%0 Int))
  (! (and (p2 %0)
          (forall ((%1 Int))
            (! (let ((a!1 (not (= (+ %0 (* (- 1) %1)) (- 1)))))
                 (or (q2 %0 %1) a!1))
               :qid itp)))
     :qid itp)) 
)

(define-fun I2 () Bool
 (exists ((%0 Int))
  (! (forall ((%1 Int))
       (! (exists ((%2 Int))
            (! (let ((a!1 (not (forall ((y Int))
                                 (! (not (p3 y)) :pattern ((p3 y))))))
                     (a!2 (not (= (+ %0 (* (- 1) %1)) (- 1))))
                     (a!3 (not (or (not (= %0 %2)) (not (= %1 %0)) (q3 %0 %1)))))
               (let ((a!4 (or (not (or a!2 (q2 %0 %1))) a!3)))
                 (and (or (p2 %0) a!1) (or (not a!4) a!1))))
               :qid itp))
          :qid itp))
     :qid itp))
)

(define-fun I3 () Bool
 (exists ((%0 Int))
  (! (let ((a!1 (not (forall ((y Int)) (! (not (p3 y)) :pattern ((p3 y)))))))
     (let ((a!2 (or (and (or (p2 %0) a!1) (q2 %0 (+ 1 %0))) a!1)))
       (and a!2 (or (p2 %0) a!1))))
     :qid itp))
)

(define-fun I4 () Bool
 (exists ((%0 Int) (%1 Int))
  (! (let ((a!1 (not (forall ((y Int)) (! (not (p3 y)) :pattern ((p3 y)))))))
     (let ((a!2 (or (and (or (p2 %1) a!1) (q2 %1 (+ 2 %0))) a!1)))
     (let ((a!3 (and (<= (- 1) (+ %0 (* (- 1) %1)))
                     (<= 1 (+ (* (- 1) %0) %1))
                     a!2
                     (or (p2 %1) a!1))))
     (let ((a!4 (or (and (or a!3 a!1) (or (p2 %1) a!1)) a!1)))
       (and a!4 (or (p2 %1) a!1))))))
     :qid itp))
)

; I2 => I1
; (assert (and I2 (not I1)))

; I3 => I2
; (assert (and I3 (not I2)))

; I4 => I3
; (assert (and I4 (not I3)))

; I2 => I4
(assert (and I2 (not I4)))

(check-sat)