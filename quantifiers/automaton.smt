(define-automaton A 
	(init (forall ((x Int)) (or (q1 x) (q2 x))))
	(final (q1 q2))
	(trans (q1 ((x Int))) (a ((y Int))) (exists ((z Int)) (and (distinct x z) (q3 y))))
	(trans (q3 ((x Int))) (a ((y Int))) (forall ((z Int)) (or (= x z) (q2 y))))
)

(define-automaton B (not A))
(define-automaton C (and A B))

(check-empty C)
