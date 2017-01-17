
; expect: sat

; a simple problem to test "asserting".
; we look for a list where "head (tail (tail (tail l))) = A"
; with safe versions of those

(declare-datatypes () ((ab (A)(B))))
(declare-datatypes () ((List (Cons (_hd ab)(_tail List)) (Nil))))

; safe head and tail

(define-fun head ((l List)) ab
  (asserting (_hd l) (not (= l Nil))))
(define-fun tail ((l List)) List
  (asserting (_tail l) (not (= l Nil))))

(assert-not
  (forall ((l List))
    (not (= (head (tail (tail (tail l)))) A))))
