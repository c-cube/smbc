; SAT

; courtesy of Koen Classen and Dan Rosen

; define a sudoku using chained lists and Peano numbers,
; then solve a particular Sudoku using the
; function that checks if an assignment is a solution


(declare-datatypes ()
  ((list6 (Nil6) (Cons6 (Cons_06 Bool) (Cons_16 list6)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Cell (C1) (C2) (C3) (C4) (C5) (C6) (C7) (C8) (C9))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Cell)))))
(declare-datatypes ()
  ((Pair2 (Pair23 (first2 Maybe) (second2 Maybe)))))
(declare-datatypes ()
  ((list4 (Nil3) (Cons3 (Cons_03 Pair2) (Cons_13 list4)))))
(declare-datatypes ()
  ((list2 (Nil4) (Cons4 (Cons_04 Maybe) (Cons_14 list2)))))
(declare-datatypes ()
  ((Pair (Pair22 (first list2) (second list2)))))
(declare-datatypes ()
  ((list3 (Nil2) (Cons2 (Cons_02 Pair) (Cons_12 list3)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 list2) (Cons_1 list)))))
(declare-datatypes () ((Sudoku (Sudoku2 (Sudoku_0 list)))))
(declare-datatypes ()
  ((list5 (Nil5) (Cons5 (Cons_05 Cell) (Cons_15 list5)))))
(define-fun-rec
  zip2
    ((x list2) (y list2)) list4
    (match x
      (case Nil4 Nil3)
      (case (Cons4 z x2)
        (match y
          (case Nil4 Nil3)
          (case (Cons4 x3 x4) (Cons3 (Pair23 z x3) (zip2 x2 x4)))))))
(define-fun-rec
  zip
    ((x list) (y list)) list3
    (match x
      (case Nil Nil2)
      (case (Cons z x2)
        (match y
          (case Nil Nil2)
          (case (Cons x3 x4) (Cons2 (Pair22 z x3) (zip x2 x4)))))))
(define-fun-rec
  transpose3
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z)
        (match y
          (case Nil4 (transpose3 z))
          (case (Cons4 x2 t) (Cons t (transpose3 z)))))))
(define-fun-rec
  transpose2
    ((x list)) list2
    (match x
      (case Nil Nil4)
      (case (Cons y z)
        (match y
          (case Nil4 (transpose2 z))
          (case (Cons4 h x2) (Cons4 h (transpose2 z)))))))
(define-fun-rec
  transpose
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y xss)
        (match y
          (case Nil4 (transpose xss))
          (case (Cons4 z xs)
            (Cons (Cons4 z (transpose2 xss))
              (transpose (Cons xs (transpose3 xss)))))))))
(define-fun-rec
  take
    ((x Nat) (y list2)) list2
    (match x
      (case Z Nil4)
      (case (S z)
        (match y
          (case Nil4 Nil4)
          (case (Cons4 x2 x3) (Cons4 x2 (take z x3)))))))
(define-fun rows ((x Sudoku)) list (match x (case (Sudoku2 y) y)))
(define-fun n9 () Nat (S (S (S (S (S (S (S (S (S Z))))))))))
(define-fun n6 () Nat (S (S (S (S (S (S Z)))))))
(define-fun n3 () Nat (S (S (S Z))))
(define-fun-rec
  length2
    ((x list2)) Nat
    (match x
      (case Nil4 Z)
      (case (Cons4 y xs) (S (length2 xs)))))
(define-fun-rec
  length
    ((x list)) Nat
    (match x
      (case Nil Z)
      (case (Cons y xs) (S (length xs)))))
(define-fun-rec
  isOkayBlock2
    ((x list2)) list5
    (match x
      (case Nil4 Nil5)
      (case (Cons4 y z)
        (match y
          (case Nothing (isOkayBlock2 z))
          (case (Just n) (Cons5 n (isOkayBlock2 z)))))))
(define-fun
  isJust
    ((x Maybe)) Bool
    (match x
      (case Nothing false)
      (case (Just y) true)))
(define-funs-rec
  ((isSolved3 ((x list) (y list2)) list6)
   (isSolved2 ((x list)) list6))
  ((match y
     (case Nil4 (isSolved2 x))
     (case (Cons4 z x2) (Cons6 (isJust z) (isSolved3 x x2))))
   (match x
     (case Nil Nil6)
     (case (Cons y z) (isSolved3 z y)))))
(define-fun-rec
  equal
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z
        (match y
          (case Z true)
          (case (S z) false)))
      (case (S x2)
        (match y
          (case Z false)
          (case (S y2) (equal x2 y2))))))
(define-fun-rec
  isSudoku2
    ((x list)) list6
    (match x
      (case Nil Nil6)
      (case (Cons y z) (Cons6 (equal (length2 y) n9) (isSudoku2 z)))))
(define-fun
  eqCell
    ((x Cell) (y Cell)) Bool
    (match x
      (case C1
        (match y
          (case default false)
          (case C1 true)))
      (case C2
        (match y
          (case default false)
          (case C2 true)))
      (case C3
        (match y
          (case default false)
          (case C3 true)))
      (case C4
        (match y
          (case default false)
          (case C4 true)))
      (case C5
        (match y
          (case default false)
          (case C5 true)))
      (case C6
        (match y
          (case default false)
          (case C6 true)))
      (case C7
        (match y
          (case default false)
          (case C7 true)))
      (case C8
        (match y
          (case default false)
          (case C8 true)))
      (case C9
        (match y
          (case default false)
          (case C9 true)))))
(define-funs-rec
  ((isSolutionOf3 ((x list3) (y list4)) list6)
   (isSolutionOf2 ((x list3)) list6))
  ((match y
     (case Nil3 (isSolutionOf2 x))
     (case (Cons3 z x2)
       (let ((x3 (isSolutionOf3 x x2)))
         (match z
           (case (Pair23 x4 x5)
             (match x4
               (case Nothing x3)
               (case (Just n1)
                 (match x5
                   (case Nothing x3)
                   (case (Just n2)
                     (Cons6 (eqCell n1 n2) (isSolutionOf3 x x2)))))))))))
   (match x
     (case Nil2 Nil6)
     (case (Cons2 y z)
       (match y
         (case (Pair22 row1 row2) (isSolutionOf3 z (zip2 row1 row2))))))))
(define-fun-rec
  elem
    ((x Cell) (y list5)) Bool
    (match y
      (case Nil5 false)
      (case (Cons5 z ys) (or (eqCell x z) (elem x ys)))))
(define-fun-rec
  unique
    ((x list5)) Bool
    (match x
      (case Nil5 true)
      (case (Cons5 y xs) (and (not (elem y xs)) (unique xs)))))
(define-fun isOkayBlock ((x list2)) Bool (unique (isOkayBlock2 x)))
(define-fun-rec
  isOkay2
    ((x list)) list6
    (match x
      (case Nil Nil6)
      (case (Cons y z) (Cons6 (isOkayBlock y) (isOkay2 z)))))
(define-fun-rec
  drop
    ((x Nat) (y list2)) list2
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Nil4 Nil4)
          (case (Cons4 x2 x3) (drop z x3))))))
(define-fun
  difficult
    () Sudoku
    (Sudoku2
      (Cons
        (Cons4 (Just C8)
          (Cons4 Nothing
            (Cons4 Nothing
              (Cons4 Nothing
                (Cons4 Nothing
                  (Cons4 Nothing
                    (Cons4 Nothing (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
        (Cons
          (Cons4 Nothing
            (Cons4 Nothing
              (Cons4 (Just C3)
                (Cons4 (Just C6)
                  (Cons4 Nothing
                    (Cons4 Nothing
                      (Cons4 Nothing (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
          (Cons
            (Cons4 Nothing
              (Cons4 (Just C7)
                (Cons4 Nothing
                  (Cons4 Nothing
                    (Cons4 (Just C9)
                      (Cons4 Nothing
                        (Cons4 (Just C2) (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
            (Cons
              (Cons4 Nothing
                (Cons4 (Just C5)
                  (Cons4 Nothing
                    (Cons4 Nothing
                      (Cons4 Nothing
                        (Cons4 (Just C7)
                          (Cons4 Nothing (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
              (Cons
                (Cons4 Nothing
                  (Cons4 Nothing
                    (Cons4 Nothing
                      (Cons4 Nothing
                        (Cons4 (Just C4)
                          (Cons4 (Just C5)
                            (Cons4 (Just C7) (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
                (Cons
                  (Cons4 Nothing
                    (Cons4 Nothing
                      (Cons4 Nothing
                        (Cons4 (Just C1)
                          (Cons4 Nothing
                            (Cons4 Nothing
                              (Cons4 Nothing (Cons4 (Just C3) (Cons4 Nothing Nil4)))))))))
                  (Cons
                    (Cons4 Nothing
                      (Cons4 Nothing
                        (Cons4 (Just C1)
                          (Cons4 Nothing
                            (Cons4 Nothing
                              (Cons4 Nothing
                                (Cons4 Nothing (Cons4 (Just C6) (Cons4 (Just C8) Nil4)))))))))
                    (Cons
                      (Cons4 Nothing
                        (Cons4 Nothing
                          (Cons4 (Just C8)
                            (Cons4 (Just C5)
                              (Cons4 Nothing
                                (Cons4 Nothing
                                  (Cons4 Nothing (Cons4 (Just C1) (Cons4 Nothing Nil4)))))))))
                      (Cons
                        (Cons4 Nothing
                          (Cons4 (Just C9)
                            (Cons4 Nothing
                              (Cons4 Nothing
                                (Cons4 Nothing
                                  (Cons4 Nothing
                                    (Cons4 (Just C4) (Cons4 Nothing (Cons4 Nothing Nil4)))))))))
                        Nil)))))))))))
(define-fun-rec
  blocks3x34
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z) (Cons (drop n6 y) (blocks3x34 z)))))
(define-fun-rec
  blocks3x33
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z) (Cons (take n3 (drop n3 y)) (blocks3x33 z)))))
(define-fun-rec
  blocks3x32
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z) (Cons (take n3 y) (blocks3x32 z)))))
(define-fun-rec
  blocks2
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z) (Cons y (blocks2 z)))))
(define-fun-rec
  append2
    ((x list2) (y list2)) list2
    (match x
      (case Nil4 y)
      (case (Cons4 z xs) (Cons4 z (append2 xs y)))))
(define-fun-rec
  group3
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons xs1 y)
        (match y
          (case Nil Nil)
          (case (Cons xs2 z)
            (match z
              (case Nil Nil)
              (case (Cons xs3 xss)
                (Cons (append2 xs1 (append2 xs2 xs3)) (group3 xss)))))))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-fun
  blocks3x3
    ((x Sudoku)) list
    (append (group3 (blocks3x32 (rows x)))
      (append (group3 (blocks3x33 (rows x)))
        (group3 (blocks3x34 (rows x))))))
(define-fun
  blocks
    ((x Sudoku)) list
    (append (blocks2 (rows x))
      (append (blocks2 (transpose (rows x))) (blocks3x3 x))))
(define-fun-rec
  and2
    ((x list6)) Bool
    (match x
      (case Nil6 true)
      (case (Cons6 y xs) (and y (and2 xs)))))
(define-fun isOkay ((x Sudoku)) Bool (and2 (isOkay2 (blocks x))))
(define-fun
  isSolved
    ((x Sudoku)) Bool
    (match x (case (Sudoku2 sud) (and2 (isSolved2 sud)))))
(define-fun
  isSolutionOf
    ((x Sudoku) (y Sudoku)) Bool
    (and (isSolved x)
      (and (isOkay x) (and2 (isSolutionOf2 (zip (rows x) (rows y)))))))
(define-fun
  isSudoku
    ((x Sudoku)) Bool
    (match x
      (case (Sudoku2 sud)
        (and (equal (length sud) n9) (and2 (isSudoku2 sud))))))
(assert-not
  (forall ((s Sudoku))
    (or (not (isSudoku s)) (not (isSolutionOf s difficult)))))
(check-sat)
