
; pigeonhole
; expect: UNSAT

(decl-ty hole)

(decl h1 hole)
(decl h2 hole)
(decl h3 hole)
(decl h4 hole)

; pigeons are directly mapped to holes
(decl p1 hole)
(decl p2 hole)
(decl p3 hole)
(decl p4 hole)
(decl p5 hole)

(assert
  (and
    (not (= h1 h2))
    (not (= h1 h3))
    (not (= h1 h4))
    (not (= h2 h3))
    (not (= h2 h4))
    (not (= h3 h4))
  ))

(assert
  (and
    (not (= p1 p2))
    (not (= p1 p3))
    (not (= p1 p4))
    (not (= p1 p5))
    (not (= p2 p3))
    (not (= p2 p4))
    (not (= p2 p5))
    (not (= p3 p4))
    (not (= p3 p5))
    (not (= p4 p5))
  ))

; list of holes is exhaustive
(assert
  (forall
    (p hole)
    (or
      (= p h1)
      (= p h2)
      (= p h3)
      (= p h4)
      )))

