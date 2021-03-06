# SMBC


[![build status](https://travis-ci.org/c-cube/smbc.svg?branch=master "build status")](https://travis-ci.org/c-cube/smbc)

Experimental model finder/SMT solver for functional programming.

The underlying algorithm is described in [a 2016 paper](https://hal.inria.fr/hal-01572531).

The code is under the BSD license.

## Use

- run on a problem (timeout 30s)

  ```
  smbc examples/regex_2.smt2 -t 30
  ```

- get a list of options:

  ```
  smbc --help
  ```

- verbose mode:

  ```
  smbc examples/regex_0.smt2 --debug 2
  ```

- specify depth/depth-step:

  ```
  smbc examples/regex_0.smt2 --depth-step 3 --max-depth 200
  ```

## Build

The recommended way is to use [opam](http://opam.ocaml.org/)

```sh
opam pin 'https://github.com/c-cube/smbc.git#master'
opam install smbc
```

Or manually, using

```sh
opam install msat containers iter tip-parser
make
```

## A Few Examples

We show a few example input files for smbc, along with the result.

### examples/append.smt2

A wrong conjecture stating that `append l1 l2 = append l2 l1`
holds for every lists `l1` and `l2`.

```smt2
(declare-datatypes ()
 ((nat (s (select_s_0 nat)) (z))))
(declare-datatypes
   ()
   ((list (cons (select_cons_0 nat) (select_cons_1 list))
          (nil))))
(define-funs-rec
   ((append ((x list) (y list)) list))
   ((match x (case (cons n tail) (cons n (append tail y)))
             (case nil y))))
(assert-not
 (forall ((l1 list) (l2 list)) (= (append l1 l2) (append l2 l1))))

(check-sat)
```

Running smbc gives us a counter-example, the lists `l1 = [s _]` and `l2 = [0]`.
Note that `l1` is not fully defined, the `?nat_8` object is an unknown
that can take any value of type `nat`. Whatever its value is,
the counter-example holds because `append l1 l2 != append l2 l1`.

```
$ smbc examples/append.smt2
(result SAT :model ((val l2 (cons z nil))
                    (val l1 (cons (s ?nat_8) nil))))
```

### examples/pigeon4.smt2

An instance of the classic
[pigeon-hole problem](https://en.wikipedia.org/wiki/Pigeonhole_principle)
with 4 holes and 5 pigeons

```smt2
(declare-sort hole 0)
(declare-fun h1 () hole)
(declare-fun h2 () hole)
(declare-fun h3 () hole)
(declare-fun h4 () hole)
(declare-fun p1 () hole)
(declare-fun p2 () hole)
(declare-fun p3 () hole)
(declare-fun p4 () hole)
(declare-fun p5 () hole)
(assert
 (and
  (not (= h1 h2)) (not (= h1 h3)) (not (= h1 h4))
  (not (= h2 h3)) (not (= h2 h4)) (not (= h3 h4))))
(assert
 (and
  (not (= p1 p2)) (not (= p1 p3)) (not (= p1 p4))
  (not (= p1 p5))
  (not (= p2 p3))
  (not (= p2 p4))
  (not (= p2 p5))
  (not (= p3 p4))
  (not (= p3 p5))
  (not (= p4 p5))))
(assert
  (forall ((p hole)) (or (= p h1) (= p h2) (= p h3) (= p h4))))
(check-sat)
```

We obtain `(result UNSAT)` since there is no way of satisfying
the constraints.

## Why the name?

"Sat Modulo Bounded Checking"

(and a reference to [the awesome webcomics](http://smbc-comics.com))


## Note: Memory Profiling

```sh
opam sw 4.04.0+spacetime
make
OCAML_SPACETIME_INTERVAL=100 ./smbc.native --debug 1 --check examples/ty_infer.lisp
prof_spacetime serve spacetime-<PID> -e smbc.native
```
