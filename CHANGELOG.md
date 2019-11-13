# Change Log

## 0.6.1

- fixes: format error, compat with containers 2.7

## 0.6

- upgrade to msat 0.8
- upgrade to tip-parser 0.6
- remove some dead code
- make tests faster (timeout=10)
- use release mode

## 0.5

- fix(model): add a constant to unin types with empty domains
- adapt to tip-parser 0.5
- handle new `Stmt_prove` from TIP
- cleaner display of result in presence of progress bar
- add `default` case in match (makes smaller terms)
- display `theorem/countersat` if the goal is a `prove` goal

- refactor a bit AST
- add travis support
- modernize metatada: opam2 and dune

## 0.4.2

- support containers 2.0
- move to jbuilder
- small optims
- add option `--eval-under-quant`
- more stats

## 0.4.1

- bugfix related to De Bruijn indices and function extensionality

## 0.4

- quantification on datatypes/bool

- remove limited checking of models
- some bugfixes and regression tests

## 0.3.1

- compatibility with containers 1.0

## 0.3

- add flag `--check-proof` for checking SAT solver proofs
- remove parser for custom format; only keep TIP; remove .lisp from tests
- less accurate detection of incomplete expansions (without unsat-cores)
- bugfixes in uninterpreted types
- detect some evaluation loops with a `term_being_evaled` field
- internal notion of `undefined` for `asserting`, loops, and selectors
- simple prefix skolemization for `assert` axioms
- add `asserting` construct
- delay a bit combinatorial explosion for HO functions
- support for HO unknowns
- allow quantification over booleans, translated as conjunction/disjunction
- better error message for HO metas
- add support for selectors

