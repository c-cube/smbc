# TODO and ideas

## Narrowing

- turn uninterpreted terms into datatypes isomorphic to `nat`
  * using a special value `card_τ : τ` to limit the range of `∧_τ` and `∨_τ`
    and compute domains (the domain of `τ` is the set of values `{x:τ | x <
    card_τ}`)
  * introduce the special `<` (or `≤`) defined on datatypes, used
    for symmetry-breaking too?

- conflict generalization
  (e.g. failed equalities with a meta on RHS)

- symmetry breaking
  * see if swapping metas => same term modulo =,&&
  * detect if normal forms of permuted terms (modulo symmetric operators)
    are identical (nf(perm(t)) = nf(t))
  * try to find symmetries for user defined functions (e.g. equal_nat or plus),
    by a simple inductive proof following the shape of recursive calls
    and normalization of body for every tuple of args in coverset (e.g.
    coverset(a,b) = {(0,0),(0,s(b'),(s(a'),0),(s(a'),s(b'))} for those funs)
  * builtin operator ≤ on {datatypes,prop,uninterpreted types} that evaluates
    `a ≤ b` to true using lexico ordering.
    use this for breaking symmetry, e.g. if problem is symmetric w.r.t `{c1,…,cn}`
    add constraints `c1 ≤ … ≤ cn`, preserves satisfiability

- support for selectors/testers?

- add "purely boolean expressions" (composed of connectives/Τ/⊥/literals),
  that can be normal forms (e.g. in unification)

- replace `max-depth` with number of steps (safer)

- release

- generic "parallel" operator (to be used by and, or, but also
  other functions such as +_nat — maybe if they are detected to be symmetric?)

# SMT

- reduction rules (if/case/proj/test)
- communication with SAT (set term_nf/propagations)
- other datatype rules
- main loop (including expansion of blocking stuff)
- expansion of functions
  * keep a priority queue/set of function calls to expand,
    or pick all those in unsatcore (fairness?)
  * upon expanding a function call, assert the corresponding lit,
    and add guards for sub-calls inside it (abstract control graph
    with if/case provides the guards that lead to blocked calls)
- start testing on simple examples


**FIX**:
./smbc.native --backtrace --debug 5 --check examples/uf3.smt2
(should be unsat)

