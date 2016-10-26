# TODO and ideas

- conflict generalization

- symmetry breaking
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

- generic "parallel" operator (to be used by and, or, but also
  other functions such as +_nat — maybe if they are detected to be symmetric?)
