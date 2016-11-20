# TODO and ideas

## Now

- experiment to remove uninterpreted types in core, and replace them
  with the following (amounts to replacing finite model finding with
  computational narrowing)
  * For a type τ, `Conv`-time declarations of:
    + `τ = 0 | S card_τ` types
    + a `card_τ` value of type `card_τ` with constraint `card_τ != 0`
    + two recursive function `forall_τ` and `exists_τ` (taking as param
      the `card_τ` value… or do closures support that? and some predicate `τ → prop`
      that will be applied to all elements from `0` to `card-1`)
    + (maybe) a special builtin pred `<` that can be used on all those types
      (mostly for symmetry breaking: if `a`, `b` are symmetric, add `a<b`)
  * a translation of axioms so they use `forall_τ` and `exists_τ`
  * model building that uses `card_τ` to compute the actual domain of
    the type. (the domain of `τ`
    is the set of values `{x:τ | x < card_τ}`)

## Narrowing

- discuss how to narrow HOF arguments with Koen (they can only be used
  on finite set of values, therefore simulate them by a finite dispatch
  table… or by their `app` function using already existing support
  for non-HO functions?)

- optimization of `match t with p1 -> c t1 | … | pn -> c tn`
  where `c` is the same cstor in every branch, into
  `c (match t with p1 -> t1 | … | pn -> tn)`. This should be
  done at preprocessing, same as compilation of simultaneous matches.
  * no need to worry about duplicate sub-computations, they will be
   shared anyway
  * allows for faster failures if this is to be equated with another
   constructor
  * nice special case: booleans
  * optimal in conjunction with simultaneous match. E.g., `less` would
    become
    `match x, y with
      | s x1, s y1 -> less x1 y1  | 0, s _ -> true | _, 0 -> false end`
    which fails if `y=0` immediately (instead of always having to decompose
    `x` first).
  * → even further: factor together the branches of simultaneous matching
    that return the same constructor, even if there still remains several
    branches.

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

## On Hold

- simultaneous match (make and/or/imply based on that)
  * also need to convert inputs that perform match on arguments (e.g. `less`)
    into this simultaneous match, automatically
  * keep it shallow (no deep patterns)
  * allow `default` case (to avoid explosion) AND wildcard patterns,
    which are critical for accurate explanations (implementation similar
    to current parallel and)
  * optim: if one matched term only has wildcards, remove it (irrelevant).
    This can happen as a result of other optimizations.
  * e.g, `and x y = match x,y with
     | false, _ -> false | _, false -> false | true, true -> true end`

- maybe parallel match is better than simultaneous match (more accurate
  in combination with following optim, as you can have some cases
  with nested matches and some cases in which the inner match collapses
  into one cstor; e.g. for `less`, matching on snd argument first
  will have sub-case collapse to `false` automatically).

- detect and prove (by simple induction), when possible, that some
  boolean function's argument's depth is smaller than another argument's?
  e.g. for `find` in `ty_infer`, depth of env must be ≥ depth of index
  for it to return `some`. A builtin `smaller_depth a b` would be used to
  prune early?

## SMT

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

## FIX
./smbc.native --backtrace --debug 5 --check examples/uf3.smt2
(should be unsat)

