# TODO and ideas

## Now

## Narrowing

- add `default` in matching (makes for smaller terms)

- add a `Failure` term (poison pill) that propagates through application
  and builtins, and makes the solver backtrack immediately
  if `goal -> failure`.
  This can be used to:
  * add pre/post conditions
  * forbid some branches in matches
  * enforce proper use of selectors


- remove field `term_blocking` (and special "parallel and") and use
  big-step semantics everywhere.
  Instead, evaluation should return the list of blocking unknowns that
  it met, so the SMT theory can use that directly.

- CLI flag + internal mechanism for generating `n` solutions instead
  of just one (add negation of solution to get the next one).

- [ ] no hashconsing branch:
  * reinforce a bit
  * write a better interpreter (separate program and runtime thunks)
    + `thunk =
       par_and|true|false|not|cstor(thunks)|ref(thunk*expl)|suspend(program,const,env)`
       (unknowns should only occur in suspensions, I think, since otherwise
        we can always reduce?)
    + `program = fun/match/if/value/const/switch/let/…`
      (maybe `value` should be flat and nested values would require "let")
    + `env = thunk list` (non-sparse env) or RAL
  * introduce `Term.Ref` case that forwards to another term (a pointer),
    but "carries over" on values (true/false/constructors). In other words,
    `Ref t -->_e Ref nf` when `t -->_e nf`, except when `nf = c u1…uk`
    where it becomes `Ref t -->_e c (Ref u1)…(Ref uk)`
  * `let x=t in u` should be converted into `u[x := Ref t]` where the `t`
    is shared (use an actual pointer/wrapper with
    backtrackable memoization in there?)
  * use this mechanism in literals, instead of memoizing literals themselves.
  * see https://gist.github.com/aspiwack/fd8d441734f9d4661555fb025ddead59
    for a basic implem of STG

- [ ] hashconsing branch:
  * [x] expand unknowns on the fly during computation
        (instead of computing dependencies)
  * [x] use `n`-ary functions
  * [x] fully applied cstors
  * [x] use environments and local closures instead of instantiation
    + [ ] can keep `let`, as an optim
    + [x] only create closures at points where evaluation blocks
      (or for cstor arguments, i.e. thunks)
    + [x] tag terms with "closed" flag
    + should allocate a lot less. Closures are part of identity/hashconsing
    + a closure is always closed(!)
  * design: this should be usable in a SMT

- [ ] rewriting branch:
  * remove `match` (and forall/exists?), replace by toplevel named symbols
    with shallow rewriting rules. Perform closure conversion, so that
    each symbol's definition is closed
  * see what is done in zipperposition (should be very similar)
  * notion of unification becomes stronger: `f(t_i) = cstor(u_j)` can
    reduce to the disjunction of rules `f(x) → rhs` where `rhs` has
    the same constructor as `cstor`, or is a subcall.
    + do it only when it excludes at least one case
    + fast failure: if no such rule exist!
    + possible issue: termination
  * parallel `or` critical for unification problems

- [x] memory profiling

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

- replace iterative increment of `depth` by `size`: should explore
  the search space in a much more interesting way
  * each constant `c` lazily maps to a set of literals `size(c)≤n`
    for each `n≥1`. It contains a list of such literals for which
    the constraints on `c.cases` (and those cases themselves) have been
    emitted to the SAT solver
    + NOTE: list, or just the maximum `n`? should
        satisfy the invariant that if `size(c)≤n+1` emitted, then `size(c)≤n` too
  * keep queue of constants that are not fully constrainted w.r.t current
    max size; when incrementing the max size, just re-start from the
    goal (+axioms) and update relevant constants `c` by:
    + if `c` not expanded, expand it
    + if `c` can have max size `n+k` but only constrained up to `n`, enumerate
      the possible redistribution of `n+i` among `c` sub-constants
      for each `i=1…(k-1)`. For instance, the case `c=A(c1,c2)` will
      enumerate all clauses `size(c)≤n+2 ⇒ size(c1)≤a ∧ size(c2)≤b`
      for each `{ (a,b) | a>0,b>0,a+b=n+1 }`.
    + then flag `c` as constrained for the new size.

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

- add "purely boolean expressions" (composed of connectives/Τ/⊥/literals),
  that can be normal forms (e.g. in unification)

- replace `max-depth` with number of steps (safer)

- release

- generic "parallel" operator (to be used by and, or, but also
  other functions such as +_nat — maybe if they are detected to be symmetric?)

### Fix

- model building for uninterpreted values
  `./smbc.native --debug 1 -t 30 --check examples/ty_infer2_unin.lisp --depth-step 5`

### On Hold

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

### FIX
./smbc.native --backtrace --debug 5 --check examples/uf3.smt2
(should be unsat)

