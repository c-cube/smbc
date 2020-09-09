
(prover
  (name smbc)
  (cmd "ulimit -t $timeout; $cur_dir/../smbc --timeout $timeout $file")
  (unsat "^UNSAT")
  (sat "^SAT")
  (unknown "UNKNOWN")
  (timeout "TIMEOUT"))

(dir
  (path $cur_dir/)
  (pattern ".*.smt2")
  (expect (const unknown)))
