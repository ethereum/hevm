# `hevm equivalence`

```sh
Usage: hevm equivalence --code-a TEXT --code-b TEXT [--sig TEXT]
                        [--arg STRING]... [--calldata TEXT]
                        [--smttimeout NATURAL] [--max-iterations INTEGER]
                        [--solver TEXT] [--smtoutput] [--smtdebug]
                        [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --code-a TEXT            Bytecode of the first program
  --code-b TEXT            Bytecode of the second program
  --sig TEXT               Signature of types to decode / encode
  --arg STRING             Values to encode
  --calldata TEXT          Tx: calldata
  --smttimeout NATURAL     Timeout given to SMT solver in seconds (default: 300)
  --max-iterations INTEGER Number of times we may revisit a particular branching
                           point
  --solver TEXT            Used SMT solver: z3 (default) or cvc5
  --smtoutput              Print verbose smt output
  --smtdebug               Print smt queries sent to the solver
  --ask-smt-iterations INTEGER
                           Number of times we may revisit a particular branching
                           point before we consult the smt solver to check
                           reachability (default: 5)
```

Symbolically execute both the code given in `--code-a` and `--code-b` and try to prove equivalence between their outputs and storages.

If `--sig` is given, calldata is assumed to take the form of the function given.
If left out, calldata is a fully abstract buffer of at most 256 bytes.

