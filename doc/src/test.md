# `hevm test`

```
Usage: hevm test [--root STRING] [--project-type PROJECTTYPE] [--rpc TEXT]
                 [--number W256] [--coverage] [--match STRING]
                 [--solver TEXT] [--num-solvers NATURAL] [--smtdebug] [--debug]
                 [--trace] [--ffi] [--smttimeout NATURAL]
                 [--max-iterations INTEGER]
                 [--loop-detection-heuristic LOOPHEURISTIC]
                 [--abstract-arithmetic] [--abstract-memory]
                 [--num-cex-fuzz INTEGER] [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --root STRING            Path to project root directory (default: . )
  --project-type PROJECTTYPE Foundry or CombinedJSON project
  --rpc TEXT               Fetch state from a remote node
  --number W256            Block: number
  --coverage               Coverage analysis
  --match STRING           Test case filter - only run methods matching regex
  --solver TEXT            Used SMT solver: z3 (default), cvc5, or bitwuzla
  --num-solvers NATURAL    Number of solver instances to use (default: number of
                           cpu cores)
  --smtdebug               Print smt queries sent to the solver
  --debug                  Debug printing of internal behaviour
  --trace                  Dump trace
  --ffi                    Allow the usage of the hevm.ffi() cheatcode (WARNING:
                           this allows test authors to execute arbitrary code on
                           your machine)
  --smttimeout NATURAL     Timeout given to SMT solver in seconds (default: 300)
  --max-iterations INTEGER Number of times we may revisit a particular branching
                           point. Default is 5. Setting to -1 allows infinite looping
  --loop-detection-heuristic LOOPHEURISTIC
                           Which heuristic should be used to determine if we are
                           in a loop: StackBased (default) or Naive
                           (default: StackBased)
  --num-cex-fuzz INTEGER   Number of fuzzing tries to do to generate a
                           counterexample (default: 3) (default: 3)
  --ask-smt-iterations INTEGER
                           Number of times we may revisit a particular branching
                           point before we consult the smt solver to check
                           reachability (default: 1) (default: 1)
```

`hevm test` executes all solidity unit tests that make use of the `std-test` assertion library
(a.k.a [Foundry tests](https://book.getfoundry.sh/forge/forge-std)). It
supports both foundry based (the default) and [dapptools](https://dapp.tools/) based projects.

A more detailed introduction to symbolic unit tests with `hevm` can be found
[here](https://fv.ethereum.org/2020/12/11/symbolic-execution-with-std-test/). An
overview of using `std-test` for solidity testing can be found in the [foundry
book](https://book.getfoundry.sh/forge/tests).
