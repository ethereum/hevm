# `hevm dapp-test`

```
Usage: hevm test [--root STRING] [--project-type PROJECTTYPE] [--rpc TEXT]
                 [--verbose INT] [--coverage] [--match STRING] [--solver TEXT]
                 [--smtdebug] [--ffi] [--smttimeout NATURAL]
                 [--max-iterations INTEGER]
                 [--loop-detection-heuristic LOOPHEURISTIC]
                 [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --root STRING            Path to project root directory (default: . )
  --project-type PROJECTTYPE
                           Is this a Foundry or DappTools project (default:
                           Foundry)
  --rpc TEXT               Fetch state from a remote node
  --verbose INT            Append call trace: {1} failures {2} all
  --coverage               Coverage analysis
  --match STRING           Test case filter - only run methods matching regex
  --solver TEXT            Used SMT solver: z3 (default) or cvc5
  --num-solvers NATURAL    Number of solver instances to use (default: number of cpu cores)
  --smtdebug               Print smt queries sent to the solver
  --ffi                    Allow the usage of the hevm.ffi() cheatcode (WARNING:
                           this allows test authors to execute arbitrary code on
                           your machine)
  --smttimeout NATURAL     Timeout given to SMT solver in seconds (default: 300)
  --max-iterations INTEGER Number of times we may revisit a particular branching
                           point
  --loop-detection-heuristic LOOPHEURISTIC
                           Which heuristic should be used to determine if we are
                           in a loop: StackBased (default) or Naive
                           (default: StackBased)
  --ask-smt-iterations INTEGER
                           Number of times we may revisit a particular branching
                           point before we consult the smt solver to check
                           reachability (default: 1) (default: 1)
```

`hevm test` will execute all solidity unit tests that make use of the `DSTest` assertion library
(a.k.a "foundry tests). It supports both foundry based (the default) and dapptools based projects.

It has support for:

- unit tests (`test` prefix, no arguments)
- fuzz tests (`test` prefix, with function arguments)
- invariant tests (`invariant` prefix, with function arguments)
- symbolic tests (`prove` prefix, with function arguments)

A more detailed introduction to symbolic unit tests with `hevm` can be found [here](https://fv.ethereum.org/2020/12/11/symbolic-execution-with-ds-test/).
An overview of using ds-test for solidity testing can be found in the [foundry book](https://book.getfoundry.sh/forge/tests).
