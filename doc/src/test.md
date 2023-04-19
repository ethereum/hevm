# `hevm dapp-test`

```
Usage: hevm test [--root STRING] [--project-type PROJECTTYPE] [--debug]
                 [--jsontrace] [--fuzz-runs INT] [--depth INT]
                 [--replay (TEXT,BYTESTRING)] [--rpc TEXT] [--verbose INT]
                 [--coverage] [--state STRING] [--cache STRING] [--match STRING]
                 [--cov-match STRING] [--solver TEXT] [--smtdebug] [--ffi]
                 [--smttimeout NATURAL] [--max-iterations INTEGER]
                 [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --root STRING            Path to project root directory (default: . )
  --project-type PROJECTTYPE
                           Is this a Foundry or DappTools project (default:
                           Foundry)
  --debug                  Run interactively
  --jsontrace              Print json trace output at every step
  --fuzz-runs INT          Number of times to run fuzz tests
  --depth INT              Number of transactions to explore
  --replay (TEXT,BYTESTRING)
                           Custom fuzz case to run/debug
  --rpc TEXT               Fetch state from a remote node
  --verbose INT            Append call trace: {1} failures {2} all
  --coverage               Coverage analysis
  --state STRING           Path to state repository
  --cache STRING           Path to rpc cache repository
  --match STRING           Test case filter - only run methods matching regex
  --cov-match STRING       Coverage filter - only print coverage for files
                           matching regex
  --solver TEXT            Used SMT solver: z3 (default) or cvc5
  --smtdebug               Print smt queries sent to the solver
  --ffi                    Allow the usage of the hevm.ffi() cheatcode (WARNING:
                           this allows test authors to execute arbitrary code on
                           your machine)
  --smttimeout NATURAL     Timeout given to SMT solver in seconds (default: 300)
  --max-iterations INTEGER Number of times we may revisit a particular branching
                           point
  --ask-smt-iterations INTEGER
                           Number of times we may revisit a particular branching
                           point before we consult the smt solver to check
                           reachability (default: 5)
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
