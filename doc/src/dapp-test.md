# `hevm dapp-test`

```
Usage: hevm dapp-test [--json-file STRING] [--dapp-root STRING] [--debug]
                      [--jsontrace] [--fuzz-runs INT] [--depth INT]
                      [--replay (TEXT,BYTESTRING)] [--rpc TEXT] [--verbose INT]
                      [--coverage] [--state STRING] [--cache STRING]
                      [--match STRING] [--cov-match STRING] [--solver TEXT]
                      [--smtdebug] [--ffi] [--smttimeout INTEGER]
                      [--max-iterations INTEGER] [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --json-file STRING       Filename or path to dapp build output (default:
                           out/*.solc.json)
  --dapp-root STRING       Path to dapp project root directory (default: . )
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
  --solver TEXT            Used SMT solver: z3 (default) or cvc4
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

Run any ds-test testing functions. Run under the hood whenever `dapp test` or `dapp debug` is called. Testing functions prefixed with `test` will be executed concretely. If concrete test functions have been given arguments, they will be randomly instantiated and run `--fuzz-runs` number of times. If testing functions are prefixed with `prove` they will be symbolically executed. In `--debug` mode, property based tests will not be available unless given specific arguments using `--replay`.

The `smttimeout`, `max-iterations` and `solver` options have the same semantics as in `hevm symbolic`
