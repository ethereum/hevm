# `hevm equivalence`

```sh
Usage: hevm equivalence --code-a TEXT --code-b TEXT [--sig TEXT]
```

Symbolically execute both the code given in `--code-a` and `--code-b` and try to prove equivalence between their outputs and storages.

If `--sig` is given, calldata is assumed to take the form of the function given.
If left out, calldata is a fully abstract buffer of at most 256 bytes.

### `hevm dapp-test`

```
Usage: hevm dapp-test [--json-file STRING] [--dapp-root STRING] [--debug]
                      [--fuzz-runs INT] [--replay (TEXT,BYTESTRING)] [--depth INT]
                      [--rpc TEXT] [--verbose INT] [--coverage] [--state STRING]
                      [--match STRING] [--smttimeout INT] [--max-iterations INT]
                      [--solver STRING] [--cache STRING] [--cov-match STRING]
```

Run any ds-test testing functions. Run under the hood whenever `dapp test` or `dapp debug` is called. Testing functions prefixed with `test` will be executed concretely. If concrete test functions have been given arguments, they will be randomly instantiated and run `--fuzz-runs` number of times. If testing functions are prefixed with `prove` they will be symbolically executed. In `--debug` mode, property based tests will not be available unless given specific arguments using `--replay`.

The `smttimeout`, `max-iterations` and `solver` options have the same semantics as in `hevm symbolic`

