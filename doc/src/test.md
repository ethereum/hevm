# `hevm test`

```plain
Usage: hevm test [--root STRING] [--project-type PROJECTTYPE] [--rpc TEXT]
                 [--number W256] [--verb INT] [--match STRING]
                 [--solver TEXT] [--num-solvers NATURAL] ...

```

Execute all unit tests that make use of the `std-test` assertion library
a.k.a [Foundry tests](https://book.getfoundry.sh/forge/forge-std) on functions that
start with `prove_`. This command supports both Foundry- and
[Dapptools-](https://dapp.tools/)based projects. For a full listing of options,
see `hevm test --help`. For common options, see [here](./common-options.md).

## Simple example usage

If you are inside a forge project that has already been built via `forge build
--ast`, you can:

```shell
$ hevm test
Checking 1 function(s) in contract src/badvault-test.sol:BadVault
[RUNNING] prove_mytest(uint256)
   [PASS] prove_mytest(uint256)
```

To prove all function that start with `prove_` in all contracts.

## Further reading

See our
[tutorial here](std-test-tutorial.html) for more details. An overview of using
`std-test` for solidity testing can be found in the [foundry
book](https://book.getfoundry.sh/forge/tests).
