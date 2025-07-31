# hevm
hevm is an implementation of the Ethereum virtual machine (EVM) made for
symbolic execution, equivalence checking, and (symbolic) unit testing of smart
contracts. `hevm` can symbolically execute smart contracts, perform symbolic
equivalence testing, and run arbitrary EVM code. In particular, it can run
[Forge](https://book.getfoundry.sh/forge/writing-tests) test suites in a
symbolic way, thereby being much more thorough than fuzz testing.

## Documentation & Support
User facing documentation can be found in the [hevm book](https://hevm.dev/).
We have a public matrix chat room
[here](https://matrix.to/#/%23hevm%3Amatrix.org).

## Installing via Static Binaries
Static binaries for x86 linux and macos are available for each
[release](https://github.com/ethereum/hevm/releases). These binaries expect to have `z3` installed.
You can install `z3` via your package manager, such as `apt install z3` on Ubuntu,
or `brew install z3` on macOS.

## Quick User Guide for a Forge Project
For a Forge project, you can run:
```bash
cd my-forge-project
forge clean
forge build --ast
hevm test --prefix test # will symbolically execute all tests prefixed with "test"
```

For a more comprehensive guide on how to use hevm for a Forge project, see our [Forge
std-test tutorial](https://hevm.dev/std-test-tutorial.html)

## Installing via nix
hevm nix package is available in
[nixpkgs](https://search.nixos.org/packages?channel=unstable&show=haskellPackages.hevm),
and can be installed via:
- flakes: `nix profile install nixpkgs#haskellPackages.hevm`
- legacy: `nix-env -iA haskellPackages.hevm`

hevm flake can be installed directly from the `main` branch of this repo via the following command:
```plain
nix profile install github:ethereum/hevm
```

## Development
We use `nix` to manage project dependencies. To start hacking on hevm you should first [install
nix](https://nixos.org/download.html).

Once nix is installed you can run `nix develop` from the repo root to enter a development shell
containing all required dev dependencies.

Once in the shell you can use the usual `cabal` commands to build and test hevm:
```plain
$ cabal run hevm -- test --root myproject # run the cli
$ cabal run test                          # run the tests
$ cabal repl test                         # enter the repl for the test.sh
$ cabal run ethereum-tests                # run the ethereum standard tests

# run the cli binary with profiling enabled
$ cabal run --enable-profiling hevm -- <CLI SUBCOMMAND> +RTS -s -p -RTS
```

## History
`hevm` was originally developed as part of the
[dapptools](https://github.com/dapphub/dapptools/) project, and was forked to
this repo by the formal methods team at the Ethereum Foundation in August 2022.

