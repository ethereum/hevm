# hevm

The `hevm` project is an implementation of the Ethereum virtual machine (EVM) made specifically for
symbolic execution, unit testing and debugging of smart contracts. The `hevm` command line program
can symbolically execute smart contracts, run unit tests, interactively debug contracts while
showing the Solidity source, or run arbitrary EVM code. Computations can be performed using local
state set up in a `dapp` testing harness, or fetched on demand from live networks using `rpc` calls.

It was originally developed as part of the [dapptools](https://github.com/dapphub/dapptools/)
project, and was forked to this repo by the formal methods team at the Ethereum Foundation in August
2022.

## Documentation

User facing documentation can be found in the [hevm book](https://hevm.dev/).

## Installation

`hevm` can be installed using nix flakes via the following command:

```
nix profile install github:ethereum/hevm
```

## Development

We use `nix` to manage project dependencies. To start hacking on hevm you should first [install
nix](https://nixos.org/download.html).

Once nix is installed you can run `nix-shell` (or `nix develop` if you use flakes) from the repo
root to enter a development shell containing all required dev dependencies. If you use
[direnv](https://direnv.net/), then you can run `direnv allow`, and the shell will be automatically
entered each time you cd in the project repo.

Once in the shell you can `cd src/hevm` and use the usual `cabal` commands to build and test hevm:

```
$ cabal build          # build the hevm library
$ cabal build exe:hevm # build the cli binary
$ cabal build test     # build the test binary

$ cabal repl           # enter a repl for the library
$ cabal repl exe:hevm  # enter a repl for the cli
$ cabal repl test      # enter a repl for the tests

$ cabal run hevm       # run the cli binary
$ cabal run test       # run the test binary

# run the cli binary with profiling enabled
$ cabal run --enable-profiling hevm -- <CLI SUBCOMMAND> +RTS -s -p -RTS

# run the test binary with profiling enabled
$ cabal run --enable-profiling test -- +RTS -s -p -RTS
```

A high level overview of the architecture can be found in [architecture.md](./architecture.md).
