# `hevm exec`

Run an EVM computation using specified parameters, using an interactive debugger when `--debug` flag is given.

```sh
Usage: hevm exec [--code TEXT] [--calldata TEXT] [--address ADDR]
                 [--caller ADDR] [--origin ADDR] [--coinbase ADDR]
                 [--value W256] [--nonce W256] [--gas W256]
                 [--number W256] [--timestamp W256] [--gaslimit W256]
                 [--gasprice W256] [--create] [--maxcodesize W256]
                 [--prevrandao W256] [--debug] [--state STRING] [--rpc TEXT]
                 [--block W256] [--json-file STRING]
```

Minimum required flags:

`--code` or (`--rpc` and `--address`).

If the execution returns an output, it will be written to stdout.

Exit code indicates whether the execution was successful or errored/reverted.

Simple example usage:

```sh
hevm exec --code 0x647175696e6550383480393834f3 --gas 0xff
```

Debug a mainnet transaction (older transactions require archive node):

```sh
export ETH_RPC_URL=https://mainnet.infura.io/v3/YOUR_API_KEY_HERE
export TXHASH=0xd2235b9554e51e8ff5b3de62039d5ab6e591164b593d892e42b2ffe0e3e4e426
hevm exec --caller $(seth tx $TXHASH from) --address $(seth tx $TXHASH to) --calldata $(seth tx $TXHASH input) --rpc $ETH_RPC_URL --block $(($(seth tx $TXHASH blockNumber)-1)) --gas $(seth tx $TXHASH gas) --debug
```

If `--state` is provided, hevm will load and save state to the directory provided. Git is used as a storage model, with each hevm run creating a new commit. The directory provided must be a non empty git repository. After a run you can see the state diff by simply looking at the commit (for example `git show HEAD`).

```sh
mkdir mystate
cd mystate && git init && git commit --allow-empty -m "init" && cd ..
hevm exec --code 0x600160015500 --state mystate --gas 0xffffff
cd mystate && git show HEAD
```

