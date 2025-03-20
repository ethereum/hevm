# `hevm exec`

Run an EVM computation using specified parameters.

```plain
Usage: hevm exec [--code TEXT] [--code-file STRING] [--calldata TEXT] [--address ADDR]
                 [--caller ADDR] [--origin ADDR] [--coinbase ADDR]
                 [--value W256] [--nonce WORD64] [--gas WORD64] [--number W256]
                 [--timestamp W256] [--basefee W256] [--priority-fee W256]
                 [--gaslimit WORD64] [--gasprice W256]
                 [--maxcodesize W256] [--prev-randao W256] [--chainid W256]
                 [--trace] [--rpc TEXT] [--block W256] ...
```

Concretely execute a given EVM bytecode with the specified parameters. Minimum
required flags: either you must provide `--code` or you must both pass `--rpc`
and `--address`. For a full listing of options, see `hevm exec --help`.

If the execution returns an output, it will be written
to stdout. Exit code indicates whether the execution was successful or
errored/reverted.

## Simple example usage

```shell
$ hevm exec --code 0x647175696e6550383480393834f3 --gas 0xff
"Return: 0x647175696e6550383480393834f3"
```

Which says that given the EVM bytecode `0x647175696e6550383480393834f3`, the Ethereum
Virtual Machine will put `0x647175696e6550383480393834f3` in the RETURNDATA.

To execute a mainnet transaction:

```shell
# install seth as per
# https://github.com/makerdao/developerguides/blob/master/devtools/seth/seth-guide/seth-guide.md
$ export ETH_RPC_URL=https://mainnet.infura.io/v3/YOUR_API_KEY_HERE
$ export TXHASH=0xd2235b9554e51e8ff5b3de62039d5ab6e591164b593d892e42b2ffe0e3e4e426
hevm exec --caller $(seth tx $TXHASH from) --address $(seth tx $TXHASH to) \
    --calldata $(seth tx $TXHASH input) --rpc $ETH_RPC_URL \
    --block $(($(seth tx $TXHASH blockNumber)-1)) --gas $(seth tx $TXHASH gas)
```
