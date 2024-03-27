# `hevm exec`

Run an EVM computation using specified parameters, using an interactive debugger when `--debug` flag is given.

```
Usage: hevm exec [--code TEXT] [--calldata TEXT] [--address ADDR]
                 [--caller ADDR] [--origin ADDR] [--coinbase ADDR]
                 [--value W256] [--nonce WORD64] [--gas WORD64] [--number W256]
                 [--timestamp W256] [--basefee W256] [--priority-fee W256]
                 [--gaslimit WORD64] [--gasprice W256] [--create]
                 [--maxcodesize W256] [--prev-randao W256] [--chainid W256]
                 [--debug] [--trace] [--rpc TEXT] [--block W256] [--root STRING]
                 [--project-type PROJECTTYPE]

Available options:
  -h,--help                Show this help text
  --code TEXT              Program bytecode
  --calldata TEXT          Tx: calldata
  --address ADDR           Tx: address
  --caller ADDR            Tx: caller
  --origin ADDR            Tx: origin
  --coinbase ADDR          Block: coinbase
  --value W256             Tx: Eth amount
  --nonce WORD64           Nonce of origin
  --gas WORD64             Tx: gas amount
  --number W256            Block: number
  --timestamp W256         Block: timestamp
  --basefee W256           Block: base fee
  --priority-fee W256      Tx: priority fee
  --gaslimit WORD64        Tx: gas limit
  --gasprice W256          Tx: gas price
  --create                 Tx: creation
  --maxcodesize W256       Block: max code size
  --prev-randao W256       Block: prevRandao
  --chainid W256           Env: chainId
  --debug                  Debug printing of internal behaviour
  --trace                  Dump trace
  --rpc TEXT               Fetch state from a remote node
  --block W256             Block state is be fetched from
  --root STRING            Path to project root directory (default: . )
  --project-type PROJECTTYPE
                           Is this a Foundry or DappTools project (default:
                           Foundry)
```

Minimum required flags: either you must provide `--code` or you must both pass
`--rpc` and `--address`. 

If the execution returns an output, it will be written
to stdout. Exit code indicates whether the execution was successful or
errored/reverted.

Simple example usage:

```
hevm exec --code 0x647175696e6550383480393834f3 --gas 0xff
"Return: 0x647175696e6550383480393834f3"
```

Which says that given the EVM bytecode `0x647175696e6550383480393834f3`, the Ethereum
Virtual Machine will put `0x647175696e6550383480393834f3` in the RETURNDATA.

To execute a mainnet transaction:

```
# install seth as per
# https://github.com/makerdao/developerguides/blob/master/devtools/seth/seth-guide/seth-guide.md
$ export ETH_RPC_URL=https://mainnet.infura.io/v3/YOUR_API_KEY_HERE
$ export TXHASH=0xd2235b9554e51e8ff5b3de62039d5ab6e591164b593d892e42b2ffe0e3e4e426
hevm exec --caller $(seth tx $TXHASH from) --address $(seth tx $TXHASH to) \
    --calldata $(seth tx $TXHASH input) --rpc $ETH_RPC_URL \
    --block $(($(seth tx $TXHASH blockNumber)-1)) --gas $(seth tx $TXHASH gas)
```
