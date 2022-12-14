# `hevm symbolic`

```sh
Usage: hevm symbolic [--code TEXT] [--calldata TEXT] [--address ADDR]
                     [--caller ADDR] [--origin ADDR] [--coinbase ADDR]
                     [--value W256] [--nonce W256] [--gas W256] [--number W256]
                     [--timestamp W256] [--basefee W256] [--priority-fee W256]
                     [--gaslimit W256] [--gasprice W256] [--create]
                     [--maxcodesize W256] [--difficulty W256] [--chainid W256]
                     [--rpc TEXT] [--block W256] [--state STRING]
                     [--cache STRING] [--json-file STRING] [--dapp-root STRING]
                     [--storage-model STORAGEMODEL] [--sig TEXT]
                     [--arg STRING]... [--debug] [--get-models] [--show-tree]
                     [--smttimeout NATURAL] [--max-iterations INTEGER]
                     [--solver TEXT] [--smtdebug] [--assertions [WORD256]]
                     [--ask-smt-iterations INTEGER]

Available options:
  -h,--help                Show this help text
  --code TEXT              Program bytecode
  --calldata TEXT          Tx: calldata
  --address ADDR           Tx: address
  --caller ADDR            Tx: caller
  --origin ADDR            Tx: origin
  --coinbase ADDR          Block: coinbase
  --value W256             Tx: Eth amount
  --nonce W256             Nonce of origin
  --gas W256               Tx: gas amount
  --number W256            Block: number
  --timestamp W256         Block: timestamp
  --basefee W256           Block: base fee
  --priority-fee W256      Tx: priority fee
  --gaslimit W256          Tx: gas limit
  --gasprice W256          Tx: gas price
  --create                 Tx: creation
  --maxcodesize W256       Block: max code size
  --difficulty W256        Block: difficulty
  --chainid W256           Env: chainId
  --rpc TEXT               Fetch state from a remote node
  --block W256             Block state is be fetched from
  --state STRING           Path to state repository
  --cache STRING           Path to rpc cache repository
  --json-file STRING       Filename or path to dapp build output (default: out/*.solc.json)
  --dapp-root STRING       Path to dapp project root directory (default: . )
  --storage-model STORAGEMODEL
                           Select storage model: ConcreteS, SymbolicS (default)
                           or InitialS
  --sig TEXT               Signature of types to decode / encode
  --arg STRING             Values to encode
  --debug                  Run interactively
  --get-models             Print example testcase for each execution path
  --show-tree              Print branches explored in tree view
  --smttimeout NATURAL     Timeout given to SMT solver in milliseconds (default:
                           60000)
  --max-iterations INTEGER Number of times we may revisit a particular branching
                           point
  --solver TEXT            Used SMT solver: z3 (default) or cvc5
  --smtdebug               Print smt queries sent to the solver
  --assertions [WORD256]   Comma seperated list of solc panic codes to check for
                           (default: everything except arithmetic overflow)
  --ask-smt-iterations INTEGER
                           Number of times we may revisit a particular branching
                           point before we consult the smt solver to check
                           reachability (default: 5)
```

Run a symbolic execution against the given parameters, searching for assertion violations.

Counterexamples will be returned for any reachable assertion violations. Where an assertion
violation is defined as either an execution of the invalid opcode (`0xfe`), or a revert with a
message of the form `abi.encodeWithSelector('Panic(uint256)', errCode)` with `errCode` being one of
the predefined solc assertion codes defined
[here](https://docs.soliditylang.org/en/latest/control-structures.html#panic-via-assert-and-error-via-require).

By default hevm ignores assertion violations that result from arithmetic overflow (`Panic(0x11)`),
although this behaviour can be customised via the `--assertions` flag. For example, the following
will return counterexmaples for arithmetic overflow (`0x11`) and user defined assertions (`0x01`):

```
hevm symbolic --code $CODE --assertions '[0x01, 0x11]'
```

`--debug` enters an interactive debugger where the user can navigate the full execution space.

The default value for `calldata` and `caller` are symbolic values, but can be specialized to concrete functions with their corresponding flags.

One can also specialize specific arguments to a function signature, while leaving others abstract.
If `--sig` is given, calldata is assumed to be of the form suggested by the function signature. With this flag, specific arguments can be instantiated to concrete values via the `--arg` flag.

This is best illustrated through a few examples:

Calldata specialized to the bytestring `0xa9059cbb` followed by 64 symbolic bytes:

```sh
hevm symbolic --sig "transfer(address,uint256)" --code $(<dstoken.bin-runtime)
```

Calldata specialized to the bytestring `0xa9059cbb0000000000000000000000007cfa93148b0b13d88c1dce8880bd4e175fb0dedf` followed by 32 symbolic bytes.

```sh
hevm symbolic --sig "transfer(address,uint256)" --arg 0x7cFA93148B0B13d88c1DcE8880bd4e175fb0DeDF --code $(<dstoken.bin-runtime)
```

Calldata specialized to the bytestring `0xa9059cbb` followed by 32 symbolic bytes, followed by the bytestring `0000000000000000000000000000000000000000000000000000000000000000`:

```sh
hevm symbolic --sig "transfer(address,uint256)" --arg "<symbolic>" --arg 0 --code $(<dstoken.bin-runtime)
```

If the `--get-models` flag is given, example input values will be returned for each possible execution path.
This can be useful for automatic test case generation.

The default timeout for SMT queries is no timeout. If your program is taking longer than a couple of minutes to run,
you can experiment with configuring the timeout to somewhere around 10s by doing `--smttimeout 10000`

Storage can take one of three forms, defaulting to `SymbolicS` unless `--create` is provided, in which case it defaults to `InitialS`:

- `SymbolicS`: The default value of SLOAD is a symbolic value without further constraints. SLOAD and SSTORE can operate on symbolic locations.
- `InitialS`: The default value of SLOAD is zero. SLOAD and SSTORE can operate on symbolic locations.
- `ConcreteS`: Storage defaults to zero or fetched from an rpc node if `--rpc` is provided. SLOAD or SSTOREs on symbolic locations will result in a runtime error.

`hevm` uses an eager approach for symbolic execution, meaning that it will first attempt to explore
all branches in the program (without querying the smt solver to check if they are reachable or not).
Once the full execution tree has been explored, the postcondition is checked against all leaves, and
the solver is invoked to check reachability for branches where a postcondition violation could
occur. While our tests have shown this approach to be significantly faster, when applied without
limits it would always result in infitie exploration of code involving loops, so after some
predefined number of iterations (controlled by the `--ask-smt-iterations` flag), the solver will be
invoked to check whether a given loop branch is reachable. In cases where the number of loop
iterations is known in advance, you may be able to speed up execution by setting this flag to an
appropriate value.
