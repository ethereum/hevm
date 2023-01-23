# controlling the unit testing environment

## Cheat codes

Since Hevm is an EVM implementation mainly dedicated to testing and exploration, it features a set of `cheat codes` which can manipulate the environment in which the execution is run.

These can be accessed by calling into a contract (typically called `Hevm`) at address `0x7109709ECfa91a80626fF3989D68f67F5b1DD12D`, which implements the following methods:

- `function warp(uint x) public`
  Sets the block timestamp to `x`.

- `function roll(uint x) public`
  Sets the block number to `x`.

- `function store(address c, bytes32 loc, bytes32 val) public`
  Sets the slot `loc` of contract `c` to `val`.

- `function load(address c, bytes32 loc) public returns (bytes32 val)`
  Reads the slot `loc` of contract `c`.

- `function sign(uint sk, bytes32 digest) public returns (uint8 v, bytes32 r, bytes32 s)`
  Signs the `digest` using the private key `sk`. Note that signatures produced via `hevm.sign` will leak the private key.

- `function addr(uint sk) public returns (address addr)`
  Derives an ethereum address from the private key `sk`. Note that `hevm.addr(0)` will fail with
  `BadCheatCode` as `0` is an invalid ECDSA private key.

- `function ffi(string[] calldata) external returns (bytes memory)`
  Executes the arguments as a command in the system shell and returns stdout. Expects abi encoded values to be returned from the shell or an error will be thrown. Note that this
  cheatcode means test authors can execute arbitrary code on user machines as part of a call to `dapp test`, for this reason all calls to `ffi` will fail unless the `--ffi` flag is passed.

- `function prank(address sender) public`
  Sets `msg.sender` to the specified `sender` for the next call.

## Environment Variables

These environment variables can be used to control block parameters:

| Variable               | Default                                      | Synopsis                                                                                                      |
| ---------------------- | -------------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| `DAPP_TEST_ADDRESS`    | `0xb4c79daB8f259C7Aee6E5b2Aa729821864227e84` | The address to deploy the test contract to                                                                    |
| `DAPP_TEST_CALLER`     | `0x00a329c0648769a73afac7f9381e08fb43dbea72` | The address to set `msg.sender` to when calling into the test contract                                        |
| `DAPP_TEST_ORIGIN`     | `0x00a329c0648769a73afac7f9381e08fb43dbea72` | The address to set `tx.orgin` to when calling into the test contract                                          |
| `DAPP_TEST_GAS_CREATE` | `0xffffffffffff`                             | The gas to provide when creating the testing contract                                                         |
| `DAPP_TEST_GAS_CALL`   | `0xffffffffffff`                             | The gas to provide to each call made to the testing contract                                                  |
| `DAPP_TEST_BALANCE`    | `0xffffffffffffffffffffffff`                 | The balance to provide to `DAPP_TEST_ADDRESS`                                                                 |
| `DAPP_TEST_COINBASE`   | `0x0000000000000000000000000000000000000000` | The coinbase address. Will be set to the coinbase for the block at `DAPP_TEST_NUMBER` if rpc is enabled       |
| `DAPP_TEST_NUMBER`     | `0`                                          | The block number. Will be set to the latest block if rpc is enabled                                           |
| `DAPP_TEST_TIMESTAMP`  | `0`                                          | The block timestamp. Will be set to the timestamp for the block at `DAPP_TEST_NUMBER` if rpc is enabled       |
| `DAPP_TEST_GAS_LIMIT`  | `0`                                          | The block gas limit to use                                                                                    |
| `DAPP_TEST_GAS_PRICE`  | `0`                                          | The gas price to use                                                                                          |
| `DAPP_TEST_PREVRANDAO` | `0`                                          | The value for PREVRANDAO. Will be set to the value for the block at `DAPP_TEST_NUMBER` if rpc is enabled  |
