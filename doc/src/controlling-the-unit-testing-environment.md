# controlling the unit testing environment

## Cheat codes

Since Hevm is an EVM implementation mainly dedicated to testing and exploration, it features a set of `cheat codes` which can manipulate the environment in which the execution is run.

These can be accessed by calling into a contract (typically called `Vm`) at address `0x7109709ECfa91a80626fF3989D68f67F5b1DD12D`, which implements the following methods:

- `function warp(uint x) public`
  Sets the block timestamp to `x`.

- `function roll(uint x) public`
  Sets the block number to `x`.

- `function assume(bool b) public`
  Add the condition `b` to the assumption base for the current branch. This functions almost identically to `require`.

- `function deal(uint usr, uint amt) public`
  Sets the eth balance of `usr` to `amt`. Note that if `usr` is a symbolic address, then it must be the address of a contract that has already been deployed.
  This restriction is in place to ensure soundness of our symbolic address encoding with respect to potential aliasing of symbolic addresses.

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

- `function createFork(string calldata urlOrAlias) external returns (uint256)`
  Creates a new fork with the given endpoint and the _latest_ block and returns the identifier of the fork.

- `function selectFork(uint256 forkId) external`
  Takes a fork identifier created by `createFork` and sets the corresponding forked state as active.

- `function activeFork() external returns (uint256)`
  Returns the identifier of the current fork.

- `function label(address addr, string calldata label) external`
  Labels the address in traces
