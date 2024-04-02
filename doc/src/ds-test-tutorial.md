# ds-test Tutorial

Test cases must be prepended with `prove_` and the testing contract must
inherit from `Test` from [Forge's standard test
library](https://book.getfoundry.sh/forge/forge-std). First, import Test:
`import {Test} from "forge-std/Test.sol";` and then inherit from it via `... is
Test`. This allows hevm to discover the test cases it needs to run. Like so:

```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract BadVaultTest is Test {
  function prove_mytest() {
  // environment setup, preconditions
  // call(s) to test
  // postcondition checks
  }
}
```

Once you have written such a test case, you need to compile with `forge build`
(see [forge documentation](https://book.getfoundry.sh/forge/tests) for more
details) and then:

```
$ hevm test
Checking 1 function(s) in contract src/badvault-test.sol:BadVault
[RUNNING] prove_mytest(uint256)
   [PASS] prove_mytest(uint256)
```

Here, hevm discovered the test case, and automatically checked it for
violations.

## Setting Up Tests

Tests usually need to set up the environment in a particular way, such
as contract address, storage, etc. This can be done via Cheat Codes that
can change the address of the caller, set block number, etc. See [Cheat
Codes](#supported-cheat-codes) below for a range of cheat codes supported. Cheat Codes
are a standard method used by other tools, such as
[Foundry](https://book.getfoundry.sh/), so you should be able to re-use your
existing setup. An example setup could be:

```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract BadVaultTest is Test {
    MyVault vault;

    function setUp() public {
        // Set up environment
        vault = new BadVault();

        address user1 = address(1);
        vm.deal(user1, 1 ether);
        vm.prank(user1);
        vault.deposit{value: 1 ether}();

        address user2 = address(2);
        vm.deal(user2, 1 ether);
        vm.prank(user2);
        vault.deposit{value: 1 ether}();

        address attacker = address(42);
        vm.prank(attacker);
        // call(s) to test
        // postcondition checks
    }
}
```

The postconditions should check the state of the contract after the call(s) are
complete. In particular, it should check that the changes that the function applied
did not break any of the (invariants)[https://en.wikipedia.org/wiki/Invariant_(mathematics)]
of the contract, such as total number of tokens.

You can read more about testing and cheat codes in the (Foundry
Book)[https://book.getfoundry.sh/forge/cheatcodes] and you can see the
hevm-supported cheat codes [below](#supported-cheat-codes).

## Understanding Counterexamples

When hevm discovers a failure, it prints an example call how to trigger the failure. Let's see the following
simple solidity code:

```
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  mapping (address => uint) balances;
  function prove_single_fail(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) { revert(); }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
```

After compiling with `forge build`, when ran under hevm, we get:

```
$ hevm test
Checking 1 function(s) in contract src/contract-fail.sol:MyContract
[RUNNING] prove_single_fail(address,uint256)
   [FAIL] prove_single_fail(address,uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_single_fail(0x0000000000000000000000000000000000000000,100)
```

Here, hevm provided us with a calldata, where the receiver happens to be the
zero address, and the value sent is exactly 100. This indeed is the boundary
condition where the function call fails. The function should have had a `>=`
rather than a `>` in the `if`. Notice that in this case, while hevm filled in
the `address` to give a complete call, the address itself is irrelevant,
although this is not explicitly mentioned.

## Test Cases that Must Always Revert

Hevm assumes that a test case should not always revert. If you have such a test
case, hevm will warn you and return a FAIL. For example this toy contract:

```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  uint256 cntr;
  function prove_allrevert(uint256 val) public {
      if(val < 0) {
          unchecked { cntr = val; }
          revert();
      } else revert();
  }
}
```

When compiled with forge and then ran under hevm with `hevm test`, hevm returns:

```
Checking 1 function(s) in contract src/contract-allrevert.sol:MyContract
[RUNNING] prove_allrevert(uint256)
   [FAIL] prove_allrevert(uint256)
   Reason:
     No reachable assertion violations, but all branches reverted
     Prefix this testname with `proveFail` if this is expected
```

This is sometimes undesirable. In these cases, prefix your contract with
`proveFail_` instead of `prove_`:

```solidity
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";
contract MyContract is Test {
  uint256 cntr;
  function proveFail_allrevert_expected(uint256 val) public {
      if(val < 0) {
          unchecked {
            cntr = val;
            cntr += 1;
          }
          revert();
      }
      else revert();
  }
}
```

When this is compiled with forge and then checked with hevm, it leads to:

```
Checking 1 function(s) in contract src/contract-allrevert-expected.sol:MyContract
[RUNNING] proveFail_allrevert_expected(uint256)
   [PASS] proveFail_allrevert_expected(uint256)
```

Which is now the expected outcome.


## Supported Cheat Codes

Since hevm is an EVM implementation mainly dedicated to testing and
exploration, it features a set of "cheat codes" which can manipulate the
environment in which the execution is run. These can be accessed by calling
into a contract (typically called `Vm`) at address
`0x7109709ECfa91a80626fF3989D68f67F5b1DD12D`, which happens to be keccak("hevm cheat code"),
implementing the following methods:

| Function | Description |
| --- | --- |
|`function prank(address sender) public`| Sets `msg.sender` to the specified `sender` for the next call.|
|`function deal(address usr, uint amt) public`| Sets the eth balance of `usr` to `amt`. Note that if `usr` is a symbolic address, then it must be the address of a contract that has already been deployed. This restriction is in place to ensure soundness of our symbolic address encoding with respect to potential aliasing of symbolic addresses.|
|`function store(address c, bytes32 loc, bytes32 val) public`| Sets the slot `loc` of contract `c` to `val`.|
|`function warp(uint x) public`| Sets the block timestamp to `x`.|
|`function roll(uint x) public`| Sets the block number to `x`.|
|`function assume(bool b) public`| Add the condition `b` to the assumption base for the current branch. This functions almost identically to `require`. For most users, `require` is preferable. However, in case you wish to understand & modify the internal IR of hevm, you may want to use `assume`.|
|`function load(address c, bytes32 loc) public returns (bytes32 val)`| Reads the slot `loc` of contract `c`.|
|`function sign(uint sk, bytes32 digest) public returns (uint8 v, bytes32 r, bytes32 s)`| Signs the `digest` using the private key `sk`. Note that signatures produced via `hevm.sign` will leak the private key.|
|`function addr(uint sk) public returns (address addr)`| Derives an ethereum address from the private key `sk`. Note that `hevm.addr(0)` will fail with `BadCheatCode` as `0` is an invalid ECDSA private key.|
|`function ffi(string[] calldata) external returns (bytes memory)`| Executes the arguments as a command in the system shell and returns stdout. Expects abi encoded values to be returned from the shell or an error will be thrown. Note that this cheatcode means test authors can execute arbitrary code on user machines as part of a call to `dapp test`, for this reason all calls to `ffi` will fail unless the `--ffi` flag is passed.|
|`function createFork(string calldata urlOrAlias) external returns (uint256)`| Creates a new fork with the given endpoint and the _latest_ block and returns the identifier of the fork.|
|`function selectFork(uint256 forkId) external`| Takes a fork identifier created by `createFork` and sets the corresponding forked state as active.|
|`function activeFork() external returns (uint256)`| Returns the identifier of the current fork.|
|`function label(address addr, string calldata label) external`| Labels the address in traces|
