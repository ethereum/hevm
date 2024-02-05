# Overview

The `hevm` project is an implementation of the Ethereum Virtual Machine (EVM) focused on symbolic
analysis of evm bytecode. It can:

- [symbolically execute](sym a smart contract and find reachable assertion violations
- prove equivalence of two different bytecode objects
- execute symbolic solidity tests written using [`ds-test`](https://github.com/dapphub/ds-test/) (a.k.a "foundry tests")
- fetch remote state via rpc

## Example

Let's say we have a function that allows transfer of money, but no balance can be larger than or equal to 100:

```solidity
pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] <= 100);
    balances[msg.sender] -= amt;
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] <= 100);
  }
}
```

Notice that this function has a bug: the `require` and the `assert` both check
for `<=`, but the `if` checks for `<`. Let's see if `hevm` can find this bug.
In order to do that, we have to prepend the function name with `prove_`, which we did.
Let's put this file into a directory `src/` and run `forge`:

```sh
$ mkdir mytest && cd mytest
$ forge init .
$ cat <<EOF >> src/contract.sol
pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] <= 100);
    balances[msg.sender] -= amt;
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] <= 100);
  }
}
EOF
$ forge build
[⠊] Compiling...
[⠒] Compiling 1 files with 0.8.19
[⠢] Solc 0.8.19 finished in 14.27ms
Compiler run successful!
hevm test --match 'src/contract.sol.*prove.*' --solver z3
```

Now we can run `hevm`:


## History
It was originally developed as part of the
[dapptools](https://github.com/dapphub/dapptools/) project, and was forked to
this repo by the formal methods team at the Ethereum Foundation in August 2022.
