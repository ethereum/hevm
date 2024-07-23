# Equivalence Checking Tutorial

Equivalence checking allows to check whether two bytecodes do the same thing under all input
circumstances. This allows to e.g. create two functions, one that is known to be good, and
another that uses less gas, but is hard to check for correctness. Then, with equivalence
checking, one can check whether the two behave the same.

## Finding Discrepancies

Let's see this toy contract, in file [contract1.sol](code_examples/contract1.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  mapping (address => uint) balances;
  function my_adder(address recv, uint amt) public {
    if (balances[recv] + amt >= 100) { revert(); }
    balances[recv] += amt;
  }
}
```

And this, slightly modified one, in file [contract2.sol](code_examples/contract2.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  mapping (address => uint) balances;
  function my_adder(address recv, uint amt) public {
    if (balances[recv] + amt >= 100) { revert(); }
    balances[recv] += amt/2;
    balances[recv] += amt/2;
  }
}
```

Now ask hevm if they are equivalent. First, let's compile both contracts and get their bytecode:

```shell
bytecode1=$(solc --bin-runtime "contract1.sol" | tail -n1)
bytecode2=$(solc --bin-runtime "contract2.sol" | tail -n1)
```

Let's ask hevm to compare the two:

```shell
$ hevm equivalence \
      --code-a $(solc --bin-runtime "contract1.sol" | tail -n1) \
      --code-b $(solc --bin-runtime "contract2.sol" | tail -n1)
Found 90 total pairs of endstates
Asking the SMT solver for 58 pairs
Reuse of previous queries was Useful in 0 cases
Not equivalent. The following inputs result in differing behaviours:
-----
Calldata:
  0xafc2c94900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000023
Storage:
  Addr SymAddr "entrypoint": [(0x0,0x10)]
Transaction Context:
  TxValue: 0x0
```

This tells us that with a value of 0x23 being sent, which corresponds
to 35, the two are not equivalent. This is indeed the case: one will add `35
div 2 = 17` twice, which is 34, the other will add 35.

## Fixing and Proving Correctness

Let's fix the above issue by incrementing the balance by 1 in case it's an odd
value. Let's call this [contract3.sol](code_examples/contract3.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  mapping (address => uint) balances;
  function my_adder(address recv, uint amt) public {
    if (balances[recv] + amt >= 100) { revert(); }
    balances[recv] += amt/2;
    balances[recv] += amt/2;
    if (amt % 2 != 0) balances[recv]++;
  }
}
```

Let's check whether this new contract is indeed equivalent:

```shell
$ hevm equivalence \
    --code-a $(solc --bin-runtime "contract1.sol" | tail -n1) \
    --code-b $(solc --bin-runtime "contract3.sol" | tail -n1)
Found 108 total pairs of endstates
Asking the SMT solver for 74 pairs
Reuse of previous queries was Useful in 0 cases
No discrepancies found
```

Hevm reports that the two are now equivalent, even though they clearly don't
consume the same amount of gas and have widely different EVM bytecodes. Yet for
an outside observer, they behave the same. Notice that hevm didn't simply fuzz
the contract and within a given out of time it didn't find a counterexample.
Instead, it _proved_ the two equivalent from an outside observer perspective.
