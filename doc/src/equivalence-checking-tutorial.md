# Equivalence Checking Tutorial

Equivalence checking allows to check whether two bytecodes do the same thing under all input
circumstances. This allows to e.g. create two functions, one that is known to be good, and
another that uses less gas, but is hard to check for correctness. Then, with equivalence
checking, one can check whether the two behave the same.

The notion of equivalence in hevm is defined as follows. Two contracts are equivalent
if for all possible calldata and state, after execution has finished, their observable
storage state is equivalent and they return the same value. In particular, the
following is NOT checked when checking for equivalence:
- [Gas](https://ethereum.org/en/developers/docs/gas/) consumption
- [Events](https://solidity-by-example.org/events/) emitted
- Maximum stack depth
- Maximum memory usage

Note that in the Solidity ABI, the calldata's first 4 bytes are the
[function selector](https://docs.soliditylang.org/en/latest/abi-spec.html#function-selector)
which decide which function is being called, along with the potential
[fallback](https://solidity-by-example.org/fallback/) function mechanism.
Hence, treating calldata as symbolic covers all possible function calls,
including fallback functions. While not all contracts
[follow the Solidity ABI](https://github.com/ethereum/requests-for-proposals/blob/master/open-rfps/pectra-system-contracts-audit.md),
since hevm's symbolic equivalence checker does not distinguish between function
selector and function parameter bytes in the calldata, it will still correctly
check the equivalence of such non-conforming contracts.

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

## Dealing with Already Compiled Contracts

If the contracts have already been compiled into a hex string, you can paste
them into files `a.txt` and `b.txt` and compare them via:

```shell
$ hevm equivalence --code-a "$(<a.txt)" --code-b "$(<b.txt)"
```

You can also copy-paste the contents of the hex strings directly into the
command line, although this can become cumbersome:

```shell
$ hevm equivalence --code-a "6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f600190506002811460455760446048565b5b50565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea26469706673582212208c57ae04774d9ebae7d1d11f9d5e730075068bc7988d4c83c6fed85b7f062e7b64736f6c634300081a0033" --code-b "6080604052348015600e575f80fd5b50600436106030575f3560e01c806385c2fc7114603457806386ae330914603c575b5f80fd5b603a6044565b005b60426055565b005b60025f541460535760526066565b5b565b60035f541460645760636066565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220bd2f8a1ba281308f845e212d2b5eceab85e029909fa2409cdca7ede039bae26564736f6c634300081a0033"
```
