# Overview

The hevm project is an implementation of the Ethereum Virtual Machine (EVM) focused on symbolic analysis of evm bytecode. This essentially means that hevm can try out _all_ execution possibilities of your contract and see it can somehow violate some assertions you have, such as e.g. the total number of tokens must always be X or that some value must never be greater than Y.

In some sense, hevm is similar to a fuzzer, but instead of only trying with random values to trigger faults, it instead _computes_ whether a fault is possible. If it is possible, it gives an example call to trigger the fault, and if it isn't possible, it mathematically proves it so, and tells the user the contract is safe. Note that while great pains have gone into making sure hevm's results can be trusted, there can always be bugs in hevm or the libraries and tools it uses.

Hevm can not only be used to find bugs in already written programs, but can also help you write a program that from the outside behaves the same as the original program, but may use less gas to execute. This can be done via (equivalence checking)[#equivalence-checking] where hevm will either prove that the behaviour of the two bytecodes is the same, or will give inputs where they differ.

## Practical scenario

The following is a practical scenario involving a smart contract function designed to transfer money under certain conditions, namely that no balance can be larger than or equal to 100. Let's see the contract and its associated check:

```solidity
// SPDX-License-Identifier: MIT

pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
```

Notice that this function has a bug: the `require` and the `assert` both check for `<`, but the `if` checks for `>`, which should instead be `>=`. Let's see if `hevm` can find this bug. In order to do that, we have to prepend the function name with `prove_`, which we did.

### Building

We now need a copy of hevm (see [releases](https://github.com/ethereum/hevm/releases)) and the SMT solver z3, which can be installed e.g. with `apt-get` on ubuntu/debian or `homebrew` on Mac, and a copy of [Foundry](https://getfoundry.sh/):

```shell
$ sudo apt-get install z3  # install z3
$ curl -L https://foundry.paradigm.xyz | bash # install foundryup
$ foundryup # install forge and other foundry binaries
$ mkdir mytest && cd mytest
$ wget https://github.com/ethereum/hevm/releases/download/release/0.53.0/hevm-x86_64-linux
$ chmod +x ./hevm-x86_64-linux
$ forge init .
$ cat <<EOF > src/contract.sol
pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  mapping (address => uint) balances;
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt > 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
}
EOF
$ forge build
[⠊] Compiling...
[⠒] Compiling 1 files with 0.8.19
[⠢] Solc 0.8.19 finished in 14.27ms
Compiler run successful!
```

### Finding the Bug

Now let's run `hevm` to see if it finds the bug:

```shell
$ hevm test --solver z3
Running 1 tests for src/contract.sol:MyContract
[FAIL] prove_add_value(address,uint256)
  Counterexample:
    result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
    calldata: prove_add_value(0x0000000000000000000000000000000000000000,100)
```

### Fixing the Bug

This counterexample tells us that when sending exactly 100 to an empty account, the new balance will violate the `< 100` assumption. Let's fix this bug, the new `prove_add_value` should now say:

```solidity
  function prove_add_value(address recv, uint amt) public {
    require(balances[recv] < 100);
    if (balances[recv] + amt >= 100) {
      revert();
    }
    balances[recv] += amt;
    assert(balances[recv] < 100);
  }
```

Let's re-build with forge and check with hevm once again:

```shell
$ forge build
[⠰] Compiling...
[⠔] Compiling 1 files with 0.8.19
[⠒] Solc 0.8.19 finished in 985.32ms
Compiler run successful!
```

```shell
$ hevm test --solver z3
Running 1 tests for src/contract.sol:MyContract
[PASS] prove_add_value(address,uint256)
```

We now get a `PASS`. Notice that this doesn't only mean that hevm couldn't find a bug within a given time frame. Instead, it means that there is surely no call to `prove_add_value` such that our assertion can be violated. However, it _does not_ check for things that it was not asked to check for. In particular, it does not check that e.g. the sender's balance is decremented. There is no such test and so this omission is not detected.

## Capabilities

- Symbolic execution of solidity tests written using [`ds-test`](https://github.com/dapphub/ds-test/) (a.k.a "foundry tests"). This allows one to find _all_ potential failure modes of a function.
- Fetch remote state via RPC, so your tests can be rooted in the real-world, calling out to other, existing contracts, with existing state and already deployed bytecode.
- Prove equivalence of two different bytecode objects such as two functions or even entire contracts.

## Similarities and Differences to Other Tools

Hevm is similar to [Halmos](https://github.com/a16z/halmos) and [Kontrol](https://docs.runtimeverification.com/kontrol/overview/readme) in its approach.

However, it is quite different from static code analysis tools such as [Oyente](https://github.com/enzymefinance/oyente), [Slither](https://github.com/crytic/slither), and [Mythril](https://github.com/ConsenSys/mythril). While these 3 tools typically use some form of symbolic execution to try to validate their results, their main method of operation is not via symbolic execution, and they can, and do, report false positives.

Notice that static code analysis tools will find bugs that the author(s) didn't write a test case for, as they typically have a (large) set of preconfigured test-cases that they will report on, if they can find a way to violate them. In that sense, it may be valuable to run them alongside hevm.

Finally, [SMTChecker](https://github.com/ethereum/solidity/blob/develop/docs/smtchecker.rst) may also be interesting to run alongside hevm. SMTChecker is very different from both approaches detailed above. While SMTChecker is capable of reliably finding both reentrancy and loop-related bugs, the tools above can only do so on a best effort basis. Hevm often reports a warning of incompleteness for such problems, while static code analysis tools either report potential positives or may even not discover them at all.

### Comparison Table

| Tool | Approach | Primary Method | Notes |
| --- | --- | --- | --- |
| **hevm** | Symbolic analysis of EVM bytecode | Symbolic execution | Focuses on exploring all execution possibilities, identifying potential assertion violations, and optimizing gas usage. Can prove equivalence between bytecodes. |
| **Halmos** | Similar to hevm | Not specified | Approach similar to hevm, but the document does not detail specific methodologies or differences. |
| **Kontrol** | Similar to hevm | Not specified | Approach similar to hevm, with a focus presumably on symbolic analysis as well, but further details are not provided in the document. |
| **Oyente** | Static code analysis | Partial symbolic execution | Uses symbolic execution to validate results but primarily relies on static analysis. Can report false positives. |
| **Slither** | Static code analysis | Partial symbolic execution | Similar to Oyente, uses static analysis as its main method, complemented by symbolic execution for validation. Known for reporting false positives. |
| **Mythril** | Static code analysis | Partial symbolic execution | Combines static code analysis with symbolic execution for result validation. Like Oyente and Slither, can report false positives. |
| **SMTChecker** | Different from both hevm and static code analysis tools | SMT solving | Capable of finding reentrancy and loop-related bugs reliably, which other tools might miss or report incompletely. Offers a distinct approach from symbolic execution. |

## History

Hevm was originally developed as part of the [dapptools](https://github.com/dapphub/dapptools/) project, and was forked into this repo by the Formal Verification team at the Ethereum Foundation in August 2022.
