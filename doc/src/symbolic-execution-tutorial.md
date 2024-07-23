# Symbolic Execution Tutorial

Symbolic execution mode of hevm checks whether any call to the contract could
result in an assertion violation. For more details on what exactly is considered an assertion violation, see
[symbolic].


## Simple Example

Let's see this toy contract, in file
[contract-symb-1.sol](code_examples/contract-symb-1.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  function simple_symb() public pure {
    uint i;
    i = 1;
    assert(i == 2);
  }
}
```

Let's first compile it:

```shell
$ solc --bin-runtime contract-symb-1.sol
======= contract-symb-1.sol:MyContract =======
Binary:
6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f600190506002811460455760446048565b5b50565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea26469706673582212202bc2d2c44310edeba83b816dca9ef8abcc9cc1c775bae801b393bf4d5ff2d32364736f6c63430008180033
```

Now let's symbolically execute it:
```shell
$ hevm symbolic --sig "simple_symb()" --code "6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f600190506002811460455760446048565b5b50565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea26469706673582212202bc2d2c44310edeba83b816dca9ef8abcc9cc1c775bae801b393bf4d5ff2d32364736f6c63430008180033"

Discovered the following counterexamples:

Calldata:
  0x881fc77c5f9a8ff385b17ae4c2b3fc970010862df98bfa2f885b071e8c29c7d920e385230182dad8c17bd5e89e8043a08ada90a6d5efdee4425f85cb863109783e158ba4fba908a0e6fae6c6b51002

Storage:
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []
```

## Symbolically executing a specific function

When there are more than one functions in the code, the system will try to
symbolically execute all. Let's take the file
[contract-symb-2.sol](code_examples/contract-symb-2.sol):
```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  uint i;
  function simple_symb1() public view {
    assert(i == 2);
  }
  function simple_symb2() public view {
    assert(i == 3);
  }
}
```

And compile it with solc:

```shell

$ solc --bin-runtime contract-symb-2.sol

======= contract-symb-2.sol:MyContract =======
Binary of the runtime part:
6080604052348015600e575f80fd5b50600436106030575f3560e01c806385c2fc7114603457806386ae330914603c575b5f80fd5b603a6044565b005b60426055565b005b60025f541460535760526066565b5b565b60035f541460645760636066565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220d70d3cfe85d6f0c8a34ce660d76d7f933db353e59397674009e3a3d982275d7e64736f6c63430008180033
```

Now execute the bytecode symbolically with hevm:

```shell
$ hevm symbolic --code "6080604052348015600e575f80fd5b50600436106030575f3560e01c806385c2fc7114603457806386ae330914603c575b5f80fd5b603a6044565b005b60426055565b005b60025f541460535760526066565b5b565b60035f541460645760636066565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220d70d3cfe85d6f0c8a34ce660d76d7f933db353e59397674009e3a3d982275d7e64736f6c63430008180033"

Discovered the following counterexamples:

Calldata:
  0x85c2fc71

Storage:
  Addr SymAddr "entrypoint": [(0x0,0x0)]
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []

Transaction Context:
  TxValue: 0x0


Calldata:
  0x86ae3309

Storage:
  Addr SymAddr "entrypoint": [(0x0,0x0)]
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []

Transaction Context:
  TxValue: 0x0
```

Notice that it discovered two issues. The calldata in each case is the function
signature that `cast` from `foundry` gives for the two functions:

```shell
$ cast sig "simple_symb1()"
0x85c2fc71

$cast sig "simple_symb2()"
0x86ae3309
```

In case you only want to execute a particular function, you tell `hevm` that you only want a particular signature executed:

```shell
$ hevm symbolic --sig "simple_symb1()" --code "6080604052348015600e575f80fd5b50600436106030575f3560e01c806385c2fc7114603457806386ae330914603c575b5f80fd5b603a6044565b005b60426055565b005b60025f541460535760526066565b5b565b60035f541460645760636066565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220d70d3cfe85d6f0c8a34ce660d76d7f933db353e59397674009e3a3d982275d7e64736f6c63430008180033"


Discovered the following counterexamples:

Calldata:
  0x85c2fc71

Storage:
  Addr SymAddr "entrypoint": [(0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []
```


## Abstract versus empty starting storage

The initial store state of `hevm` is completely abstract. This means that the
functions are explored for all possible values of the state. Let's take the
following contract [contract-symb-3.sol](code_examples/contract-symb-3.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  uint i;
  function simple_symb() public view {
    assert(i == 0);
  }
}
```

Let's compile with solc:

```shell
solc --bin-runtime contract-symb-3.sol

======= contract-symb-3.sol:MyContract =======
Binary of the runtime part:
6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f805414604057603f6042565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220cf838a7ff084e553805b9b56decd46ea37363e97e26405b2409d22cb905de0e664736f6c63430008180033
```

With default symbolic execution, a counterexample is found:

```shell
$ cabal hevm symbolic --initial-storage Empty --code "6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f805414604057603f6042565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220cf838a7ff084e553805b9b56decd46ea37363e97e26405b2409d22cb905de0e664736f6c63430008180033"

Discovered the following counterexamples:

Calldata:
  0x881fc77c

Storage:
  Addr SymAddr "entrypoint": [(0x0,0x1)]
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []

Transaction Context:
  TxValue: 0x0
```

However, notice that the counterexample has `1` as the value for `i` storage
variable. However, this contract can never actually assign `i` to any value.
Running this contract with `--initial-state Empty` ensures that the default
value, 0, is assigned, and the assert can never fail:

```shell
cabal run exe:hevm -- symbolic --initial-storage Empty --code "6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f805414604057603f6042565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220cf838a7ff084e553805b9b56decd46ea37363e97e26405b2409d22cb905de0e664736f6c63430008180033"

QED: No reachable property violations discovered
```
