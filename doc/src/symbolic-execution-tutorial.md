# Symbolic Execution Tutorial

Symbolic execution mode of hevm checks whether any call to the contract could
result in an assertion violation. Let's see a simple contract, in file
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

Let's first compile it with `solc`:

```shell
$ solc --bin-runtime contract-symb-1.sol
======= contract-symb-1.sol:MyContract =======
Binary:
6080604052348015600e575f80f....
```

Now let's symbolically execute it:
```shell
$ hevm symbolic --sig "simple_symb()" --code "6080604052348015...."

Discovered the following counterexamples:

Calldata:
  0x881fc77c

Storage:
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []

Transaction Context:
  TxValue: 0x0
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
6080604052348015600e57....
```

Now execute the bytecode symbolically with hevm:

```shell
$ hevm symbolic --code "608060405234...."

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

Notice that hevm discovered two issues. The calldata in each case is the function
signature that `cast` from `foundry` gives for the two functions:

```shell
$ cast sig "simple_symb1()"
0x85c2fc71

$cast sig "simple_symb2()"
0x86ae3309
```

In case you only want to execute only a particular function, you can ask `hevm`
to only execute a particular function signature via the `--sig` option:

```shell
$ hevm symbolic --sig "simple_symb1()" --code "6080604052348015600...."


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
6080604052348015600e575f80fd5b50600436106026575f3560e01c806388....
```

With default symbolic execution, a counterexample is found:

```shell
$ cabal hevm symbolic --initial-storage Empty --code "60806040523...."

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
cabal run exe:hevm -- symbolic --initial-storage Empty --code "60806040...."

QED: No reachable property violations discovered
```

Here, no counterexamples are discovered, because with empty default state, the
value of `i` is zero, and therefore `assert(i == 0)` will all never trigger.

## Using forge to build your project for symbolic execution

Forge can also be used to build your project and run symbolic execution on it.
This fits in well with standard development practices. You can use `forge` to
build and then `jq` to extract the runtime bytecode. Let's say we have the
following contract:

```solidity
contract AbsStorage {
    uint256 public a;
    function not2() public {
      assert(a != 2);
    }
}
```

Notice that this contract cannot set `a` to 2, hence the assert will never fail
in the real world. However, in `symbolic` mode, hevm allows the state to be
symbolic, hence it can explore all possible values of `a`, even ones that are
not possible in the real world. Let's compile this contract with forge and then
run symbolic execution on it:

```shell
$ forge build --ast
[⠒] Compiling...
[⠢] Compiling 1 files with Solc 0.8.19
[⠆] Solc 0.8.19 finished in 11.46ms

$ hevm symbolic --code $(jq -r '.deployedBytecode.object' out/abs_storage.sol/AbsStorage.json )
Discovered the following 1 counterexample(s):

Calldata:
  0xb1712ffd

Storage:
  Addr SymAddr "entrypoint": [(0x0,0x2)]
  Addr SymAddr "miner": []
  Addr SymAddr "origin": []

Transaction Context:
  TxValue: 0x0
```

The calldata provided by hevm is the function signature of `not2()`. This can
be checked via `cast`, which is installed as part of foundry:

```shell
cast keccak "not2()"
0xb1712ffd...
```

We can get all the details of the state and context led to the counterexample
by using the `--get-models` flag. While there will be a number of branches
displayed, only one will be relevant to the counterexample. Here is the
relevant branch:

```
=== Models for 8 branches ===
[...]

--- Branch ---

Inputs:

  Calldata:
    0xb1712ffd

  Storage:
    Addr SymAddr "entrypoint": [(0x0,0x2)]

  Transaction Context:
    TxValue: 0x0


End State:

  (Failure
    Error:
      (Revert
        (ConcreteBuf
          Length: 36 (0x24) bytes
          0000:   4e 48 7b 71  00 00 00 00  00 00 00 00  00 00 00 00   NH{q............
          0010:   00 00 00 00  00 00 00 00  00 00 00 00  00 00 00 00   ................
          0020:   00 00 00 01                                          ....
        )
      )
      [...]
```

Here, the storage variable is set to `2`, which is the value that
the `assert` tested for. Notice that the panic exception is of type `01`, which
is what's expected for an [`assert` failure in
solidity](https://docs.soliditylang.org/en/latest/control-structures.html).
