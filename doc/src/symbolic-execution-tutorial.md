# Symbolic Execution Tutorial

Symbolic execution mode of hevm checks whether any call to the contract could
result in an assertion violation. For more details on what exactly is considered an assertion violation, see
[symbolic].


## Simple Example

Let's see this toy contract, in file [contract-symb-1.sol](contract-symb-1.sol):

```solidity
//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  function simple_symb() public pure {
    uint i;
    require(i == 1);
    assert(i == 2);
  }
}
```

Let's first compile it:

```shell
$ solc --bin doc/src/code_examples/contract-symb-1.sol
======= contract-symb-1.sol:MyContract =======
Binary:
6080604052348015600e575f80fd5b5060b28061001b5f395ff3fe6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f60018114603e575f80fd5b60028114604c57604b604f565b5b50565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea26469706673582212205b3c554bf52c7f17e2e57ad844a1a323de3ef0c4472642b71a3e3d5eb5a5dd7364736f6c63430008180033
```

Now let's symbolically execute it:
```shell
$ hevm symbolic --code "6080604052348015600e575f80fd5b5060b28061001b5f395ff3fe6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f60018114603e575f80fd5b60028114604c57604b604f565b5b50565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea26469706673582212205b3c554bf52c7f17e2e57ad844a1a323de3ef0c4472642b71a3e3d5eb5a5dd7364736f6c63430008180033"

WHATEVER
```

## More complicated example

TODO: with non-abstract starting state, for example

