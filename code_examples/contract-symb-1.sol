//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  function simple_symb() public pure {
    uint i;
    i = 1;
    assert(i == 2);
  }
}
