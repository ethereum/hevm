//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  uint i;
  function simple_symb() public view {
    assert(i == 0);
  }
}
