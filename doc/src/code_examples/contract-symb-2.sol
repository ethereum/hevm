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
