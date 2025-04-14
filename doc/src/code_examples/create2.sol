//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract C {
  uint private immutable NUMBER;
  constructor(uint a) {
    NUMBER = 4;
  }
  function stuff(uint b) public returns (uint256) {
    unchecked {return NUMBER+b;}
  }
}
