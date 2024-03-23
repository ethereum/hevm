//SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract MyContract {
  mapping (address => uint) balances;
  function my_adder(address recv, uint amt) public {
    if (balances[recv] + amt >= 100) { revert(); }
    balances[recv] += amt;
  }
}