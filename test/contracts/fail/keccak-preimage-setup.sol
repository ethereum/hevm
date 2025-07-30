// SPDX-License-Identifier: MIT
import {Test} from "forge-std/Test.sol";

contract MyContractTest is Test {
  mapping (address => uint) balances;
  function setUp() public {
    balances[address(0x1234)] = 50;
  }
  function prove_bad_addr(address x) public view {
    assert(balances[x] != 50);
  }
}
