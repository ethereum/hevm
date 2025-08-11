// SPDX-License-Identifier: MIT
import {Test} from "forge-std/Test.sol";

contract Stuff {
  function myfun(uint a ) public pure returns (uint) {
    unchecked {
      return a * 2;
    }
  }
}

contract MyOnlyDeployed is Test {
  Stuff stuff;
  function setUp() public {
    stuff = new Stuff();
  }

  // cast keccak "myfun(uint256)"
  // 0xb2d71d6870ba4b4e58f932901330aa9aaf5e31a65a07d4c73632529167626820
  function prove_only_deployed(uint a, address addr) public {
    (, bytes memory ret) = addr.call(abi.encodeWithSelector(0xb2d71d68, a));
    uint x = abi.decode(ret, (uint));
    assert(x == a * 2);
  }
}
