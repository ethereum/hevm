pragma solidity ^0.8.19;

import "forge-std/Test.sol";
import {ERC20} from "tokens/erc20.sol";

contract SolidityTestFail2 is Test {
    ERC20 token;

    function setUp() public {
        token = new ERC20("TOKEN", "TKN", 18);
    }

    function prove_transfer(uint supply, address usr, uint amt) public {
        // require(supply >= amt, "supply must be greater than or equal to amt");
        token.mint(address(this), supply);

        uint prebal = token.balanceOf(usr);
        token.transfer(usr, amt);
        uint postbal = token.balanceOf(usr);

        uint expected = usr == address(this)
                        ? 0    // self transfer is a noop
                        : amt; // otherwise `amt` has been transferred to `usr`
        assertTrue(expected == postbal - prebal);
    }
}

