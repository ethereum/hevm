import {DSTest} from "ds-test/test.sol";
import {ERC20} from "lib/erc20.sol";

contract C is DSTest {
    // BAL: https://etherscan.io/address/0xba100000625a3754423978a60c9317c58a424e3D#code
    ERC20 bal = ERC20(0xba100000625a3754423978a60c9317c58a424e3D);

    function test_trivial() public {
        uint ub = bal.balanceOf(0xBA12222222228d8Ba445958a75a0704d566BF2C8);
        assertEq(ub, 27099516537379438397130892);
    }

    function prove_trivial() public {
        test_trivial();
    }
}
