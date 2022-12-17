import {DSTest} from "ds-test/test.sol";
import {ERC20} from "lib/erc20.sol";

contract C is DSTest {
    // BAL: https://etherscan.io/address/0xba100000625a3754423978a60c9317c58a424e3D#code
    ERC20 bal = ERC20(0xba100000625a3754423978a60c9317c58a424e3D);

    function prove_transfer(address dst, uint amt) public {
        // ignore cases where we don't have enough tokens
        if (amt > bal.balanceOf(address(this))) return;
        if (dst == address(0x0)) return;

        uint preBalThis = bal.balanceOf(address(this));
        uint preBalDst  = bal.balanceOf(dst);

        bal.transfer(dst, amt);

        // no change for self-transfer
        uint delta = dst == address(this) ? 0 : amt;

        // balance of `this` has been reduced by `delta`
        assertEq(preBalThis - delta, bal.balanceOf(address(this)));

        // balance of `dst` has been increased by `delta`
        assertEq(preBalDst + delta, bal.balanceOf(dst));
    }

    function testCex() public {
        prove_transfer(0x8000000000000000000000000000000000000000,0);
    }
}
