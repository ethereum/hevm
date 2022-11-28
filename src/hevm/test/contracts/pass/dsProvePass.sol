import "ds-test/test.sol";
import "lib/erc20.sol";

contract ConstructorArg {
    address immutable public a;
    constructor(address _a) public {
        a = _a;
    }
}

contract SolidityTest is DSTest {
    ERC20 token;

    function setUp() public {
        token = new ERC20("Token", "TKN", 18);
    }

    function prove_trivial() public {
        assertTrue(true);
    }

    function prove_easy(uint v) public {
        if (v != 100) return;
        assertEq(v, 100);
    }

    function prove_add(uint x, uint y) public {
        unchecked {
            if (x + y < x) return; // no overflow
            assertTrue(x + y >= x);
        }
    }

    function prove_balance(address usr, uint amt) public {
        assertEq(0, token.balanceOf(usr));
        token.mint(usr, amt);
        assertEq(amt, token.balanceOf(usr));
    }

    function prove_supply(uint supply) public {
        token.mint(address(this), supply);
        uint actual = token.totalSupply();
        assertEq(supply, actual);
    }

    function prove_constructorArgs(address b) public {
        ConstructorArg c = new ConstructorArg(b);
        assertEq(b, c.a());
    }

    function proveFail_revertSmoke() public {
        require(false);
    }

    function proveFail_assertSmoke() public {
        assertTrue(false);
    }

    //function prove_transfer(uint supply, address usr, uint amt) public {
        //if (amt > supply) return; // no underflow

        //token.mint(address(this), supply);

        //uint prebal = token.balanceOf(usr);
        //token.transfer(usr, amt);
        //uint postbal = token.balanceOf(usr);

        //uint expected = usr == address(this)
                        //? 0    // self transfer is a noop
                        //: amt; // otherwise `amt` has been transfered to `usr`
        //assertEq(expected, postbal - prebal);
    //}

    function prove_burn(uint supply, uint amt) public {
        if (amt > supply) return; // no undeflow

        token.mint(address(this), supply);
        token.burn(address(this), amt);

        assertEq(supply - amt, token.totalSupply());
    }

    //function prove_loop(uint n) public {
        //uint counter = 0;
        //for (uint i = 0; i < n; i++) {
            //counter++;
        //}
        //assertTrue(counter < 100);
    //}
}
