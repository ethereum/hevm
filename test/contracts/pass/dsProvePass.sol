import "ds-test/test.sol";
import "tokens/erc20.sol";

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

    function prove_no_fail_require() public {
        require(false);
    }

    function proveFail_userAssertSmoke() public {
        assert(false);
    }

    function proveFail_assertSmoke() public {
        assertTrue(false);
    }

    // requires don't fail passing tests, but are not treated as successes in proveFail tests.
    function proveFail_require() public {
        require(false);
    }

    function prove_burn(uint supply, uint amt) public {
        if (amt > supply) return; // no undeflow

        token.mint(address(this), supply);
        token.burn(address(this), amt);

        assertEq(supply - amt, token.totalSupply());
    }
}
