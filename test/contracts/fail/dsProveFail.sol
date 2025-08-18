import "forge-std/Test.sol";
import "tokens/erc20.sol";

contract SolidityTest is Test {
    ERC20 token;

    function setUp() public {
        token = new ERC20("TOKEN", "TKN", 18);
    }

    function prove_trivial() public {
        assert(false);
    }

    function prove_all_branches_revert() public {
        require(false);
    }

    function prove_trivial_dstest() public {
        assertEq(uint(1), uint(2));
    }

    function prove_add(uint x, uint y) public {
        unchecked {
            assertTrue(x + y >= x);
        }
    }

    function prove_smtTimeout(uint128 p, uint128 q) public {
        unchecked {
            uint256 product = uint256(p) * uint256(q);
            uint256 N = 0xFFFFFFFFFFFFFFFF6DBE8AFB4BF7B8B9D5D8F8B5C7E5B0B2D6B1B5B8F8B9D5D8;
            if (product == N) {
                assertTrue(false);
            } else {
                assertTrue(true);
            }
        }
    }

    function prove_multi(uint x) public {
        if (x == 3) {
            assertTrue(false);
        } else if (x == 9) {
            assertTrue(false);
        } else if (x == 1023423194871904872390487213) {
            assertTrue(false);
        } else {
            assertTrue(true);
        }
    }

    function prove_distributivity(uint120 x, uint120 y, uint120 z) public {
        assertEq(x + (y * z), (x + y) * (x + z));
    }
}

