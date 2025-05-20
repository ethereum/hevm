import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_assert_equal(uint stuff) public {
        assertEq(stuff, 0);
    }
}
