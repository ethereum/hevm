import {Test} from "forge-std/Test.sol";

// should not be run (no code)
abstract contract MyTest is Test {
    function testAbstract() public {
        assertTrue(true);
    }
}

// should run and pass
contract TestMy is MyTest {
    function testTrue() public {
        assertTrue(true);
    }
}
