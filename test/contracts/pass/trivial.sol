import {DSTest} from "ds-test/test.sol";

// should run and pass
contract Trivial is DSTest {
    function testTrue() public {
        assertTrue(true);
    }
}

