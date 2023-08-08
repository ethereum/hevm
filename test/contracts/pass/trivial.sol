import {DSTest} from "ds-test/test.sol";

// should run and pass
contract Trivial is DSTest {
    function prove_true() public {
        assertTrue(true);
    }
}

