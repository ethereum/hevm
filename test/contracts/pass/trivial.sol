import {Test} from "forge-std/Test.sol";

// should run and pass
contract Trivial is Test {
    function prove_true() public {
        assertTrue(true);
    }
}

