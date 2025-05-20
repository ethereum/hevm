import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_revert_empty(uint stuff) public {
        if (stuff == 0) revert();
    }
}
