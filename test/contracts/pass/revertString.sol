import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_revert_string(uint stuff) public {
        if (stuff == 0) revert("stuff");
    }
}
