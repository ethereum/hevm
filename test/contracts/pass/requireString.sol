import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_require_string(uint stuff, uint a) public returns (uint) {
        if (stuff == 0) {
          require(a == 0, "must be 0");
          return a;
        }
        return a;
    }
}
