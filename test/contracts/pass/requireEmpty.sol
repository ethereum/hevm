import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_require_emtpy(uint stuff, uint a) public returns (uint) {
        if (stuff == 0) {
          require(a == 0);
          return a;
        }
        return a;
    }
}
