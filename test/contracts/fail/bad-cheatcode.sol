import {Test} from "forge-std/Test.sol";

interface Vm {
  function bad_cheatcode(uint) external returns (bytes32);
}

contract SolidityTest is Test {
    function prove_bad_cheatcode(uint stuff) public {
        Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
        assert(stuff != 4);
        vm.bad_cheatcode(stuff);
    }
}
