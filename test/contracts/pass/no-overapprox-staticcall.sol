
// This test overapproximates the staticcall (it's a "view" function, so it's a staticcall)
// if an SMT solver is not called to check that there is only one solution to the address masking
import {Test} from "forge-std/Test.sol";

contract ERC20 {
  function f() public view { }
}

contract TEST is Test{
  address[] tokens;
  address any = address(0x1234);
  mapping(address => uint256) balances;

  function setUp() public {
    tokens.push(address(new ERC20()));
  }

  function prove_no_overapprox(address target) public {
    balances[target] = any.balance;
    ERC20(address(tokens[0])).f();
  }
}
