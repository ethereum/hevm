import "ds-test/test.sol";
import "lib/erc20.sol";

contract InvariantTest is DSTest {
    ERC20 token;
    User user;
    address[] targetContracts_;

    function targetContracts() public returns (address[] memory) {
      return targetContracts_;
    }

    function setUp() public {
        token = new ERC20("TOKEN", "TKN", 18);
        token.mint(address(this), 100 ether);
        user = new User(token);
        token.transfer(address(user), 100 ether);
        targetContracts_.push(address(user));
    }

    function invariantTestThisBal() public {
        assertLe(token.balanceOf(address(user)), 100 ether);
    }
    function invariantTotSupply() public {
        assertEq(token.totalSupply(), 100 ether);
    }
}

contract User {
  ERC20 token;
  constructor(ERC20 token_) public {
    token = token_;
  }

  function doTransfer(address to, uint amount) public {
    token.transfer(to, amount);
  }

  function doSelfTransfer(uint amount) public {
    token.transfer(address(this), amount);
  }
}
