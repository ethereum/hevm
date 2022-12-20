import "ds-test/test.sol";

contract Testdapp {
    uint public x;
    function f() public {
        x++;
    }
    function g(uint y) public {
        if (y % 2 == 0) x*=2;
    }
}


contract TestdappTest is DSTest {
    Testdapp testdapp;

    function setUp() public {
        testdapp = new Testdapp();
    }

    function invariantFirst() public {
        assertLt(testdapp.x(), 100);
    }
}

contract InvariantCount is DSTest {
    BrokenAtStart count;
    address[] targetContracts_;

    function targetContracts() public returns (address[] memory) {
      return targetContracts_;
    }
    function setUp() public {
        count = new BrokenAtStart();
        targetContracts_.push(address(count));
    }

    // this can only fail if we call the invariant method before calling any other method in the target contracts
    function invariantCount() public {
        assertGt(count.count(), 0);
    }
}

contract BrokenAtStart {
    uint public count;

    function inc() public {
        count++;
    }
}
