import "ds-test/test.sol";

interface Hevm {
    function warp(uint256) external;
    function roll(uint256) external;
    function load(address,bytes32) external returns (bytes32);
    function store(address,bytes32,bytes32) external;
    function sign(uint256,bytes32) external returns (uint8,bytes32,bytes32);
    function addr(uint256) external returns (address);
    function ffi(string[] calldata) external returns (bytes memory);
    function prank(address) external;
}

contract Payable {
    function hi() public payable {}
}

contract TestFailCheatCodes is DSTest {
    Hevm hevm = Hevm(HEVM_ADDRESS);

    function testBadFFI() public {
        string[] memory inputs = new string[](2);
        inputs[0] = "echo";
        inputs[1] = "acab";

        // should revert if --ffi hasn't been passed to hevm...
        hevm.ffi(inputs);
    }

    function test_prank_underflow() public {
        address from = address(0x1312);
        uint amt = 10;

        Payable target = new Payable();

        hevm.prank(from);
        target.hi{value : amt}();
    }
}
