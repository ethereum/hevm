pragma solidity ^0.8.24;
pragma experimental ABIEncoderV2;

import "ds-test/test.sol";

interface Hevm {
    function warp(uint256) external;
    function deal(address,uint256) external;
    function assume(bool) external;
    function roll(uint256) external;
    function load(address,bytes32) external returns (bytes32);
    function store(address,bytes32,bytes32) external;
    function sign(uint256,bytes32) external returns (uint8,bytes32,bytes32);
    function addr(uint256) external returns (address);
    function ffi(string[] calldata) external returns (bytes memory);
    function prank(address) external;
    function startPrank(address) external;
    function stopPrank() external;
    function label(address addr, string calldata label) external;
}

contract HasStorage {
    uint slot0 = 10;
}

contract Prankster {
    function prankme() public returns (address) {
        return msg.sender;
    }
}

contract Payable {
    function hi() public payable {}
    receive() external payable {}
}

contract Empty {}

contract CheatCodes is DSTest {
    Hevm hevm = Hevm(HEVM_ADDRESS);

    function prove_buggy(address e, uint val) public {
        address e = address(new Empty());
        assert(e.balance == 0);
        require(val < 1000);
        hevm.deal(e, val);
        assert(e.balance == val);
        hevm.deal(e, 2*val);
        assert(e.balance == 2*val);

        bytes4 selector = 0xc88a5e6d;  //cast sig "deal(address,uint256)"
        address hevm_addr = address(hevm);
        assembly {
            // Get the free memory pointer
            let ptr := mload(0x40)

            // Store the function selector at the memory location
            mstore(ptr, selector)

            // Store the argument for the function call (offset by 4 bytes for the selector)
            mstore(add(ptr, 0x04), e)
            mstore(add(ptr, 0x24), 5) // BUG HERE

            // Call the function (address of the contract is in "address" variable)
            let result := call(
                gas(),           // Pass all available gas
                hevm_addr,
                0,               // No Ether to send
                ptr,             // Pointer to the input data
                0x44,             // Size of the input data. 4 bytes selector + 32*x bytes argument
                0,               // Output location (not needed)
                0                // Output size (not needed)
            )
            if eq(result, 0) {
                revert(0, 0)
            }
        }
        assert(e.balance == 5);
    }
}
