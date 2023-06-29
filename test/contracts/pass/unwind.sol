import {DSTest} from "ds-test/test.sol";

// tests unwind support in precompiles
contract Unwind is DSTest {
    function testInvalidSum() public {
        bytes32 x = hex"01";
        try this.callBn256Add(x, x, x, x) returns (bytes32[2] memory) {
            failed();
        } catch (bytes memory) { }
    }

    function callBn256Add(
        bytes32 ax,
        bytes32 ay,
        bytes32 bx,
        bytes32 by
    ) external returns (bytes32[2] memory result) {
        bytes32[4] memory input;
        input[0] = ax;
        input[1] = ay;
        input[2] = bx;
        input[3] = by;
        assembly {
            let success := call(gas(), 0x06, 0, input, 0x80, result, 0x40)
            switch success
            case 0 {
                revert(0, 0)
            }
        }
    }
}
