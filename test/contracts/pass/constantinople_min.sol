import "ds-test/test.sol";

contract DeadCode{
    function dummy() external returns (uint256) {}
}

contract ConstantinopleTests is DSTest {
    DeadCode notmuch;
    function setUp() public {
      notmuch = new DeadCode();
    }

    // this 5 byte-long initcode simply returns nothing
    // PUSH1  00     PUSH1  00     RETURN
    // 60     00     60     00     f3
    bytes32 zerocode        = 0x60006000f3000000000000000000000000000000000000000000000000000000;
    // this 13 byte-long initcode simply returns 0xdeadbeef:
    // PUSH4  de     ad     be     ef     PUSH1  00     MSTORE PUSH1  32     PUSH1  00     RETURN
    // 63     de     ad     be     ef     60     00     52     60     20     60     00     f3
    bytes32 deadcode        = 0x63deadbeef60005260206000f300000000000000000000000000000000000000;
    // this 25 byte-long initcode returns deadcode (but without the padding)
    // PUSH1  0d     PUSH1  0c     PUSH1  00     CODECO PUSH1  0d     PUSH1  00     RETURN deadcode
    // 60     0d     60     0c     60     00     39     60     0d     60     00     f3
    bytes32 deploysdeadcode = 0x600d600c600039600d6000f363deadbeef60005260206000f300000000000000;

    // address of account created by CREATE2 is
    // keccak256(0xff + address + salt + keccak256(init_code))[12:]
    function check_create2_1() public {
        address a;
        uint256 salt = 0xfacefeed;
        assembly {
          let top := mload(0x40)
          mstore(top, sload(deadcode.slot))
          a := create2(0, top, 13, salt)
        }

        address expected_a;

        assembly {
          let top := mload(0x40)
          mstore(top, sload(deadcode.slot))
          let inithash := keccak256(top, 13)
          mstore(sub(top, 11), address())
          mstore8(top, 0xff)
          mstore(add(top, 21), salt)
          mstore(add(top, 53), inithash)
          expected_a := and(keccak256(top, 85), 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff)
        }

        assertEq(a, expected_a);
    }
}
