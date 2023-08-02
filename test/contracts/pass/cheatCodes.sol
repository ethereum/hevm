pragma experimental ABIEncoderV2;

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
}

contract CheatCodes is DSTest {
    address store = address(new HasStorage());
    Hevm hevm = Hevm(HEVM_ADDRESS);

    function prove_warp_concrete() public {
        uint jump = 1000;
        uint pre = block.timestamp;
        hevm.warp(block.timestamp + jump);
        assertEq(block.timestamp, pre + jump);
    }

    function prove_warp_symbolic(uint128 jump) public {
        uint pre = block.timestamp;
        hevm.warp(block.timestamp + jump);
        assertEq(block.timestamp, pre + jump);
    }

    function prove_roll_concrete() public {
        uint jump = 1000;
        uint pre = block.number;
        hevm.roll(block.number + jump);
        assertEq(block.number, pre + jump);
    }

    function prove_store_load_concrete() public {
        uint x = 1000;
        uint ten = uint(hevm.load(store, bytes32(0)));
        assertEq(ten, 10);

        hevm.store(store, bytes32(0), bytes32(x));
        uint val = uint(hevm.load(store, bytes32(0)));
        assertEq(val, x);
    }

    function prove_store_load_symbolic(uint x) public {
        uint ten = uint(hevm.load(store, bytes32(0)));
        assertEq(ten, 10);

        hevm.store(store, bytes32(0), bytes32(x));
        uint val = uint(hevm.load(store, bytes32(0)));
        assertEq(val, x);
    }

    function prove_sign_addr_digest() public {
        uint sk = 1000000;
        bytes32 digest = "123456789";

        (uint8 v, bytes32 r, bytes32 s) = hevm.sign(sk, digest);
        address expected = hevm.addr(sk);
        address actual = ecrecover(digest, v, r, s);

        assertEq(actual, expected);
    }

    function proveFail_sign_addr() public {
        uint sk = 999;
        bytes32 digest = "abcdef123456";
        uint badKey = sk + 1;

        (uint8 v, bytes32 r, bytes32 s) = hevm.sign(badKey, digest);
        address expected = hevm.addr(sk);
        address actual = ecrecover(digest, v, r, s);

        assertEq(actual, expected);
    }

    function proveFail_addr_zero_sk() public {
        hevm.addr(0);
    }

    function proveFFI() public {
        string[] memory inputs = new string[](3);
        inputs[0] = "echo";
        inputs[1] = "-n";
        inputs[2] = "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046163616200000000000000000000000000000000000000000000000000000000";

        (string memory output) = abi.decode(hevm.ffi(inputs), (string));
        assertEq(output, "acab");
    }

    function prove_prank() public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));
        hevm.prank(address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        assertEq(prankster.prankme(), address(this));
    }

    function prove_prank(address caller) public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));
        hevm.prank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), address(this));
    }

    function test_prank_val() public {
        address from = address(0x1312);
        uint amt = 10;

        Payable target = new Payable();
        from.call{value: amt}("");

        uint preBal = from.balance;

        hevm.prank(from);
        target.hi{value : amt}();

        uint postBal = from.balance;

        assertEq(preBal - postBal, amt);
    }
}
