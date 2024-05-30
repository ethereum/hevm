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


    function prove_startPrank(address caller) public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));

        hevm.startPrank(address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        hevm.stopPrank();

        hevm.startPrank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), caller);
        hevm.stopPrank();

        assertEq(prankster.prankme(), address(this));

        hevm.prank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), address(this));
    }

    // this is not supported yet due to restrictions around symbolic address aliasing...
    function proveFail_deal_unknown_address(address e, uint val) public {
        hevm.deal(e, val);
        assert(e.balance == val);
    }

    function prove_deal_simple(uint val) public {
        address e = address(new Empty());
        assert(e.balance == 0);
        hevm.deal(e, val);
        assert(e.balance == val);
    }

    function prove_deal_no_underflow(uint val) public {
        require(address(this).balance < val);
        prove_deal_simple(val);
    }

    function prove_deal_multiple(uint val1, uint val2) public {
        address e = address(new Empty());

        assert(e.balance == 0);
        hevm.deal(e, val1);
        assert(e.balance == val1);

        hevm.deal(e, val2);
        assert(e.balance == val2);
    }

    function prove_assume(bool b) public {
        hevm.assume(b);
        assert(b);
    }

    function prove_assume(uint v) public {
        hevm.assume(v > 10);
        assert(v > 10);
    }

    function proveFail_assume(uint v) public {
        hevm.assume(v > 10);
        assert(v <= 10);
    }

    function proveFail_assume(bool b) public {
        hevm.assume(b);
        assert(!b);
    }

    function prove_prank_val() public {
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

    function prove_prank_val_2() public {
        address payable a = payable(address(new Payable()));
        address payable b = payable(address(new Payable()));

        // send this.balance to a
        a.call{value: address(this).balance}("");
        uint aBal = a.balance;

        // send 1 wei from a to b
        hevm.prank(a);
        address(b).call{value: 1}("");

        // check balances
        assertEq(a.balance, aBal - 1);
        assertEq(b.balance, 1);
    }

    function prove_startPrank_val() public {
        address payable a = payable(address(new Payable()));
        address payable b = payable(address(new Payable()));

        // send this.balance to a
        a.call{value: address(this).balance}("");
        uint aBal = a.balance;

        // send 1 wei from a to b
        hevm.startPrank(a);
        address(b).call{value: 1}("");
        address(b).call{value: 1}("");
        hevm.stopPrank();

        // check balances
        assertEq(a.balance, aBal - 2);
        assertEq(b.balance, 2);
    }

    function prove_label_works() public {
        hevm.label(address(this), "label");
        assert(true);
    }
}
