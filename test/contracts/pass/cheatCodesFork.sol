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
    function startPrank(address) external;
    function stopPrank() external;
    function deal(address,uint256) external;
    function createFork(string calldata urlOrAlias) external returns (uint256);
    function selectFork(uint256 forkId) external;
    function activeFork() external returns (uint256);
}

/// @dev This contract's state should depend on which fork we are on
contract TestState {
    uint256 public state;
    function setState(uint256 _state) external {
        state = _state;
    }
}

/// @dev This contract's state should be persistent across forks, because it's the contract calling `selectFork`
contract CheatCodesForkDeployee is DSTest {
    Hevm hevm = Hevm(HEVM_ADDRESS);
    address stateContract;
    uint256 forkId1;
    uint256 forkId2;
    uint256 persistentState;

    constructor() {
        stateContract = address(new TestState());
        forkId1 = hevm.createFork("foo"); // If the default fork's id is 0, then this would be 1
        forkId2 = hevm.createFork("bar"); // and this would be 2
        persistentState = 0;
    }

    function deployee_prove_ForkedState() external {
        hevm.selectFork(0);                             // Default fork
        assert(hevm.activeFork() == 0);                 // Check active fork
        persistentState = 1;                            // Make sure this contract maintains its own state across fork
        hevm.selectFork(forkId1);                       // Fork 1
        assert(hevm.activeFork() == forkId1);           //      Check active fork
        assert(TestState(stateContract).state() == 0);  //      Check initial external state
        assert(persistentState == 1);                   //      Check persistent state
        persistentState = 2;                            //      Set persistent state
        TestState(stateContract).setState(1);           //      Set unique external state
        hevm.roll(12345678);                            //      Set unique block number
        hevm.selectFork(forkId2);                       // Fork 2
        assert(hevm.activeFork() == forkId2);           //      Check active fork
        assert(TestState(stateContract).state() == 0);  //      Check initial external state
        assert(persistentState == 2);                   //      Check persistent state
        persistentState = 3;                            //      Set persistent state
        TestState(stateContract).setState(2);           //      Set unique external state
        hevm.roll(23456789);                            //      Set unique block number
        hevm.selectFork(forkId1);                       // Fork 1
        assert(hevm.activeFork() == forkId1);           //      Check active fork
        assert(block.number == 12345678);               //      Check unique block number
        assert(TestState(stateContract).state() == 1);  //      Check unique external state
        assert(persistentState == 3);                   //      Check persistent state
        persistentState = 4;                            //      Set persistent state
        TestState(stateContract).setState(0);           //      Set initial external state
        hevm.selectFork(forkId2);                       // Fork 2
        assert(hevm.activeFork() == forkId2);           //      Check active fork
        assert(block.number == 23456789);               //      Check unique block number
        assert(TestState(stateContract).state() == 2);  //      Check unique external state
        assert(persistentState == 4);                   //      Check persistent state
        persistentState = 5;                            //      Set persistent state
        TestState(stateContract).setState(0);           //      Set initial external state
        hevm.selectFork(forkId1);                       // Fork 1
        assert(hevm.activeFork() == forkId1);           //      Check active fork
        hevm.deal(address(this), 10);                   //      Get some eth
        payable(msg.sender).send(10);                   //      Send eth to msg.sender
        uint256 senderBalance = msg.sender.balance;     //      Record msg.sender's balance
        hevm.selectFork(forkId2);                       // Fork 2
        assert(hevm.activeFork() == forkId2);           //      Check active fork
        assert(msg.sender.balance == senderBalance);    //      Check msg.sender's balance
        hevm.selectFork(0);                             // Default fork
        assert(hevm.activeFork() == 0);                 //      Check active fork
        assert(persistentState == 5);                   //      Check persistent state
    }
}

/// @dev This contract's state should be persistent across forks, because it's the `msg.sender` when running `deployee_prove_ForkedState`.
///  We need this "deployer/deployee" architecture so that `msg.sender` will be concrete when running `deployee_prove_ForkedState`.
///  If we were to only use the `CheatCodesForkDeployee` contract, the `msg.sender` would be abstract.
contract CheatCodesFork is DSTest {
  CheatCodesForkDeployee testContract = new CheatCodesForkDeployee();
  function prove_ForkedState() external {
    testContract.deployee_prove_ForkedState();
  }
}
