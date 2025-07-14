import "forge-std/Test.sol";

contract SolidityTest is Test {

    function prove_conc_fail_somerev(uint x) public {
      if (x == 0) prove_manual_fail_allrev(x);
      else return;
    }

    function prove_conc_fail_allrev(uint x) public {
      assembly {
        // Load free memory pointer
        let ptr := mload(0x40)

        // Store Error selector (keccak256("Error(string)")) → 0x08c379a0
        mstore8(ptr, 0x08)
        mstore8(add(ptr, 0x01), 0xc3)
        mstore8(add(ptr, 0x02), 0x79)
        mstore8(add(ptr, 0x03), 0xa0)

        // Store data offset (string starts at 0x20)
        mstore(add(ptr, 0x04), 0x20)

        // Store string length (0x10 = 16 bytes for "assertion failed")
        mstore(add(ptr, 0x24), 0x10)

        // Store the string "assertion failed" (padded to 32 bytes)
        mstore(add(ptr, 0x44), "assertion failed")
        mstore(0x40, add(ptr, 0x80)) // Update free memory pointer

        // Revert with (offset, size = 0x64 = 100 bytes)
        revert(ptr, 0x64)
      }
    }

    // These are the SAME as above EXCEPT we allow "c" that overwrites the "a" in "assertion failed"
    // that is by default set to "x" instead of "a". Hence, these can be made to fail with c == "a"
    function prove_symb_fail_somerev_text(uint x, uint8 c) public {
      if (x == 0) prove_symb_fail_allrev_text(x, c);
      else return;
    }

    function prove_symb_fail_allrev_text(uint x, uint8 c) public {
      assembly {
        // Load free memory pointer
        let ptr := mload(0x40)

        // Store Error selector (keccak256("Error(string)")) → 0x08c379a0
        mstore8(ptr, 0x08)
        mstore8(add(ptr, 0x01), 0xc3)
        mstore8(add(ptr, 0x02), 0x79)
        mstore8(add(ptr, 0x03), 0xa0)

        // Store data offset (string starts at 0x20)
        mstore(add(ptr, 0x04), 0x20)

        // Store string length (0x10 = 16 bytes for "assertion failed")
        mstore(add(ptr, 0x24), 0x10)

        // Store the string "assertion failed" (padded to 32 bytes)
        mstore(add(ptr, 0x44), "xssertion failed")
        // c := 0x61 // Set c to 'a' (0x61 in hex) -- this certainly works
        mstore8(add(ptr, 0x44), c)
        mstore(0x40, add(ptr, 0x80)) // Update free memory pointer

        // Revert with (offset, size = 0x64 = 100 bytes)
        revert(ptr, 0x64)
      }
    }

    // This is the SAME as above EXCEPT we make the SELECTOR symbolic
    // if c is 0xa0 as above, then it will fail
    function prove_symb_fail_somerev_selector(uint x, uint8 c) public {
      if (x == 0) prove_symb_fail_allrev_selector(x, c);
      else return;
    }

    function prove_symb_fail_allrev_selector(uint x, uint8 c) public {
      assembly {
        // Load free memory pointer
        let ptr := mload(0x40)

        // Store Error selector (keccak256("Error(string)")) → 0x08c379a0
        mstore8(ptr, 0x08)
        mstore8(add(ptr, 0x01), 0xc3)
        mstore8(add(ptr, 0x02), 0x79)
        mstore8(add(ptr, 0x03), c)

        // Store data offset (string starts at 0x20)
        mstore(add(ptr, 0x04), 0x20)

        // Store string length (0x10 = 16 bytes for "assertion failed")
        mstore(add(ptr, 0x24), 0x10)

        // Store the string "assertion failed" (padded to 32 bytes)
        mstore(add(ptr, 0x44), "assertion failed")
        mstore(0x40, add(ptr, 0x80)) // Update free memory pointer

        // Revert with (offset, size = 0x64 = 100 bytes)
        revert(ptr, 0x64)
      }
    }
}
