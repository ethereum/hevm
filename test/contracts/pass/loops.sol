import "forge-std/Test.sol";

contract Loops is Test {

    function prove_loop(uint n) public {
        uint counter = 0;
        for (uint i = 0; i < n; i++) {
            counter++;
        }
        assertTrue(counter < 100);
    }
}
