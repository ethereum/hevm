import "ds-test/test.sol";

contract Loops is DSTest {

    function prove_loop(uint n) public {
        uint counter = 0;
        for (uint i = 0; i < n; i++) {
            counter++;
        }
        assertTrue(counter < 100);
    }
}
