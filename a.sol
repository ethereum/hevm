contract A {
    bytes public data;
    function stuff(uint a, uint b) public pure returns (uint) {
       unchecked {
         uint c = a + b/2;
         return c;
       }
    }
}
