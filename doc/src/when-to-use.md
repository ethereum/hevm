# When to use Symbolic Execution

In the cryptocurrency world, it is exceedingly easy to lose a [lot of
assets](https://chainsec.io/defi-hacks/) due to bugs. This risk can be alleviated
via a good test approach. Testing is a [discipline of its
own](https://en.wikipedia.org/wiki/Software_testing) that includes far more
than simple test cases. Normally, it should include an understanding of what
needs to be tested (i.e. scope) and for what types of issues (e.g.
malicious/accidental). It normally consists of a test approach, documenting
what has been tested and what remains to be tested. It should consist of a
number of unit tests, module tests, integration tests, user acceptance tests,
and exploratory testing. Written test cases normally consist of both positive
tests (i.e. correct input, correct behaviour), and negative tests (i.e.
incorrect input, no incorrect behaviour).

## Fuzzing versus Symbolic Execution

Fuzzing and symbolic execution fits within the [exploratory
testing](https://en.wikipedia.org/wiki/Exploratory_testing) part of
the testing methodology. Exploratory test cases usually have a set of
(sometimes implicit) pre- and postconditions, but the actual action (e.g.
function call) is performed by an external entity. Let's see an example:

```solidity
pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  uint balance;
  function test_overflow(uint amt) public {
    unchecked {
     balance += amt;
    }
    assert(balance >= amt);
  }
}
```

This function is easy to break by picking an `amt` that overflows `balance`,
so that the postcondition `balance > amt` will not hold. A
[fuzzer](https://en.wikipedia.org/wiki/Fuzzing) finds this kind of bug very
easily. However, fuzzers have trouble finding bugs that are either specifically
hidden (e.g. by a malicious developer), or that have a complicated code path
towards them. Let's see a simple one:


```solidity
pragma solidity ^0.8.19;
import "ds-test/test.sol";

contract MyContract is DSTest {
  uint balance;
  function prove_multiply(uint amt, uint amt2) public {
    require(amt != 1);
    require(amt2 != 1);
    require(amt < amt2);
    uint tmp;
    tmp = amt * amt2;
    if (tmp == 119274257) balance = 1337;
    else balance += tmp;
    assert(balance >= tmp);
  }
}
```

Calling this contract with `amt = 9479` and `amt2 = 12583` will set the balance
to 1337 which is less than `amt*amt2`, breaking the postcondition. However, a
fuzzer, e.g. [Echidna](https://github.com/crytic/echidna) will likely not find
those numbers, because `uint` has a potential range of `2**256` and so it'd be
looking for a needle in a haystack, when looking randomly. Here's how to run
Echidna on the multiplication test:

```solidity
pragma solidity ^0.8.19;
contract MyContract {
 // the rest is the same
}
```

Then run:
```
echidna --test-mode assertion src/multiply-test.sol
```

Echidna will terminate after 50k runs, with all tests passing. Notice that the
difference here, compared to the previous example, is that the overflow example
has _many_ different inputs that can break the postcondition, whereas here only
one can.

Hevm finds the bug in both of these functions. This is because
hevm (and symbolic execution frameworks in general) try to find the bug via
proof-directed search rather than using random inputs. In hevm, we try to prove
that there are no inputs to the test case such that given the preconditions, the
postconditions can be broken. While trying to construct this mathematical proof,
hevm finds a _countereexample_, an  input that breaks the postconditions:


```
$ hevm test
Checking 1 function(s) in contract src/multiply-test.sol:MyContract
[RUNNING] prove_multiply(uint256,uint256)
   [FAIL] prove_multiply(uint256,uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_multiply(9479,12583)

Checking 1 function(s) in contract src/overflow-test.sol:MyContract
[RUNNING] prove_overflow(uint256)
   [FAIL] prove_overflow(uint256)
   Counterexample:
     result:   Revert: 0x4e487b710000000000000000000000000000000000000000000000000000000000000001
     calldata: prove_overflow(00000000000000000000000000000000000000000000000100000000000000000182dad8c17bd5e89e8043a08ada90a6d5efdee4425f85cb863109783e158ba4fba908a0e6fae6c6b51002)
```

## Similarities and Differences to Other Tools

Fuzzers are exceedingly fast and efficient when there are many potential faults
with a function/contract, or if the faults are of a type that's easy to search
for (e.g. off-by-one). However, they rarely, if ever, find cases where the bug
is hidden deep in the branch logic, or needs very specific input parameters.
Hence, it is best to use fuzzers at first to find easy-to-find bugs, as fuzzers
are very efficient at that. Then, once the tests pass the fuzzer, it is
recommended to use a symbolic execution engine such as hevm.

While hevm is similar to [Halmos](https://github.com/a16z/halmos) and
[Kontrol](https://docs.runtimeverification.com/kontrol/overview/readme) in its
approach. However, it is quite different from static code analysis tools such
as [Oyente](https://github.com/enzymefinance/oyente),
[Slither](https://github.com/crytic/slither), and
[Mythril](https://github.com/ConsenSys/mythril). While these 3 tools typically
use some form of symbolic execution to try to validate their results, their
main method of operation is not via symbolic execution, and they can, and do,
report false positives.

Notice that static code analysis tools can find bugs that the author(s) didn't
write a test case for, as they typically have a (large) set of preconfigured
test-cases that they can report on, if they can find a way to violate them. Hence,
it may be valuable to run static analysis tools alongside symbolic execution tools
such as hevm.

Finally,
[SMTChecker](https://github.com/ethereum/solidity/blob/develop/docs/smtchecker.rst)
may also be interesting to run alongside hevm. SMTChecker is very different
from both approaches detailed above. While SMTChecker is capable of reliably
finding both reentrancy and loop-related bugs, the tools above can only do so
on a best effort basis. Hevm often reports a warning of incompleteness for
such problems, while static code analysis tools either report potential
positives or may even not discover them at all.
