# `hevm equivalence`

```plain
Usage: hevm equivalence [--code-a TEXT] [--code-b TEXT] [--code-a-file STRING]
                        [--code-b-file STRING] [--sig TEXT] [--arg STRING]...
                        [--calldata TEXT] [--smttimeout NATURAL]
                        [--max-iterations INTEGER] [--solver TEXT]
                        [--num-solvers NATURAL] ...
```

Symbolically execute both the code given in `--code-a` and `--code-b` and try
to prove equivalence between their outputs and storages. For a full listing of
options, see `hevm equivalence --help`. For common options, see
[here](./common-options.md).

## Simple example usage

```shell
$ solc --bin-runtime "contract1.sol" | tail -n1 > a.bin
$ solc --bin-runtime "contract2.sol" | tail -n1 > b.bin
$ hevm equivalence --code-a-file a.bin --code-b-file b.bin
```

## Calldata size limits

If `--sig` is given, calldata is assumed to take the form of the function
given. If `--calldata` is provided, a specific, concrete calldata is used. If
neither is provided, a fully abstract calldata of at most `2**64` byte is
assumed. Note that a `2**64` byte calldata would go over the gas limit, and
hence should cover all meaningful cases. You can limit the buffer size via
`--max-buf-size`, which sets the exponent of the size, i.e. 10 would limit the
calldata to `2**10` bytes.

## What constitutes equivalence

The equivalence checker considers two contracts equivalent if given the
same calldata they:
- return the same value
- have the same storage
- match on the success/failure of the execution
Importantly, logs are *not* considered in the equivalence check. Hence,
it is possible that two contracts are considered equivalent by `hevm equivalence` but
they emit different log items. Furthermore, gas is explicitly not considered,
as in many cases, the point of the equivalence check is to ensure that the
contracts are functionally equivalent, but one of them is more gas efficient.

For example, two contracts that are:

```
PUSH1 3
```

And

```
PUSH1 4
```

Are considered *equivalent*, because they don't put anything in the return
data, are not different in their success/fail attribute, and don't touch
storage. However, these two are considered different:

```
PUSH1 3
PUSH1 0x20
MSTORE
PUSH1 0x40
PUSH1 0x00
RETURN
```

and:


```
PUSH1 4
PUSH1 0x20
MSTORE
PUSH1 0x40
PUSH1 0x00
RETURN
```

Since one of them returns a 3 and the other a 4. We also consider contracts different when
they differ in success/fail. So these two contracts:

```
PUSH1 0x00
PUSH1 0x00
RETURN
```

and:

```
PUSH1 0x00
PUSH1 0x00
REVERT
```

Are considered different, as one of them reverts (i.e. fails) and the other
succeeds.

## Creation code equivalence

If you want to check the equivalence of not just the runtime code, but also the
creation code of two contracts, you can use the `--creation` flag.  For example
these two contracts:

```solidity
contract C {
  uint private immutable NUMBER;
  constructor(uint a) {
    NUMBER = 2;
  }
  function stuff(uint b) public returns (uint256) {
    unchecked{return 2+NUMBER+b;}
  }
}
```

And:

```solidity
contract C {
  uint private immutable NUMBER;
  constructor(uint a) {
    NUMBER = 4;
  }
  function stuff(uint b) public returns (uint256) {
    unchecked {return NUMBER+b;}
  }
}
```

Will compare equal when compared with `--create` flag:

```shell
solc --bin a.sol | tail -n1 > a.bin
solc --bin b.sol | tail -n1 > b.bin
cabal run exe:hevm equivalence -- --code-a-file a.bin --code-b-file b.bin --create
```

Notice that we used `--bin` and not `--bin-runtime` for solc here. Also note that
in case `NUMBER` is declared `public`, the two contracts will not be considered
equivalent, since solidity will generate a getter for `NUMBER`, which will
return 2/4 respectively.

## Further reading

For a tutorial on how to use `hevm equivalence`, see the [equivalence checking
tutorial](symbolic-execution-tutorial.html).
