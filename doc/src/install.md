# Quick Installation Guide

To fastest way to start using hevm is to install
  [Foundry](https://book.getfoundry.sh/getting-started/installation#using-foundryup),
  e.g. via
```
curl -L https://foundry.paradigm.xyz | bash
```

Next, you need to have either [Z3](https://github.com/Z3Prover/z3) or
[CVC5](https://cvc5.github.io/) installed. Often, these can be installed via:
```
$ sudo apt-get install z3
```
or similar. If you installed CVC5 instead, you will need to pass the flag
"--solver cvc5" to "hevm test" later.


Finally, download the static hevm binary from [the github
repository](https://github.com/ethereum/hevm/releases/) for your platform and
put it in your path so it can be executed via typing "hevm".

# How to Check if it Works

Once you have the above, you can go to the root of your forge-based project
and build it:
```
$ forge build
[⠒] Compiling...
[⠆] Compiling 34 files with 0.8.19
[⠔] Solc 0.8.19 finished in 2.12s
Compiler run successful.
```

Then run hevm on all functions prefixed with `prove_` as such:

```
$ hevm test
Checking 1 function(s) in contract src/contract-pass.sol:MyContract
[RUNNING] prove_pass(address,uint256)
   [PASS] prove_pass(address,uint256)
```

See [ds-test Tutorial](./ds-test-tutorial.md) for details.

Note that Foundry provides the solidity compiler, hence there is no need to
install solidity separately.
