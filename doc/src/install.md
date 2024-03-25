# Quick Installation Guide

To fastest way to start using hevm, is:
* Install
  [Foundry](https://book.getfoundry.sh/getting-started/installation#using-foundryup),
  often via `curl -L https://foundry.paradigm.xyz | bash`
* Download the static hevm binary from [the github
  repository](https://github.com/ethereum/hevm/releases/) for your platform and
  put it in your path so it can be executed via typing "hevm".

Once you have the above, you can go to the root of your forge-based project,
build with `forge build` and then and issue `hevm test`, which will run all
tests of your project that start with `prove_` or `proveFalse_`. See
[ds-test-based Testing](./ds-test-tutorial.md) for details.

Note that Foundry provides the solidity compiler, hence there is no need to
install solidity separately.
