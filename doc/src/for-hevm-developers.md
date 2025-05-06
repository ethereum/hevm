# General overview

To get an idea about what `hevm` is, see [CAV'24 paper](https://link.springer.com/content/pdf/10.1007/978-3-031-65627-9_22.pdf?pdf=inline%20link).
You can also check out a few [presentations](https://github.com/msooseth/hevm-presentation) by [@msooseth](https://github.com/msooseth).

# Debugging

## Printf-style debugging

Haskell offers a way to print messages anywhere in the code with [Debug.Trace](https://hackage.haskell.org/package/base-4.20.0.1/docs/Debug-Trace.html).
The simplest is `trace` which takes a string and a value and returns the same value while printing the string.
For example
```haskell
add x y = trace "Hello from add!" (x + y)
```

# Testing

`hevm` uses [Tasty](https://hackage.haskell.org/package/tasty-1.5/docs/Test-Tasty.html) framework for running tests, including [`QuickCheck`](https://hackage.haskell.org/package/tasty-quickcheck-0.11/docs/Test-Tasty-QuickCheck.html) for property-based testing.


## Running tests

The basic command to run the tests is:
```
cabal run test
```

For development, it might be beneficial to pass `devel` flag:
```
cabal run -f devel test
```

This should enable parallel compilation and test runs (see the config file `hevm.cabal`).

Additional parameters can be passed to the test runner after `--`. For example `cabal run test -- --help` will list all the additional parameters.

Some of the interesting options are `-p <PATTERN>` to filter only some of the tests and `--quickcheck-tests <NUMBER>` to control how many tests quickcheck will generate for each property test.

## On property-based testing

There are a few ways to control how many tests Quickcheck will generate per property.
By default, it generates 100 tests (satisfying the precondition).
This can be controlled by `maxSuccess` argument passed to Quickcheck, or, in Tasty framework, using `localOption (QuickCheckTests <N>)`.
Passing `--quickcheck-tests <N>` to the binary will change this value to `<N>`.
This value can be dynamically adjusted for a test group or a specific test.
For example, instead of `localOption` it is possible to use `adjustOption` for a test group.
The following ensures that for the following test group, the maximal value of the `QuickCheckTests` option is `50` (but if the current value is lower, it will be left unchanged).
```
adjustOption (\(Test.Tasty.QuickCheck.QuickCheckTests n) -> Test.Tasty.QuickCheck.QuickCheckTests (min n 50))
```

Similarly, the `maxSuccess` value can be modified for a single test. The following sets the number of tests generated to 20 for the particular test:
```
testProperty <property_name> $ withMaxSuccess 20 $ ...
```

# Profiling

## Profiling Haskell code

**NOTE:** Most of the time will likely be spent in the solver, and that will not show up when profiling Haskell application.

In order to build the application with profiling information, we need to pass `--enable-profiling` to `cabal`.
If we want to profile the test suite, we could run
```bash
cabal run test --enable-profiling -- +RTS -p
```
Note that `+RTS` means the next arguments will be passed to GHC and -p instructs the program to create a time profile report.
This report is written into the `.prof` file.
If we want to pass arguments to our executable, we have to indicate this with `-RTS`, for example, to profile run of only some tests, we would use

```bash
cabal run test --enable-profiling -- +RTS -p -RTS -p <test_to_profile>
```

