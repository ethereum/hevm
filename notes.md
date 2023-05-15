# Decompilation

Lift bytecode to Expr.
Take list of interfaces from Act. For each one do a symbolic execution and produce a flattened list of Exprs.

We also run an abi exhaustiveness check, which constrains calldata to be none of the methods defined
in the act file, and checks that there are no reachable success states.

```haskell
decompile :: Contract -> ByteString -> IO (Map Interface [Expr End])
checkAbiExhaustiveness :: Contract -> ByteString -> IO Bool
```

# Lowering

```haskell
data Behaviour t = Behaviour
  { _name :: Id
  , _contract :: Id
  , _interface :: Interface
  , _preconditions :: [Exp ABoolean t] -- if preconditions are not satisfied execution is reverted
  , _case :: [Exp ABoolean t] -- if preconditions are satisfied and a case is not, some other instance of the bahaviour should apply
  , _postconditions :: [Exp ABoolean Timed]
  , _stateUpdates :: [Rewrite t]
  , _returns :: Maybe (TypedExp Timed)
  } deriving (Show, Eq)
```

each behaviour can be represented as a single `Success` leaf in Expr:

```haskell
Success (fmap actToExpr (_precondtions <> _case)) (rewritesToExpr _stateUpdates) (returnsToExpr _returns)
```

```haskell
contractToExpr :: Contract -> Map Interface [Expr End]
```

# Equivalence Checking

We reuse the existing Expr <-> Expr equivalence checker and

