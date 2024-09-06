## Aliasing in Act

Either:

1. introduce some notion of aliasing into our representation of EVM state (see below)
  - quite a deep rework of hevm
  - does it help with the combinatorial explosion or just move it around?

2. implement case splitting at the act level (as + case discovery)
  - should work, but bad cos combinatorial explosion

3. implement syntax in act that constrains the prestate to the non-aliased one (points to)
  - expressive and rigorus
  - resolves address / contract semantics in act in a satisfying way
  - cannot express aliasing

## SMT Encoding

```haskell
(Success
  state:
    (SetContract (Addr "a") (C ...)
    (SetContract (Addr "b") (C ...)
    AbstractState
    ))

  returndata:
    (WriteWord 0 (SLoad 0 (LookupContract (Addr "c") s).storage) AbstractBuf)
)

SMT:
  2d map: storage
  1d map: balances

smt type of state : SMTArray address (SMTArray word word)
(SLoad 0 (LookupContract (Addr "c") s).storage) ==> lookup 0 (lookup "c" state)
```

## Resolving Calls

```haskell
case lookupContract addr state of
  C {} => error "whatever we always did"
  LookupContract .... =>
    -- there is some aliasing, but the set of aliased addresses is bounded and known, and each one
    -- has known code. in this case we just branch and execute each one.
    -- probably SMT solver needed to resolve aliasing?
    _ => error "reason by cases"
    -- there are a few ways to do this:
    -- 1. dumbest possible way:
    --   set all storage to be AbstractStore and continue execution
    -- 2. a bit smarter:
    --   some kind of static analysis that determines which storage slots could actually be changed.
    --   havoc only those that could have been updated
    _ => error "completely unknown code"
```
