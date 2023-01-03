# ADR 5: Inlining fully saturated functions

Date: 2022-12

## Authors

Marty Stumpf <marty.stumpf@iohk.io>

## Status

Accepted

## Context

As part of our effort to increase script capacity,
we take from [Plutonomy](https://github.com/well-typed/plutonomy),
which gives 15-30% speedup on benchmarks.
See [PLT-1044](https://input-output.atlassian.net/browse/PLT-1044).

The goal is to integrate what we know already works there and
also add optimizations we can do before UPLC (Plutonomy only applies optimization to UPLC).
We currently have an inliner pass for PIR and UPLC.
One of the optimization we can add is inlining of saturated functions in both PIR and UPLC.
From our analysis, this is one of the optimizations that contributes to the speedup in Plutonomy.

For example:

```haskell
let f x y = 1
    y = f q
in f a b 
```

we should inline `f` on line 3 (even though it’s used more than once), because it’s saturated,
i.e. it has all its arguments, and we can reduce it.
([PLT-1146](https://input-output.atlassian.net/browse/PLT-1146))

To do this we need to count the number of type/term lambda abstractions,
so we know how many term/type arguments they have.
We also need to decide whether or not to inline based on the call site, which we don’t currently.

## Decision

For a first round of implementation, we are adding a simplified pass.
We will refine the implementation over time.
In each round, we benchmark and test and investigate the results.

### The heuristic: Counting lambdas and arguments

In this inline pass we check for a binding that is a lambda abstraction and is fully applied in the body.

E.g.,

```haskell
let v = rhs in body
```

We pattern match the _rhs_ with `LamAbs` or `TyAbs` (lambda abstraction for terms or types),
and count the number of lambdas.
Then, in the _body_, we check for term or type application (`Apply` or `TyInst`) of _v_.

If _v_ is fully applied in the body, i.e., if

1. the number of type lambdas equals the number of type arguments applied, and
2. the number of term lambdas equals the number of term arguments applied, and

if other call site inlining conditions are satisfied, (we currently inline too little, this will be improved later, see below)

we inline _v_, i.e., replace its occurrence with _rhs_ in the _body_.
For the rest of the discussion here we focus on the conditions 1 and 2 only.

E.g., for

```haskell
let f = \x.\y.x+y in
    f 2 4
```

the _body_ `f 2 4` is a function application of `f`. Since `f` is fully applied, we inline `f`.

### Examples

Below are some examples that involve a _body_ that is not fully reducible/applied but following our heuristic is beneficial.

#### Example 1: function in body

```haskell
let f = \x . x
     g = \y . f
in g a
```

`f` and `g` each has 1 lambda. However, `g`'s _body_ includes `f` which also has a lambda.
Since we only count the number of lambdas, `g` is fully applied, and we inline.
`g a` reduces to `f`, which reduces the amount of code even though `f` has a lambda that is not applied.

#### Example 2: function as an argument

```haskell
let id :: forall a . a -> a
    id x = x
in id {int -> int} (\x -> x +1)
```

Here we have a type application for a function that takes one type variable.
I.e., it's fully applied in terms of type.
In terms of terms, `id` takes one argument, and is indeed applied to one.
So `id` is fully applied! And we inline it.

Reducing the _body_ `id {int -> int} (\x -> x +1)` leaves us `(\x -> x +1)`,
a function with 1 lambda. Even though it's not fully applied, inlining and reducing `id` reduces the amount of code, as desired.

#### Example 3: function application in _RHS_

```haskell
let f = (\x.\y.x+y) 4
in f 5
```

With beta-reduction, `f` becomes `\y.4+y` and it has 1 lambda.
The _body_ `f 5` is a fully applied function!
We can reduce it to 9.
However, because the _rhs_ `(\x.\y.x+y) 4` is a function application, not a lambda abstraction,
we won't inline it with the current implementation. This is something we may be able to improve.

### The implementation: Counting lambdas and applications

We run `countLam` to the _rhs_ of the binding:

```haskell
-- | Count the number of type and term lambdas in the RHS of a binding
countLam :: 
    Term tyname name uni fun a -- ^ the RHS
    -> (Natural, Natural) -- ^ Number of type lambdas, number of term lambdas
countLam = countLamInner 0 0
    where
      countLamInner ::
        Natural -- ^ Number of type lambdas of the function.
        -> Natural -- ^ Number of term lambdas of the function.
        -> Term tyname name uni fun a -- ^ The rhs term that is being counted.
        -> (Natural, Natural)
      countLamInner typeLambdas termLambdas (LamAbs _a _n _ty body) =
        -- If the term is a term lambda abstraction, increase the count of the number of term lambdas by one.
        -- Keep on examining the body.
        countLamInner typeLambdas (termLambdas + 1) body
      countLamInner typeLambdas termLambdas (TyAbs _a _n _kind body) =
        -- If the term is a type lambda abstraction, increase the count of the number of type lambdas by one.
        -- Keep on examining the body.
        countLamInner (typeLambdas + 1) termLambdas body
      countLamInner typeLambdas termLambdas _ = 
        -- whenever we encounter a body that is not a lambda abstraction, we are done counting
        (typeLambdas, termLambdas) 
```

To count the number of applied arguments, we already have something that collects the applications
([extractApps](
https://github.com/input-output-hk/plutus/blob/791e1dc0f6f5b9954da4c4d19e4597f5e75d0727/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Transform/Inline.hs#L138))
in the UPLC inliner. We can run `length` to the result to get the number for the UPLC inliner.
It's straight forward to implement this for the PIR inliner as well.

### The implementation: call site inlining

Another substantial component of this implementation is the actual inlining at the call site.
Details of this to be worked out.

## Future plans

We have plans to improve this pass so that it will catch more cases that are desirable,
and not inline undesirably.

### Add beta-reduction pass

If beta-reduction of _rhs_ is run before this pass, it can catch cases categorized by example 3.

### Add inline size heuristic

If we do some analysis of the inline size, we can better decide whether it's desirable to inline.
Plutonomy also [uses a similar heuristic](https://github.com/well-typed/plutonomy/blob/14b9bd46084db1b785b3a99d55f7f10d38165ee8/src/Plutonomy/Hereditary/Transform.hs#L266).

### Add more refined heuristic for call site inlining

See [PLT-1041](https://input-output.atlassian.net/browse/PLT-1041).
At the moment we inline any lambda with a trivial body.
This is too aggressive and has been observed to lead to size increases.
We will optimize this further in PLT-1041.
