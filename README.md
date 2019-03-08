
# Idris-Even

A library to deal with even `Nat` and `Vect` of even length

## Installation

- clone the repo
- run `idris --install even.ipkg`
- import in your code with `Even.Vect` and `Even.Nat`
- run idris with `-p idris-even`

## How to use

Currently the API is mostly useful for `pairup` `unpair` `mapPairs` `deuxMapVect` and `toEvenVect`.

They are specialised in mapping elements two-by-two somtimes into a vector half the size of the 
original vector

### pairup

```
||| Takes an EvenVect and return a vect of pairs, preserves order
export pairup : EvenVect n a -> Vect n (a, a)
```

This takes an `EvenVect` and turns it into a `Vect` while keeping the order and the structure of
`EvenVect`. For example

```
ab : EvenVect 1 Nat
ab = [(1, 2)]

> pairup ab
> [(1,2)]: Vect 1 (Nat, Nat) 
```

### unpair

```
||| Given a vector of pairs, return a vector of even length, preseves order
export unpair : Vect n (a, a) -> EvenVect n a
```

This takes a Vector of identical pairs and length n and return a vector of even length with the same content

```
ab : Vect 1 (Nat, Nat)
ab = [(1,2)]

> unpair ab
> [(1, 2)] : EvenVect 1 Nat
```

### toEvenVect

```
||| Given a vector of length n + n, return a vector of even length
export toEvenVect : Vect (n + n) a -> EvenVect n a
```

Takes a Vector that is provably even (since any nat added to itself results in an even nat) and
return an `EvenVect` the order of the original vect is preseved even if the structure is a bit different.

```
ab : Vect (2 + 2) Nat
ab = [1,2,3,4]

> toEvenVect ab
> [(1, 2), (3, 4)] : EvenVect 2 Nat
```


### deuxMapVect

```
||| Given a vector of length n + n, map each element two by two 
||| to a vector of length n
export deuxMapVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
```

Using a function that combines two `a` into a `b`, this will reduce a vector of even length
into a vector of length twice smaller comprised of `b`. The order is preseved, the following
schema should help get an intuition as to what is happening.

```
1 :: 2 :: 3 :: 4      < Our vector of even length n

+ : Nat -> Nat -> Nat < Our function

1 + 2 :: 3 + 4        < How we construct the resulting vector

3 :: 7                < The result of length n / 2
```

As a concrete example

```
ab : Vect (2 + 2) Nat
ab = [1,2,3,4]

> deuxMapVect (+) ab
> [3, 7] : Vect 2 Nat
```

This is very similar to fold using another vector as accumulator.


## TODO

- `EvenVect` is missing the usual instances (Functor, Monoid, etc)
- Tests

## Contibuting

You are welcome to clone the project and open a pull request if you find a bug that you need to 
be fixed. If you feel like a feature is missing, open an issue.
