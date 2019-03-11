
# Idris-Even

A library to deal with even `Nat` and `Vect` of even length

## Installation

- clone the repo
- run `idris --install even.ipkg`
- import in your code with `Even.Vect` and `Even.Nat`
- run idris with `-p idris-even`

## How to use

We define a set of function that operate on `Vect` and `EvenVect`, allowing to convert from
one to the other and allowing the API of `EventVect` to be compatible with `Vect` of size
`n + n.

### EvenVect

`EvenVect` is an alias for `Vect n (a, a)`, it's a vector that contains `n + n` elements.
It packs elements in pairs to encode the fact that the number of elements is a multiple of
2.

### extract

```
||| Extracts the elements of an EvenVect into a Vect twice its length preserving order
extract : EvenVect n e -> Vect (n + n) e
```

Given a vector of even length, converts into a vector of size `n + n` where `n` is half the
size of the vector. The order is preseved as demonstrated by the following example:

```
v : EvenVect 2 Nat
v = [(1,2) , (3,4)]

> extract v
> [1, 2, 3, 4] : Vect 4 Nat
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

### mapSplit

```
||| Using a function that splits an `a` into two `b`s, map a Vect n into a vector of even length
mapSplit : (a -> (b, b)) -> Vect n a -> EvenVect n b
```

Using a function that splits one `a` into two `b`s, creates an `EvenVect` of `b` values.

### mapJoin

```
||| Map a vector of even length to a vector, combining elements two by two
mapJoin : (a -> a -> b) -> EvenVect n a -> Vect n b
```

Using a function that combines two `a`s into a single `b`, create a `Vect` of length half the
size of the original vector containing values of `b`.

### mapSplitVect

```
||| Using a function that splits an `a` into two `b`s map a Vect n a into a Vect twice its length
||| containing `b`s
mapSplitVect : (a -> (b, b)) -> Vect n a -> Vect (n + n) b
```

Using a function that splits one `a` into two `b`s, this function takes a `Vect` of arbitrary
length and creates a `Vect` twice its size using the newly created `b` values.

### mapJoinVect

```
||| Given a vector of length n + n, map each element two by two 
||| to a vector of length n
export mapJoinVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
```

Using a function that combines two `a` into a `b`, this will reduce a vector of even length
into a vector of length twice smaller comprised of `b` values. The order is preseved, the 
following schema should help get an intuition as to what is happening.

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

> mapJoinVect (+) ab
> [3, 7] : Vect 2 Nat
```

This is very similar to fold using another vector as accumulator.


## TODO

- `EvenVect` is missing the usual instances (Functor, Monoid, etc)
- Tests

## Contibuting

You are welcome to clone the project and open a pull request if you find a bug that you need to 
be fixed. If you feel like a feature is missing, open an issue.
