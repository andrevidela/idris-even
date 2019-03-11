
module EvenVect

import Data.Vect
import Even.NatProofs

%default total 
%access export

||| Constructs a vector of even length. The Nat index is half the length of thevector
||| Which mean EvenVect n a has length 2 * n
public export EvenVect : Nat -> Type -> Type
EvenVect size elems = Vect size (elems, elems)

private
congVect : a = b -> Vect a c = Vect b c
congVect Refl = Refl

private
vectPlusSuccRight : (k : Nat) -> (a : Type) -> Vect (S (S (k + k))) a = Vect (S (k + (S k))) a
vectPlusSuccRight k a = congVect evenNatSuccPlus

private
evenVectSuccRight : (k : Nat) -> (a : Type) -> Vect (S (k + (S k))) a -> Vect (S (S (k + k))) a
evenVectSuccRight k a xs = rewrite vectPlusSuccRight k a in xs

||| Extracts the elements of an EvenVect into a Vect twice its length preserving order
extract : EvenVect n e -> Vect (n + n) e
extract [] = []
extract ((a, b) :: y) {n=(S k)} {e} = rewrite sym $ vectPlusSuccRight k e in
                                              a :: b :: extract y

||| Given a vector of length n + n, return a vector of even length
toEvenVect : Vect (n + n) a -> EvenVect n a
toEvenVect xs {n = Z} = []
toEvenVect xs {n = (S k)} {a} with (evenVectSuccRight k a xs)
  toEvenVect xs {n = (S k)} | (x :: (y :: ys)) = (x, y) :: toEvenVect ys

||| Using a function that splits an `a` into two `b`s, map a Vect n into a vector of even length
mapSplit : (a -> (b, b)) -> Vect n a -> EvenVect n b
mapSplit f [] = []
mapSplit f (x :: xs) = f x :: mapSplit f xs

||| Map a vector of even length to a vector, combining elements two by two
mapJoin : (a -> a -> b) -> EvenVect n a -> Vect n b
mapJoin f [] = []
mapJoin f ((a, b) :: xs) = f a b :: mapJoin f xs

||| Using a function that splits an `a` into two `b`s map a Vect n a into a Vect twice its length
||| containing `b`s
mapSplitVect : (a -> (b, b)) -> Vect n a -> Vect (n + n) b
mapSplitVect f xs = extract $ mapSplit f xs

||| Given a vector of length n + n, map each element two by two
||| to a vector of length n, preserves order.
mapJoinVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
mapJoinVect f xs = mapJoin f $ toEvenVect xs

