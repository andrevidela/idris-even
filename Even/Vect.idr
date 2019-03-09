
module EvenVect

import Data.Vect
import NatProofs

%default total 

||| Constructs a vector of even length. The Nat index is half the length of thevector
||| Which mean EvenVect n a has length 2 * n
public export data EvenVect : Nat -> Type -> Type where
  Nil : EvenVect Z a
  (::) : (a, a) -> EvenVect n a -> EvenVect (S n) a

congVect : a = b -> Vect a c = Vect b c
congVect Refl = Refl

vectPlusSuccRight : (k : Nat) -> (a : Type) -> Vect (S (S (k + k))) a = Vect (S (k + (S k))) a
vectPlusSuccRight k a = congVect evenNatSuccPlus

evenVectSuccRight : (k : Nat) -> (a : Type) -> Vect (S (k + (S k))) a -> Vect (S (S (k + k))) a
evenVectSuccRight k a xs = rewrite vectPlusSuccRight k a in xs

||| Takes an EvenVect and return a vect of pairs, preserves order
export pairup : EvenVect n a -> Vect n (a, a)
pairup [] = []
pairup (x :: y) = x :: pairup y

||| Extracts the pairs of an EvenVect into a Vect twice its length preserving order
export extract : EvenVect n e -> Vect (n + n) e
extract [] = []
extract ((a, b) :: y) {n=(S k)} {e} = rewrite sym $ vectPlusSuccRight k e in
                                              a :: b :: extract y

||| Given a vector of pairs, return a vector of even length, preseves order
export unpair : Vect n (a, a) -> EvenVect n a
unpair [] = []
unpair (x :: xs) = x :: unpair xs

||| Given a vector of length n + n, return a vector of even length
export toEvenVect : Vect (n + n) a -> EvenVect n a
toEvenVect xs {n = Z} = []
toEvenVect xs {n = (S k)} {a} with (evenVectSuccRight k a xs)
  toEvenVect xs {n = (S k)} | (x :: (y :: ys)) = (x, y) :: toEvenVect ys

||| Given a list of pair construct a vector of even length
export fromPairList : (l : List (a, a)) -> EvenVect (length l) a
fromPairList ls with (fromList ls)
  | vs = unpair vs

||| Given a list of pairs construct a vector twice the length of the list
export pairListToVect : (l : List (a, a)) -> Vect (length l + length l) a
pairListToVect l = extract $ fromPairList l

||| Map a vector of even length to a vector, combining elements two by two
export mapPairs : (a -> a -> b) -> EvenVect n a -> Vect n b
mapPairs f [] = []
mapPairs f ((a, b) :: xs) = f a b :: mapPairs f xs

||| Given a vector of length n + n, map each element two by two
||| to a vector of length n
export deuxMapVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
deuxMapVect f xs = mapPairs f $ toEvenVect xs
