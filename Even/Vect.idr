
module EvenVect

import Data.Vect
import Even.NatProofs

%default total 

||| Constructs a vector of even length. The Nat index is half the length of thevector
||| Which mean EvenVect n a has length 2 * n
public export data EvenVect : Nat -> Type -> Type where
  Nil : EvenVect Z a
  (::) : (a, a) -> EvenVect n a -> EvenVect (S n) a

replicate : (len : Nat) -> a -> EvenVect len a
replicate Z x = []
replicate (S k) x = (x, x) :: replicate k x

Functor (EvenVect n) where
  map func [] = []
  map func ((a, b) :: y) = (func a, func b) :: map func y

Applicative (EvenVect n) where
  pure x {n} = replicate n x
  [] <*> [] = []
  ((f, g) :: z) <*> ((a, b) :: w) = (f a, g b) :: (z <*> w)

Foldable (EvenVect n) where
  foldr func init [] = init
  foldr func init ((a, b) :: ys) = let f = func a init 
                                       s = func b f in
                                       foldr func s ys
  foldl func init [] = init
  foldl func init ((a, b) :: ys) = let end = foldl func init ys
                                       prev = func end b in
                                       func prev a

wrapPair : Applicative f => f a -> f a -> f (a, a)
wrapPair x y = (pure MkPair) <*> x <*> y

Traversable (EvenVect n) where
  traverse f [] = [| [] |]
  traverse f ((x, y) :: xs) = [| wrapPair (f x) (f y) :: traverse f xs |]


Eq a => Eq (EvenVect n a) where
  [] == [] = True
  (x :: xs) == (y :: ys) = x == y && (xs == ys)

Ord a => Ord (EvenVect n a) where
  compare [] [] = EQ
  compare (x :: xs) (y :: ys) = compare x y `thenCompare` compare xs ys


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

||| Using a function that splits an `a` into two `b`s map a Vect n a into an EvenVect b of length n
export mapEven : (a -> (b, b)) -> Vect n a -> EvenVect n b
mapEven f [] = []
mapEven f (x :: xs) = f x :: mapEven f xs

||| Using a function that splits an `a` into two `b`s map a Vect n a into a Vect twice its length
||| containing `b`s
export mapEvenVect : (a -> (b, b)) -> Vect n a -> Vect (n + n) b
mapEvenVect f xs = extract $ mapEven f xs

||| Map a vector of even length to a vector, combining elements two by two
export mapPairs : (a -> a -> b) -> EvenVect n a -> Vect n b
mapPairs f [] = []
mapPairs f ((a, b) :: xs) = f a b :: mapPairs f xs

||| Given a vector of length n + n, map each element two by two
||| to a vector of length n
export deuxMapVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
deuxMapVect f xs = mapPairs f $ toEvenVect xs
