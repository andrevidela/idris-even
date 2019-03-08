
module EvenVect

import Data.Vect
import NatProofs

%default total 

data EvenVect : Nat -> Type -> Type where
  Nil : EvenVect Z a
  (::) : (a, a) -> EvenVect n a -> EvenVect (S n) a

pairup : EvenVect n a -> Vect n (a, a)
pairup [] = []
pairup (x :: y) = x :: pairup y

unpair : Vect n (a, a) -> EvenVect n a
unpair [] = []
unpair (x :: xs) = x :: unpair xs

congVect : a = b -> Vect a c = Vect b c
congVect Refl = Refl

vectPlusSuccRight : Vect (S (S (k + k))) a = Vect (S (k + (S k))) a
vectPlusSuccRight = congVect evenNatSuccPlus

evenVectSuccRight : Vect (S (k + (S k))) a -> Vect (S (S (k + k))) a
evenVectSuccRight xs {k} {a} = rewrite vectPlusSuccRight {k} {a} in xs

toEvenVect : Vect (n + n) a -> EvenVect n a
toEvenVect xs {n = Z} = []
toEvenVect xs {n = (S k)} with (evenVectSuccRight xs)
  toEvenVect xs {n = (S k)} | (x :: (y :: ys)) = (x, y) :: toEvenVect ys

mapPairs : (a -> a -> b) -> EvenVect n a -> Vect n b
mapPairs f [] = []
mapPairs f ((a, b) :: xs) = f a b :: mapPairs f xs

deuxMapVect : (a -> a -> b) -> Vect (n + n) a -> Vect n b
deuxMapVect f xs = mapPairs f $ toEvenVect xs
