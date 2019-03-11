module Even.List

import Even.Vect
import Data.Vect

export extract : List (a, a) -> List a
extract [] = []
extract ((x, y) :: xs) = x :: y :: extract xs

||| Given a list of pair construct a vector of even length
export fromPairList : (l : List (a, a)) -> EvenVect (length l) a
fromPairList = fromList

||| Given a list of pairs construct a vector twice the length of the list
export pairListToVect : (l : List (a, a)) -> Vect (length l + length l) a
pairListToVect l = extract $ fromPairList l

||| Attempts to convert a list into an even vector
export maybeEvenVect : List a -> Maybe (n ** EvenVect n a)
maybeEvenVect [] = Just (Z ** [])
maybeEvenVect (x :: []) = Nothing
maybeEvenVect (x :: (y :: xs)) with (maybeEvenVect xs)
  maybeEvenVect (x :: (y :: xs)) | Nothing = Nothing
  maybeEvenVect (x :: (y :: xs)) | (Just (m ** ts)) = Just (S m ** ((x, y) :: ts))

