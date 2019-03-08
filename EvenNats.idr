module EvenNats

import NatProofs
%default total

data EvenNat : Nat -> Type where   
  ZEven : EvenNat Z
  SSucc : EvenNat n -> EvenNat (S (S n))

toNat : EvenNat n -> Nat 
toNat ZEven = 0 
toNat (SSucc x) = S (S (toNat x)) 

Uninhabited (EvenNat (S Z)) where   
  uninhabited ZEven impossible   
  uninhabited (SSucc _) impossible 

notEven : (contra : EvenNat k -> Void) -> EvenNat (S (S k)) -> Void 
notEven contra (SSucc x) = contra x 

isEven : (n : Nat) -> Dec (EvenNat n) 
isEven Z = Yes ZEven 
isEven (S Z) = No absurd 
isEven (S (S k)) with (isEven k)
  isEven (S (S k)) | (Yes prf) = Yes $ SSucc prf
  isEven (S (S k)) | (No contra) = No (notEven contra)

evenNatSuccPlusEvenNat : EvenNat (S (k + (S k))) = EvenNat (S (S (k + k)))
evenNatSuccPlusEvenNat = cong $ sym evenNatSuccPlus

triviallyEven : {n : Nat} -> EvenNat (n + n)
triviallyEven {n = Z} = ZEven
triviallyEven {n = (S k)} = rewrite evenNatSuccPlusEvenNat {k} in (SSucc triviallyEven)
