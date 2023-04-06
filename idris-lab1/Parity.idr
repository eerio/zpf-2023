module Parity
import Data.Nat

data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))



parity0 : (n:Nat) -> Parity n
parity0 Z     = Even {n = Z}
parity0 (S Z) = Odd {n = Z}
parity0 (S (S k)) with (parity0 k)
    parity0 (S (S (j + j)))     | Even = let resE = (Even {n=S j}) in ?Erhs
    parity0 (S (S (S (j + j)))) | Odd  = let resO = (Odd {n=S j}) in ?Orhs




parity : (n:Nat) -> Parity n
parity Z     = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even = let resE = (Even {n=S j}) in 
       rewrite plusSuccRightSucc j j in resE
    parity (S (S (S (j + j)))) | Odd  = let resO = (Odd {n=S j}) in 
       rewrite plusSuccRightSucc j j in resO

-- Data.Nat.plusSuccRightSucc : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right

-- plusSuccRightSucc j j : S (j+j) = j + S j
-- resE : parity (S j + S j), resE : parity S (j + S j)
-- result needs to be in parity (S (S (j + j)) 

parity2 : (n : Nat) -> Parity n
parity2 Z = Even {n = Z}
parity2 (S Z) = Odd {n = Z}
parity2 (S (S k)) with (parity2 k)
  parity2 (S (S (j + j))) | Even
      = rewrite plusSuccRightSucc j j in Even {n = S j}
  parity2 (S (S (S (j + j)))) | Odd
      = rewrite plusSuccRightSucc j j in Odd {n = S j}

