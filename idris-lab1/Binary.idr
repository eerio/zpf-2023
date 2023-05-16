module Main

import Data.Nat

data Binary : Nat -> Type where
    BEnd : Binary Z
    BO : Binary n -> Binary (n + n)
    BI : Binary n -> Binary (S (n + n))

-- BO BI BEnd: Binary 2 represents 2 = (10)_2

Show (Binary n) where
    show (BO x) = show x ++ "0"
    show (BI x) = show x ++ "1"
    show BEnd = ""

data Parity : Nat -> Type where
   Even : {n: Nat} -> Parity (n + n)
   Odd  : {n: Nat} -> Parity (S (n + n))


parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j))) | Even
      = rewrite plusSuccRightSucc j j in Even {n = S j}
  parity (S (S (S (j + j)))) | Odd 
      = rewrite plusSuccRightSucc j j in Odd {n = S j}



natToBin : (n:Nat) -> Binary n
natToBin Z = BEnd
natToBin (S k) with (parity k)
   natToBin (S (j + j))     | Even {n = j} = BI (natToBin j)
   natToBin (S (S (j + j))) | Odd {n = j} -- = ?h $ BO (natToBin (S j))
           = rewrite (plusSuccRightSucc j j) in  BO (natToBin (S j))


main : IO ()
main = do putStr "Enter a number: "
          x <- getLine
          print (natToBin (fromInteger (cast x)))

          

