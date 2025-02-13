import Data.Vect


ident : (1 y : a) -> a
ident y =  y

duplicate : (1 y : a) -> (a,a)
duplicate y  = ?s

{-
--erasure

badNot : (0 x : Bool) -> Bool
badNot False = True
badNot True = False
-} 

data SBool : Bool -> Type where
     SFalse : SBool False
     STrue  : SBool True

sNot : (0 x: Bool) -> SBool x -> Bool
sNot _ SFalse = True
sNot _ STrue  = False

-- n available at run time 

vlen : {n : Nat} -> Vect n a -> Nat
vlen {n} xs = n


sumLengths0 : Vect m a -> Vect n a  -> Nat
sumLengths0 xs ys = ?sum0 --vlen xs + vlen ys


sumLengths : {m,n: Nat} ->  Vect m a -> Vect n a  -> Nat
sumLengths {m} {n} xs ys = ?sum --vlen xs + vlen ys


