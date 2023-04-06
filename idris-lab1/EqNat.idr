data EqNat : Nat -> Nat -> Type where
     Same : (x : Nat) -> EqNat x x

sameS : {k : Nat} -> {j : Nat} -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = Same (S k)


checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
{- does not work 
checkEqNat k k = Just (Same k)
checkEqNat _ _ = Nothing
-}

checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              Just eq => Just (sameS eq)
-}
-- the (EqNat 4 4) (Same (2+2)) 
