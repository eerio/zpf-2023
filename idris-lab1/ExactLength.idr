data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

{-
exactLength0 : {m:Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength0 len input = case m == len of
                                 False => Nothing
                                 True => Just ?input

-}

{-
exactLength0 : (m:Nat) -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength0 m m input = Just input
exactLength0 m len input = Nothing
-}




















data EqNat : Nat -> Nat -> Type where
     Same : (x : Nat) -> EqNat x x

sameS : {k : Nat} -> {j : Nat} -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS {k=k} {j=k} (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              Just eq => Just (sameS eq)


exactLength  : {m : Nat} -> (len : Nat) -> 
               (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 Just (Same _) => Just ?inp
--                                 Just (Same m) => Just input




