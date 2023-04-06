isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []

sum : (single : Bool) -> isSingleton single -> Nat
sum True x = x
sum False [] = 0
sum False (x :: xs) = x + sum False xs


id : a -> a
id = \x =>x

defId : (a : Type) -> a -> a
defId a = \x => x 

notId : {a : Type} -> a -> a
notId {a = Integer} x = x+1
notId x = x
