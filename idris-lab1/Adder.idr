
AdderType : (numargs : Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next : numType) -> AdderType k numType

adder : Num numType => (numargs : Nat) -> numType -> AdderType numargs numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)


id : {a: Type} -> a -> a
id x = x

adderInt : (n : Nat) -> AdderType n Int
adderInt x = adder x 0

-- addreInt 2 3 4 
-- adder 2 0 3 4
