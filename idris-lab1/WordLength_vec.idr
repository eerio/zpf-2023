import Data.Vect


allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words


-- allLengths ["ala", "w", "kkkk"]
