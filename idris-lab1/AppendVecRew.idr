import Data.Nat
import Data.Vect


append_nil : Vect m el -> Vect (plus m 0) el
append_nil  xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + k)) el -> Vect (plus m (S k)) el
append_xs  xs = rewrite sym (plusSuccRightSucc m k) in xs

append : Vect n el -> Vect m el -> Vect (m + n) el
append [] ys = append_nil ys
append (x :: xs) ys = append_xs (x :: append xs ys)


app: Vect n el -> Vect m el -> Vect (n + m) el
-- :gd 16 app
