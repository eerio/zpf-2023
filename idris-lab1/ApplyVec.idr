import Data.Vect


vApp : Vect n (a -> b) -> Vect n a -> Vect n b
vApp  []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as


{-
vApp : forall a. forall b. forall n. Vect n (a -> b) -> Vect n a -> Vect n b
vApp []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as
-}

{-
vApp : {a : Type} -> {b : Type} -> {n : Nat} ->  Vect n (a -> b) -> Vect n a -> Vect n b
vApp {n = Z} []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as
-}


{- Does not type check

vApp : (a:Type) -> (b:Type) -> (n:Nat) -> Vect n (a -> b) -> Vect n a -> Vect n b
vApp  []       []         = []
vApp  (f :: fs) (a :: as) = f a :: vApp fs as
-}

{-
vApp : (a:Type) -> (b:Type) -> (n:Nat) -> Vect n (a -> b) -> Vect n a -> Vect n b
vApp x y _ []       []         = []
vApp x y _ (f :: fs) (a :: as) = f a :: vApp x y _fs as
-}
