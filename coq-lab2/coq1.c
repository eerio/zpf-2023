Fixpoint len {A: Type} (l: list A) :=
  match l with
    nil => 0
  | x::xs=> 1 + len xs
end.

Fixpoint mapi {A B: Type} (f: A-> B) l :=
  match l with 
    nil => nil
    | x: xs => (f x) :: mapi f xs
end.