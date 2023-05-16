Require Import ZArith.


Inductive ftree : nat -> Type :=
| Leaf : ftree O
| Node : forall n, Z -> ftree n -> ftree n -> ftree (S n).


(*
Definition root (n:nat)(t:ftree (S n)): Z :=
match t with
| Node n z l r => z
end.


Eval compute in root 0 (Node 0 3 Leaf Leaf).

Check Z.of_nat.

Fixpoint zrob (n:nat): ftree n := 
match n with
| O => Leaf
| S k => Node k (Z.of_nat k) (zrob k) (zrob k)
end.

Eval compute in root 5 (zrob 6). 

*)

Check Node.
Arguments Node [n].


Definition rooti {n:nat}(t:ftree (S n)): Z :=
match t with
| Node z l r => z
end.

Eval compute in rooti (Node 3 Leaf Leaf).

Fixpoint zrobi (n:nat): ftree n := 
match n with
| O => Leaf
| S k => Node (Z.of_nat k) (zrobi k) (zrobi k)
end.

Eval compute in rooti (Node 3 Leaf Leaf).

Eval compute in rooti (zrobi 6).
