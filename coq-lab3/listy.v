Require Import List.

Print list.

Print "++".

Lemma append_assoc: forall A (l1 l2 l3: list A),  l1 ++(l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
intros.
induction l1.
- reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma append_nil : forall A (l: list A), l ++ nil = l.
Proof.
intros.
induction l.
- reflexivity.
- simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma length_append: forall A (l1 l2: list A), length (l1++l2) = length l1 + length l2.
Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.  
Qed.

Lemma length_map: forall A B (f:A-> B)(l: list A), length (map f l) = length l.
Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma length_zero: forall A (l:list A), length l = 0 <-> l = nil.
Proof.
intros.
induction l.
- simpl.
  easy.
- simpl.
  split.
  + intros.
   inversion H.
  + intros.
   inversion H.
Qed.
