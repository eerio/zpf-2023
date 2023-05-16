Require Import Lia.
Require Import List.

Print list.

Fixpoint sum (l : list nat) : nat :=
match l with
  nil => O
| cons a t => a + sum t
end.


(* use lia *)
Lemma or3: forall n , n=O \/ n=1 \/ n >=2.
Proof.
lia.
Qed.

Print In.

(* use lia *)
Lemma Pigeonhole: forall (l:list nat), sum l > length l -> exists x, In x l /\ x>=2.
intros.
induction l.
- inversion H.
- simpl in H.
  destruct (or3 a) as [H0 H1 H2].

  try rewrite H0 in H;
  simpl in H;
  assert (sum l > length l);
  try lia;
  assert (exists x: nat, In x l /\ x >= 2);
  try apply IHl;
  try apply H1;
  assert (sum l > length l);
  auto with arith;
  try destruct H2;
  try exists x;
  simpl.
  + split.
    * right. apply H2.
    * apply H2.
  + destruct H0.
    * rewrite H0 in H.
      simpl in H;
      assert (sum l > length l);
      lia;
      assert (exists x: nat, In x l /\ x >= 2);
      apply IHl;
      apply H1;
      assert (sum l > length l);
      auto with arith;
      destruct H2;
      exists x.
    * 

      
Qed.
