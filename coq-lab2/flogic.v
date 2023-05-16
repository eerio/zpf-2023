

Lemma and_comm: forall R Q, R /\ Q -> Q /\ R.
Proof.
intros.
destruct H.
split.
(*constructor.*)
 * assumption.
 * assumption.
Qed.

Print and_comm.
Print and.
Check and_ind.
(*
and_ind
     : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P*)

(* destruct robi mniej więcej to co:

apply (and_ind (A:=R)(B:=Q)); try assumption.
intros. 
*)


Lemma or_comm: forall P Q, P \/ Q -> Q \/ P.
Proof.
intros.
destruct H.
 * constructor 2. 
   assumption.
 * constructor 1.
   assumption.
Qed.

Print or.
Print or_comm.

Check or_ind.
(* or_ind 
     :forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P*)

Print iff.

Lemma Iff_or_comm: forall A B, A \/ B <-> B \/ A.
intros.
split; apply or_comm.
Qed.


Print False.
Check False_ind.

Lemma FalseImpliesAny: False -> 2+2=5.
Proof.
intro.
destruct H.
Qed.



Lemma negations: forall P Q :Prop, ~P -> ~ ~ P -> Q.
Proof.
intros.
(*contradiction.*)
unfold not in H0.
unfold not in H.
(*destruct H0.
assumption.*)
exfalso.
apply H0.
assumption.
Qed.


Print ex.


(*Lemma istnieje1: @ex nat (fun x:nat => x+1 = 2).*)

Lemma istnieje1: exists x, x+1=2.
Proof.
exists 1.
simpl.
trivial.
Qed.

Lemma istnieje2: forall m n, (exists x, x+n = m) -> (n=m) \/ (exists k, m = S k).
Proof.
intros.
destruct H.
destruct x.
(*destruct x eqn:?.*)
* left.
  simpl in H.
  assumption.
* right.
  simpl in H.
  exists (x+n).
  symmetry.
  assumption.
Qed.
 

Definition Double_neg : Prop := forall P:Prop, ~~P -> P.

Definition Exm : Prop := forall P : Prop, P \/ ~P.

Definition Classical_impl : Prop := forall P Q:Prop, (P -> Q) -> ~P \/ Q.

Definition Peirce : Prop := forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition Not_forall_not_exists : Prop :=
           forall (A:Type)(P:A->Prop), ~(forall x:A, ~P x) -> ex P.

Check negations.


Lemma  Exm_Double_neg : Exm -> Double_neg.
Proof.
 unfold Double_neg.
 intros H P.
 unfold Exm in H. 
 destruct (H P) as [p | p'].
 - intro;assumption.
 -  (* generalize p'.*) 
   apply negations.
   assumption.
Qed.


