Set Implicit Arguments.
Require Import List.
Require Import Eqdep.
Require Import Eqdep_dec.
Require Import Lia.


(*
This file contains a variety of theorems useful for using dependently-typed
vectors in the Coq language. The theorems and auxiliary lemmas have been proved
by the author (Pawel Balawender) as part of the Advanced Functional Programming
course at the University of Warsaw. The author of the assignment and the grader
is Daria Walukiewicz-Chrząszcz, University of Warsaw. It is important to note
that the theorems require an additional axiom: Uniqueness of Identity Proofs.
Without assuming it, it is impossible to prove theorems using the equality sign `=`
*)

Section filterL.
(*------------------------------------------------------------------
Nondependent case : filter on lists
--------------------------------------------------------------------
*)

Print list.

Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.

Fixpoint filterL (l:list A) : list A :=
match l with
| nil => nil
| cons a l' => if P_dec a then cons a (filterL l') else filterL l'
end.

Fixpoint countPL (l : list A) := 
match l with 
| nil => O
| cons x l' => if P_dec x then S (countPL l') else countPL l'
end.

(* 
Prove lemmas cPL0, cPL1, cPL2 and cPL3 
*)

Lemma cPL0: forall (l:list A), length (filterL l) = countPL l.
Proof.
intro l.
induction l.
- reflexivity. 
- simpl.
  destruct P_dec.
  + simpl.
    f_equal.
    apply IHl.
  + apply IHl.
Qed.

Print Forall.

Lemma cPL1: forall (l:list A), countPL l = 0 -> 
           Forall (fun x => ~P x) l.
Proof.
intros l H.
induction l.
- constructor 1. 
- constructor 2;
  try apply IHl;
  simpl in H;
  destruct P_dec in H;
  try congruence;
  try assumption.
Qed.

Lemma cPL2_aux: forall (l:list A), countPL l <= length l.
Proof.
intro l.
induction l.
- constructor.
- simpl.
  destruct P_dec; lia.
Qed.

Lemma cPL2: forall (l:list A), countPL l = length l -> Forall P l.
Proof.
intros l H.
induction l.
- constructor.
- simpl in H.
  destruct P_dec.
  + assert (countPL l = length l).
    congruence.
    constructor.
    apply p.
    apply IHl.
    apply H0.
  + exfalso.
    pose proof (cPL2_aux l).
    lia.
Qed.

Lemma cPL3: forall (l:list A), Forall P (filterL l).
Proof.
intro l.
induction l.
- constructor.
- simpl.
  destruct P_dec;
  try constructor;
  assumption.
Qed.

End filterL.


Section filterV.
(*------------------------------------------------------------------
Dependent case: filter on vectors
--------------------------------------------------------------------
*)


Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.


Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, A -> vector n -> vector (S n).

Arguments Vcons {_} _ _.

(* Write the definition of countPV on vectors: *)
Fixpoint countPV {n:nat} (v : vector n) : nat :=
  match v with
  | Vnil => 0
  | Vcons x v' => if P_dec x then S (countPV v') else countPV v'
  end.


(* Write the definition of filterV on vectors: *)

Fixpoint filterV {n:nat} (v:vector n): vector (countPV v):=
  match v with
  | Vnil => Vnil
  | Vcons x v' =>
    match (P_dec x) as is_x return vector (
        match is_x
        with
        | right _ => (countPV v')
        | left _ => (S (countPV v'))
        end            
    )
    with
    | right ph => (filterV v')
    | left ph => Vcons x (filterV v')
    end
  end.

(*
ForallV is Forall on vectors:
*)

Print Forall.

Inductive ForallV (P:A-> Prop): forall {n:nat}, vector n -> Prop :=
    Forall_Vnil : ForallV P Vnil
  | Forall_Vcons : forall (x : A) (n:nat) (v : vector n),
                  P x -> ForallV P v -> ForallV P (Vcons x v).

(* 
Prove lemmas cPV1, cPV2 and cPV3:
*)


Lemma cPV1: forall (n:nat)(v:vector n), countPV v = 0 -> 
           ForallV (fun x => ~P x) v.
Proof.
intros n v H.
induction v.
- constructor.
- simpl in H.
  destruct P_dec.
  constructor.
  + exfalso. lia.
  + exfalso. lia.
  + constructor.
    * apply n0.
    * apply IHv. apply H.
Qed.

Lemma cPV2_aux : forall(n:nat) (v:vector n), countPV v <= n.
Proof.
intros n v.
induction v.
- constructor.
- simpl.
  destruct P_dec.
  + lia.
  + assert (countPV v <= n -> countPV v <= S n).
    * lia.
    * apply H. apply IHv.
Qed.

Lemma cPV2: forall (n:nat) (v:vector n), countPV v = n -> ForallV P v.
Proof.
intros n v H.
induction v.
- constructor.
- simpl in H.
  destruct P_dec.
  + assert (countPV v = n) as H0.
    lia.
    constructor.
    * assumption.
    * apply IHv. apply H0.
  + constructor;
    exfalso;
    pose proof (cPV2_aux v);
    lia.
Qed.

Lemma cPV3: forall n (v: vector n), ForallV P (filterV v).
Proof.
intros n v.
induction v.
- constructor.
- simpl.
  destruct P_dec.
  + constructor; assumption.
  + assumption.
Qed.

(*
Prove lemma cPVInversion; use Defined. 
*)

Print sigT.

Definition invtype {n} (v: vector n):=
(match n return vector n -> Type with
| O => fun v => v = Vnil
| S n' => fun v => sigT (fun x => (sig (fun v' => v = Vcons x v')))
end) v.

Definition cPVInversion {n} (v: vector n) : invtype v.
induction v.
- constructor.
- simpl.
  exists a.
  exists v.
  reflexivity.
Defined.

(* Write the definition of toList *)
Fixpoint toList {n} (v:vector n) : list A :=
  match v with
  | Vnil => nil
  | Vcons a v' => cons a (toList v')
  end.

(* 
Prove three lemmas about toList: lenToListEqn, injectiveToList, surjectiveToList. 
lenToList should be transparent (use Defined.)
*) 

Lemma lenToListEqn: forall n (v: vector n), length (toList v) = n.
Proof.
intros n v.
induction v.
- constructor.
- simpl.
  f_equal.
  assumption.
Defined.

Lemma injectiveToList: forall n (v v': vector n), toList v' = toList v -> v' = v.
Proof.
intro n.
induction n;
intros v v' H;
pose proof (cPVInversion v);
pose proof (cPVInversion v').
- congruence.
- simpl in X. simpl in X0.
  destruct X as [Xa Xb]. destruct Xb as [Xb Xc].
  destruct X0 as [Ya Yb]. destruct Yb as [Yb Yc].
  rewrite Yc in H. rewrite Xc in H. simpl in H.
  assert (Ya = Xa). congruence.
  rewrite H0 in H.
  assert (toList Yb = toList Xb).
  congruence.
  assert (Yb = Xb).
  apply IHn.
  assumption.
  rewrite Xc. rewrite Yc. congruence.
Qed.

Print sig.

Lemma surjectiveToList: forall  (l: list A), 
      sig (fun (v: vector (length l)) =>  toList v = l).
Proof.
intro l.
induction l.
- simpl. exists Vnil. reflexivity.
- destruct IHl. exists (Vcons a x). simpl. f_equal. assumption.
Qed.

(* Write the definition of toVector *)
Fixpoint toVector (l:list A) : vector (length l) :=
  match l with
  | nil => Vnil
  | a :: l => Vcons a (toVector l)
  end.

Eval compute in (toVector nil).

(* 
Prove lemmas iso1 and iso2 
*)

Lemma iso1: forall (l:list A), toList (toVector l) = l.
Proof.
intro l.
induction l.
- constructor.
- simpl. f_equal. assumption.
Qed.

Print UIP_refl.

Lemma iso2: forall n (v: vector n), v = match (lenToListEqn v) with
                                            | eq_refl => toVector (toList v)
                                            end.
Proof.
intros n v.
induction v.
- constructor.
- simpl.
  rewrite IHv at 1.
  generalize (lenToListEqn v).
  generalize (lenToListEqn (Vcons a v)).
  intros.
  simpl in H.
  revert H.
  destruct e.
  intro.
  easy.
Qed.


(*
Prove cPVfilterVIdentity
*)

(* Recall that UIP_refl nat is provable in Coq *)

Check (UIP_refl nat). 

Lemma cPVfilterVIdentity: forall (n:nat) (v:vector n) (d: n = countPV v),
filterV v = match d in _= m return vector m with
                            | eq_refl => v
                            end.
Proof.
intros n v d.
induction v; simpl; intros.
- rewrite (UIP_refl nat 0 d). reflexivity.
- simpl in d. destruct P_dec.
  + assert (n = countPV v). lia. rewrite (IHv H).
    destruct H. rewrite (UIP_refl nat (S n) d). reflexivity.
  + exfalso. pose proof (cPV2_aux v). lia.
Qed.

(* 
cPVtc is a type-cast needed to formulate the lemma given below
*)

Lemma cPVtc : forall {n:nat} (v:vector n),  countPV v = countPV (filterV v).
Proof.
intros n v.
induction v.
- constructor.
- simpl. destruct P_dec.
  + simpl. destruct P_dec.
    * f_equal. assumption.
    * easy.
  + assumption.
Qed.

(* 
Use the lemmas proved above to show that filterV is idempotent
Lemma cPV3: forall n (v: vector n), ForallV P (filterV v).
*)
 

Lemma filterV_idem: forall {n:nat} (v:vector n),
      filterV (filterV v) = match cPVtc v in _= m return vector m with
                            | eq_refl => filterV v
                            end.
Proof.
intros.
apply cPVfilterVIdentity.
Qed.

End filterV.

Section filterfilter.

(*------------------------------------------------------------------
Combining filterL and filterV 
--------------------------------------------------------------------
*)


Variable A : Type.
Variable P : A -> Prop.

Variable P_dec : forall x, {P x}+{~P x}.

(* Prove the lemmas about filterV, filterL, toList and toVector *)

Lemma filterVfilterL:  forall n (v:vector A n), 
      toList(filterV P P_dec v) = filterL P P_dec (toList v).
Proof.
intros n v.
induction v.
- constructor.
- simpl. destruct P_dec; simpl; try f_equal; apply IHv.
Qed.

(* 
The following lemma is needed as a type-cast and should be ended with Defined 
*) 

Lemma countPVlength: forall l, countPV P P_dec (toVector l) = length (filterL P P_dec l ).
Proof.
intro l.
induction l.
- constructor.
- simpl. destruct P_dec.
  * simpl. f_equal. apply IHl.
  * apply IHl.
Defined.

Lemma filterLfilterV: forall (l:list A), 
toVector (filterL P P_dec l) = match (countPVlength l) with 
                               | eq_refl => filterV P P_dec (toVector l)
                               end.
Proof.
intros.
induction l.
- reflexivity.
- simpl. destruct P_dec.
  + simpl.
    rewrite IHl.
    generalize (countPVlength l).
    generalize (countPVlength (a :: l)).
    intros.
    simpl in H.
    destruct P_dec.
    * simpl in H. destruct e. easy.
    * congruence.
  + easy.
Qed.
