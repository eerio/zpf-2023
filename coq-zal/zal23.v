Set Implicit Arguments.
Require Import  List.
Require Import Eqdep.
Require Import Eqdep_dec.
Require Import Lia.


(* Coq assignment - ZPF 2023 - due date 16.05.2023

Fill the definitions and prove the lemmas given below (replace 
Admitted with Qed or Defined)

It is not allowed to: 
1. change/erase given definitions and lemma statements,
   section header/footer, variable declaration, etc.,
2. introduce your own axioms, parameters, variables, hypotheses etc.,   
3. import other modules,
4. define Ltac tactics.

It is allowed to:
1. introduce your own definitions and auxiliary lemmas,
2. change the order of the lemmas to prove,
3. add comments. 

Submit your solution via email before 23:59 on 16.05.2023. 
You should submit one file named Nazwisko.v containing your proofs.

The author of the assignment and the grader is Daria Walukiewicz-Chrząszcz.

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
intros.
induction l.
- simpl.
  reflexivity.
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
intros.
induction l.
- constructor 1. 
- constructor 2.
  + simpl in H.
    destruct P_dec in H.
    * congruence.
    * assumption.
  + apply IHl.
    simpl in H.
    destruct P_dec in H.
    * congruence.
    * assumption.
Qed.

Lemma cPL2_aux: forall (l:list A), countPL l <= length l.
Proof.
intros.
induction l.
- constructor.
- simpl.
  destruct P_dec; lia.
Qed.

Lemma cPL2: forall (l:list A), countPL l = length l -> Forall P l.
Proof.
intros.
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
intros.
induction l.
- constructor.
- simpl.
  destruct P_dec.
  + constructor.
    * assumption.
    * assumption.
  + assumption. 
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
intros.
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
intros.
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
intros.
induction v.
- constructor.
- simpl in H.
  destruct P_dec.
  + assert (countPV v = n).
    lia.
    constructor.
    * assumption.
    * apply IHv. apply H0.
  + constructor.
    * exfalso.
      pose proof (cPV2_aux v).
      lia.
    * exfalso.
      pose proof (cPV2_aux v).
      lia.
Qed.

Lemma cPV3: forall n (v: vector n), ForallV P (filterV v).
Proof.
intros.
induction v.
- constructor.
- simpl.
  destruct P_dec.
  + constructor.
    * assumption.
    * assumption.
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
Qed.

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
intros.
induction v.
- constructor.
- simpl.
  f_equal.
  assumption.
Defined.

Lemma injectiveToList: forall n (v v': vector n), toList v' = toList v -> v' = v.
Proof.
intros n.
induction n.
- intros.
  pose proof (cPVInversion v).  
  pose proof (cPVInversion v'). congruence.
- intros.
  pose proof (cPVInversion v). pose proof (cPVInversion v').
  simpl in X. simpl in X0.
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
intros.
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
intros.
induction l.
- constructor.
- simpl. f_equal. assumption.
Qed.

Lemma iso2: forall n (v: vector n), v = match (lenToListEqn v) with
                                            | eq_refl => toVector (toList v)
                                            end.
Proof.
intros.
induction v.
- constructor.
- simpl.
  assert (forall (v': vector n), v=v' -> Vcons a v = Vcons a v').
  intros.
  congruence.
  simpl in IHv.
Admitted.


(*
Prove cPVfilterVIdentity
*)

(* Recall that UIP_refl nat is provable in Coq *)

Check (UIP_refl nat).

(*
Fixpoint vappend {n m : nat} (v1 : vector n) (v2 : vector m) {struct v1}
  : vector (n + m) := 
    match v1 (*in vector l' return vector (l' + m)*) with
    | Vnil => v2
    | Vcons x xs => Vcons x (vappend xs v2)
    end.
Theorem vappend_assoc_UIP
  : forall a b c (va : vector a) (vb : vector b) (vc : vector c),
      vappend (vappend va vb) vc (*vector ((a+b)+c) *)
  = match Plus.plus_assoc a b c in _ = X return vector X with
   | eq_refl => vappend va (vappend vb vc) 
                 (*vector (a + (b+c))*)
        end.
  Proof.
    induction va.
    - intros.
      simpl.
      (*generalize (vappend vb vc).*) 
      generalize (PeanoNat.Nat.add_assoc 0 b c).
      intro.
      simpl in e.
      rewrite (UIP_refl nat (b+c) e).
      reflexivity.
    - simpl. intros. rewrite IHva; clear IHva.
      (*generalize (vappend va (vappend vb vc)).
      intro.*)
      generalize (PeanoNat.Nat.add_assoc n b c).
      generalize (PeanoNat.Nat.add_assoc (S n) b c).
      intros.
      simpl in e.
      revert e0 e.
      generalize (n + b + c).
      intros.
      destruct e0.
      rewrite (UIP_refl nat (S (n + (b + c))) e).
      reflexivity.
  Qed.*)

Lemma cPVfilterVIdentity: forall (n:nat) (v:vector n) (d: n = countPV v),
filterV v = match d in _= m return vector m with
                            | eq_refl => v
                            end.
Proof.
induction v.
- simpl. intros. rewrite (UIP_refl nat 0 d). reflexivity.
- simpl. intros. destruct P_dec.
  + assert (n = countPV v). lia. 
Admitted.

(* 
cPVtc is a type-cast needed to formulate the lemma given below
*)

Lemma cPVtc : forall {n:nat} (v:vector n),  countPV v = countPV (filterV v).
Proof.
intros.
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
induction v.
- simpl. rewrite (UIP_refl _ _ (cPVtc Vnil)). reflexivity.
Admitted.

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
intros.
induction v.
- constructor.
- simpl. destruct P_dec.
  * simpl. f_equal. apply IHv.
  * simpl. apply IHv.
Qed.

(* 
The following lemma is needed as a type-cast and should be ended with Defined 
*) 

Lemma countPVlength: forall l, countPV P P_dec (toVector l) = length (filterL P P_dec l ).
Proof.
intros.
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
  * simpl. rewrite (UIP_refl _ _ (countPVlength l)).

assert (length (filterL P P_dec l) = countPV P P_dec (toVector l)).
induction l.
+ constructor.
+ simpl. destruct P_dec. 
++ simpl. f_equal. apply IHl0. rewrite (UIP_refl _ _ (countPVlength l)).
   


Admitted.




