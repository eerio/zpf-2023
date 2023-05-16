Require Import Arith.
Require Import List.
Require Import Lia.
Require Extraction.

Print nat.

Check nat_ind.

Definition plus2 n := n+2.

Check plus2.

Fixpoint factorial n := 
  match n with
    0 => 1
  | S m => n*factorial m
end.

Eval compute in factorial 3.

Print list.

Check nil.

Check @nil nat.

Check @nil.

Check @cons.

Check cons 3 nil.

Check @cons nat 3 nil.

Check list_ind.


Fixpoint map (A B: Type)(f: A-> B) l := 
  match l with
    nil => nil
  | x::xs => (f x) ::  map A B f xs
end.

Check map.

Fixpoint mapi {A B: Type}(f: A-> B) l := 
  match l with
    nil => nil
  | x::xs => (f x) ::  mapi f xs
end.

Check mapi.
Check @mapi.


Eval compute in mapi (fun x:nat => x+1) 
(1::24::nil).


(* Types are first-class values *)

Fixpoint AddernatType (n:nat):Type := 
match n with 
  0 => nat
| (S k) => nat -> AddernatType k 
end.

Check AddernatType.


Fixpoint addernat (numargs : nat) (acc: nat): 
                          AddernatType numargs :=
match numargs with 
  0 => acc
| (S k) => fun next => addernat k (next + acc)
end.


Eval compute in (addernat 2 10 2 4).

Eval compute in (addernat 3 0 1 2 3) : nat.

(* Propositions and proofs are first-class values *)

Fixpoint len {A: Type} (l: list A) :=
  match l with
    nil => 0
  | x::xs => 1 + len xs
end.

Check len.


Lemma lenEqZero: forall A (l:list A), 
                    len l = 0 -> l = nil.
Proof.
intros A l h.
destruct l. (* rozumowanie przez przypadki po budowie l *)
* trivial.
* simpl in h.
  congruence.
Qed.

Check lenEqZero.
Check (forall (A : Type) (l : list A), len l = 0 -> l = nil).
Print lenEqZero.

Check (@len nat nil) = 0.

(*
Print le.
Print "<=".
Print "<".
Print ">".

Lemma lenGeZero: forall A (l:list A), 0 <= len l. 
Proof.
intros.
induction l.
- simpl. trivial.
- simpl. constructor. trivial.
Qed.

Check lenGeZero.
Print lenGeZero. 

*)

(* forall A (l:list A), 0 <= length l is a dependent type...*)



Inductive vector {T:Type} : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall n, T -> vector n -> vector (S n).

Check Vcons.


(* Przykład rodziny indukcyjnej o parametrach A i R, gdzie A implicit 

Inductive Acc {A:Type} (R:A->A->Prop) | (x:A) : Prop
  := Acc_in : (forall y, R y x -> Acc y) -> Acc x.

Check @Acc.
Check @Acc_in.
Check Acc_in.

*)

Definition vhead {T:Type}{n:nat}(v:vector (S n)):T :=
match v with
  Vcons n h t => h
end. 

Print vhead.

Check vhead.

Extraction vector.
Extraction vhead.


Lemma Rew (A:Type) (f:A -> A) (g: A -> A -> A) (a:A): 
a = (f a) -> g a = g (f a).
Proof.
intros.
(*rewrite <- H. *)
rewrite H at 1.
reflexivity.
Qed.


(* congruence - decision procedure for ground equlities 
                with uninterpreted symbols *)

Lemma Cong (A:Type) (f:A -> A) (g: A -> A -> A) a b: 
a=(f a) -> (g b (f a))=(f (f a)) -> (g a b = f (g b a)) -> g a b = a.
Proof. 
intros.
congruence.
Qed.


(* lia - linear integer arithmetic *)

Lemma Lia (n m k: nat): n = 2*m - 1 -> k > n -> k > m.
Proof.
intros.
lia.
Qed.