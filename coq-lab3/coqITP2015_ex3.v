Require Import Arith.
Require Import Bool.
Require Import Lia.

(**************)
(* Exercise 1 *)
(**************)

(* We first want to prove that our definition of add satisfies commutativity. *)
Print plus.
Print Init.Nat.add.


Fixpoint add n m := 
  match n with 0 => m | S p => add p (S m) end.

Lemma addnS : forall n m, add n (S m) = S (add n m).
  induction n.
  - intros m; simpl.
    auto.
  - intros m; simpl.
    apply IHn.
Qed.

(* Q1. Prove the following two theorems: beware that you will probably need
  addnS. *)

(* Already done during the lecture ? *)
Lemma addn0 : forall n, add n 0 = n.
induction n.
- simpl. reflexivity.
- rewrite <- IHn at 2. rewrite <- addnS at 1. simpl. reflexivity. 
Qed.

Lemma add_comm : forall n m, add n m = add m n.
induction n, m.
- reflexivity.
- rewrite addn0. simpl. reflexivity.
- rewrite addn0. simpl. reflexivity.
- rewrite addnS. rewrite addnS. f_equal. simpl.
  rewrite addnS. rewrite addnS. f_equal. apply IHn.
Qed.

(* Q2. Now state and prove the associativity of this function. *)
Lemma add_assoc : forall n m o, add n (add m o) = add (add n m) o.
intros.
induction n, m.
- reflexivity.
- reflexivity.
- simpl. rewrite addnS. rewrite addnS. simpl. rewrite addnS. f_equal. rewrite addn0.
  reflexivity.
- simpl in IHn. simpl. repeat rewrite addnS. simpl. repeat rewrite addnS. f_equal.
  repeat rewrite addnS in IHn. simpl in IHn. repeat rewrite addnS in IHn. apply IHn.
Qed.

(* Q3. Now state and prove a theorem that expresses that the add function
  returns the same result as the addition available in the loaded libraries
  (given by function plus) *)
Lemma add_correct : forall n m, add n m = n + m.
induction n.
- reflexivity.
- simpl. intro m. rewrite addnS. f_equal. apply IHn.
Qed.

(*********************)
(* Exercise 2: lists *)
(*********************)
Require Import List  Bool_nat.

(* From lecture 2 *)
Class Eq (A : Type) := cmp : A -> A -> bool.

Infix "==" := cmp (at level 70, no associativity).

Instance bool_Eq : Eq nat := beq_nat.
(* beq_nat comes from the Coq library. *)

Fixpoint multiplicity (n : nat)(l : list nat) : nat  := 
  match l with 
    nil => 0%nat 
  | a :: l' => 
    if n == a then S (multiplicity n l') 
    else multiplicity n l' 
  end. 


Definition is_perm (l l'  : list nat)  := 
  forall n, multiplicity n l = multiplicity n l'.

(* Q4. Show the following theorem :  *)

Lemma multiplicity_app  (x : nat) (l1 l2 : list nat) : 
  multiplicity x (l1 ++ l2) = multiplicity x l1 + multiplicity x l2.
induction l1.
- reflexivity.
- case_eq (x == a).
  + intros. simpl. rewrite H. simpl. f_equal. apply IHl1.
  + intros. simpl. rewrite H. simpl. f_equal. apply IHl1.
Qed.

(* Note : for Q5 and Q6, you will probably have an opportunity
  to use the lia tactic *)

(* Q5. State and prove a theorem that expresses that element counts are
  preserved by reverse. *)
Print rev.
Lemma multiplicity_rev (x: nat) (l1 : list nat) :
  multiplicity x l1 = multiplicity x (rev l1).
induction l1.
- reflexivity.
- simpl. case_eq (x == a).
  + intro. rewrite multiplicity_app. simpl. rewrite H. lia.
  + intro. rewrite multiplicity_app. simpl. rewrite H. lia.
Qed.

(* Q6. Show the following theorem. *)

Lemma is_perm_transpose x y l1 l2 l3 : 
  is_perm (l1 ++ x::l2 ++ y::l3) (l1 ++ y :: l2 ++ x :: l3).
unfold is_perm.
intro.
repeat rewrite (multiplicity_app n).
f_equal.
Admitted.

(* Q7 :  Complete the following lemma using only a reasonning
  on the function rev_app  *)
(* Excerpt from Lecture3.v - Begin *)
Fixpoint rev_app (A : Type)(l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | a :: tl => rev_app A tl (a :: l2)
  end.

Check app_assoc_reverse.
Check app_assoc.


Lemma rev_app_nil : forall A (l1 : list A), 
rev_app A l1 nil = rev l1.
Proof.
intros A l1.
assert (Htmp: forall l2, rev_app A l1 l2 = rev l1 ++ l2).
+ induction l1; intros l2.
  * simpl. auto.
  * simpl.
    rewrite app_assoc_reverse.
    simpl.
    apply IHl1.
+ rewrite Htmp. 
  rewrite app_nil_r.
  auto.
Qed.
(* Excerpt from Lecture3.v - End *)


(* Tu powinien być jeden pomocniczy lemat, 
   żeby móc dokończyć poniższy dowód *)

Lemma rev_rev_id : forall A (l:list A), rev (rev l) = l.
Proof.
  intros.
  rewrite <- rev_app_nil.
  rewrite <- rev_app_nil.
  
Admitted.

(* Q8 : What does this function do? *)
Fixpoint mask (A : Type)(m : list bool)(s : list A) {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask A m' s' else mask A m' s'
  | _, _ => nil
  end.

Arguments mask [A] _ _.

Lemma length0_empty : forall A (l: list A), length l = 0 <-> l = nil.
Proof.
destruct l; easy.
Qed.

(* Q9 Prove that : *)
Lemma mask_cat : forall A m1 (s1 : list A),
    length m1 = length s1 ->
  forall m2 s2, mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
intros.
induction m1.
- simpl. simpl in H. symmetry in H. apply length0_empty in H. rewrite H. easy.
- simpl in H. admit.
Admitted.

(**************)
(* Exercise 3 *)
(**************)

(* Define an inductive type formula : Type that represents the *)
(*abstract language of propositional logic without variables: 
L = L /\ L | L \/ L | ~L | L_true | L_false
*)


(* Define a function formula_holds of type (formula -> Prop computing the *)
(* Coq formula corresponding to an element of type formula *)

(* Define  a function isT_formula of type (formula -> bool) computing *)
(* the intended truth value of (f : formula) *)


(* prove that is (idT_formula f) evaluates to true, then its *)
(*corresponding Coq formula holds ie.:

Require Import Bool.
Lemma isT_formula_correct : forall f : formula, 
   isT_formula f = true <-> formula_holds f.
*)

(**************)
(* Exercise 4 *)
(**************)

(* We use the inductive type defined in the lecture: *)

Inductive natBinTree : Set :=
| Leaf : natBinTree
| Node : nat -> natBinTree -> natBinTree -> natBinTree.

(* Define a function which sums all the values present in the tree.

Define a function is_zero_present : natBinTree -> bool, which tests whether
the value 0 is present or not in the tree.
*)

Print "||".

Locate "||".

Check beq_nat.

(*
Prove several simple statements about the fonctions tree_size
and tree_height seen in the lecture/Define size and height functions.

Define a function called mirror that computes the mirror image of a tree.

Prove that a tree and its mirror image have the same height.

Prove that mirror is involutive (ie the mirror image of the mirror image
of the tree is this tree).

It is possible to navigate in a binary tree, given a tree t and
a path like "from the root, go to the left subtree, then 
 go to the right subtree, then go to the left subtree, etc. "

Such a path can be easily represented by a list of directions. *)

Inductive direction : Set := L (* go left *) | R (* go right *).


(* Define in Coq a function get_label that takes a tree and some path,
and returns the label at which one arrives following the path
(if any) *)

Fixpoint get_label (path : list direction)(t:natBinTree): option nat:= None.
(* TO DO *)

(* Consider the following function :
*)

Fixpoint zero_present (t: natBinTree) : bool :=
match t with Leaf => false
           | Node n t1 t2 =>  beq_nat n 0 ||
                              zero_present t1 ||
                              zero_present t2
end.
(* 
Prove that whenever zero_present t = true, then there exists 
some path p such that get_label p t = Some 0

*)

Check orb_prop.
Check beq_nat_true.



(**************)
(* Exercise 5 *)
(**************)
(* Define the function 
split : forall A B : Set, list A * B -> (list A) * (list B)

which transforms a list of pairs into a pair of lists
and the function
combine : forall A B : Set, list A * list B -> list (A * B)
which transforms a pair of lists into a list of pairs.

Write and prove two theorems relating the two functions.
*)

Fixpoint split : forall A B : Set, list A * B -> (list A) * (list B) :=
match A with


combine : forall A B : Set, list A * list B -> list (A * B)