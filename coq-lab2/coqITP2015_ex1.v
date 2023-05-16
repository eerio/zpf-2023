(***********************************************************************)
(** An exercises file to be launch with coqide coqITP2015-ex1.v            *)
(** Revised version, 2015/8/29                                         *)
(***********************************************************************)

(** * Stating and proving simple propositions *)

(* Prove the following *)

Lemma composition : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
intros.
apply H0.
apply H.
apply H1.
Qed.

Lemma tautology : forall (A:Type) (P:A -> Prop) (a:A), P a ->  P a.
Proof.
intros.
apply H.
Qed.


(** * Looking at some examples of inductive definitions and 
      definitions defined in the automatically loaded prelude of Coq *)

(** * Some basic inductive propositions *)

(* Let us look (again) at how is the [True] proposition (inductively) defined *)
(* Observe that [True] is an inductive definition with one constructor *)
(* with no argument. Hence, it can always be proved (being inhabited). *)
Print True.

(* Let us look at how is the [False] proposition (inductively) defined *)
(* Observe that [False] is an inductive definition with no constructor at all *)
(* Hence, it can never be proved (being inhabited) *)
Print False.

(* Let us look at how is the conjunction of propositions is inductively defined *)
(* Observe that [and A B] is bound to a notation, "A /\ B" *)
(* Observe that [and A B] has a single constructor expecting two arguments: a proof of A and a proof of B *)
(* Observe that [and A B] comes with "implicit" arguments *)
Print and.
Print conj.
 
(* Since [and] is bound to the notation "\/", we can as well say *)
Print "/\".

(* Let us look at how is the disjunction of propositions is inductively defined *)
(* Observe that [or A B] is bound to a notation, "A \/ B" *)
(* Observe that [or A B] has two constructors expecting each one argument, *)
(* either a proof of A or a proof of B *)
(* Observe that [and] comes with "implicit" arguments *)
Print or.
Print or_introl.

Check or_introl.
Check (or_introl) (fun P:Prop => fun p:P => p).
Check (or_introl) (1=3) (fun P:Prop => fun p:P => p).


(* Let us look as how the negation is defined in terms of [False] *)
Print not.

(* It happens that "not A" is bound to a notation "~ A" as witnessed by the
following *)
Print "~".

(* Let us look as how iff is defined in terms of [and] and [->] *)
Print iff.

(* It happens that "iff A B" is bound to a notation "A <-> B" as witnessed by the
following *)
Print "<->".



(* Sections allow to introduce a local assumption which will later be discharged *)

Section Classical_reasoning.

(* We assert the classical principle of double negation elimination *)

Variable DNE : forall A:Prop, ~~A -> A.

Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
intros p.
apply DNE.
unfold not.
intros.
apply H.
pose proof (DNE p) as B.
unfold not in B.
info_auto.
Qed.

Ltac inv H := inversion H; clear H; try subst.

Lemma not_ex_all_not :
 forall (U: Type) (P:U -> Prop), ~ (exists n : U, P n) -> (forall n:U, ~ P n).
Proof.
intros.
unfold not in H.
unfold not.
intro.
apply H.
exists n.
apply H0.
Qed.

Lemma drinker_paradox :
forall P:nat -> Prop, exists x:nat, forall y:nat, P x -> P y.
Proof.
intros.
apply DNE. intro H. apply H.
exists 0.
intros.
apply DNE. intro H'. apply H'.
exfalso.
apply H.
exists y.
intros y' HPy.
exfalso.
apply H', HPy.
Qed.


(* This closes the section, discharging over DNE *)

End Classical_reasoning.

(* Check the statement of drinker_paradox out of the section *)
Check drinker_paradox.
