Lemma ExampleCHI: forall A B C: Prop, (A -> B -> C) -> (A -> B) -> (A -> C).
Proof.
(*intros.*)
intros A B C X Y Z.

apply X.

assumption.

apply Y.
assumption.
Qed.

Print ExampleCHI.

Definition xampleCHI := 
fun (A B C : Prop) (X : A -> B -> C) (Y : A -> B) (Z : A) => X Z (Y Z).

(* In natural deduction

G, A |- B
-------------------- (-> intro) 
G |- A -> B


G |- A -> B      G |- A
-------------------------(-> elim) (application rule)
G |- B

*)

(* In simply-typed lambda calculus

G, x:A |- M: B
-------------------------- (abstraction) 
G |- fun x:A => M : A -> B


G |- M: A -> B      G |- N: A
-------------------------------(application)
G |- M N : B

*)


Section Minimal_propositional_logic.
 Variables P Q R S : Prop.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
 intros H0 H1 H2 H3.
 apply H2.
 * apply H0.
   assumption.
 *  apply H1; assumption.
 Qed.

 Print diamond.

End Minimal_propositional_logic.

Print diamond.


Section Minimal_first_order_logic.
 Variables (A : Set)
   (P Q : A -> Prop)
   (R : A -> A -> Prop).

 Theorem all_imp_dist :
  (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
 Proof.
 intros H1 H2.
 intro. 
 apply (H1 a).
 apply H2.
 Qed.

 Print all_imp_dist.

 Theorem all_delta : (forall a b:A, R a b) -> forall a:A, R a a.
 Proof.
 intros.
 apply H.
 Qed.

End Minimal_first_order_logic.

Check all_imp_dist.

Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
tauto.
(* intros P Q H p.
 apply H. 
 intro H0.
 apply H0.
assumption. *)
Qed.

Print P3Q.
