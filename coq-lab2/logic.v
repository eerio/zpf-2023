(* First, let us look at some examples : *)

Section s1.

Variables P Q: Prop.


Lemma P3Q : (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros H p.
 apply H. 
 intro H0. 
 apply H0. 
 assumption. 
Qed.

Check P3Q.
Print P3Q.

End s1.

Lemma forallP3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros P Q H p; apply H. 
 intro H0;apply H0;assumption. 
Qed.

Check forallP3Q.
Check P3Q.

Lemma triple_neg : forall P:Prop, ~~~P -> ~P.
Proof.
 intros.
 (* apply H.  does not work .... First one has to unfold not *) 
 unfold not.
 unfold not in H.
 apply P3Q. 
 assumption. 
Qed.


Lemma all_perm :
 forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> 
   forall x y:A, P y x.
Proof.
intros.
apply H.
Qed.

Lemma resolution :
 forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.
intros.
apply H.
- apply H0.
  apply H1.
- apply H2.
Qed.

Ltac inv H := inversion H; clear H; try subst.

Lemma not_ex_forall_not : forall (A: Type) (P: A -> Prop),
                      ~(exists x, P x) <-> forall x, ~ P x.
Proof.
intros.
split.
- intros.
  unfold not.
  intros.
  apply H.
  now exists x.
- intros.
  unfold not.
  intro.
  inversion H0.
  destruct (H x).
  apply H1.
Qed.


Lemma ex_not_forall_not : forall (A: Type) (P: A -> Prop),
                       (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
intros.
unfold not.
intros.
inversion H.
destruct (H0 x).
apply H1.
Qed.


Lemma diff_sym : forall (A:Type) (a b : A), a <> b -> b <> a.
Proof.
unfold not.
intros.
apply H.
rewrite H0.
reflexivity.
Qed.



Lemma fun_diff :  forall (A B:Type) (f : A -> B) (a b : A), 
                       f a <> f b -> a <> b.
Proof.
intros.
intros contra.
destruct H.
rewrite contra.
reflexivity.
Qed.
