(* Definitions and lemmas suggested by Rafał Stefański and Daria Walukiewicz-Chrząszcz *)
Require Import String.
Require Import List.
(*
At the end of the file, we prove Kolmogorov's theorem:
For a set of premises gamma, a formula f is classicaly provable
if and only if K(f) is intuitionistically provable from the set
of premises {K(phi) for phi in gamma}, where `K` is Kolmogorov's double negation translation:
Fixpoint k (f : formula) : formula :=
  match f with
      Var x => ~~ (Var x)
    | (p --> q)%form => ~~( (k p) --> (k q))
    | False => 0
  end.
for more information about the double negation translation,
please refer to the nLab entry:
https://ncatlab.org/nlab/show/double+negation+translation
*)

Inductive formula : Type :=
   Var (x : string)
  |Impl (f1 : formula) (f2 : formula)
  |False.

Bind Scope formula_scope with formula.
Delimit Scope formula_scope with form.

Notation "x '-->' y" := (Impl x y)
                        (at level 55, right associativity) : formula_scope.
Notation "0" := False : formula_scope.

Definition notf f := (f --> 0) % form.

Notation "'~' x" := (notf x) : formula_scope.

  (* Kolmogorov's double negation translation *)
Fixpoint k (f : formula) : formula :=
  match f with
      Var x => ~~ (Var x)
    | (p --> q)%form => ~~( (k p) --> (k q))
    | False => 0
  end.


Definition env : Type := list formula.

Print In.

(* Intuitionistic proof *)
Inductive intu_provable : env -> formula -> Prop :=
  II : forall gamma a b,
    intu_provable (a::gamma) b -> intu_provable gamma (a --> b) |
  EI : forall gamma a b,
    intu_provable gamma (a --> b) ->
    intu_provable gamma a ->
    intu_provable gamma b |
  Ax : forall gamma a,
    In a gamma -> intu_provable gamma a |
  EF : forall gamma a,
    intu_provable gamma 0 ->
    intu_provable gamma a.

(* Classical proof *)
Inductive class_provable : env -> formula -> Prop :=
  IIC : forall gamma a b,
    class_provable (a::gamma) b -> class_provable gamma (a --> b) |
  EIC : forall gamma a b,
    class_provable gamma (a --> b) ->
    class_provable gamma a ->
    class_provable gamma b |
  AxC : forall gamma a,
    In a gamma -> class_provable gamma a |
  EFC : forall gamma a,
    class_provable gamma 0 ->
    class_provable gamma a |
  Cheat : forall a gamma,
    class_provable gamma (~~a) ->
    class_provable gamma a.


(* At the beginning of the lemma below, quantifier order change occurs:

Lemma weakening_intu : forall gamma f, intu_provable gamma f  ->
  forall gamma', (forall x, In x gamma -> In x gamma') -> intu_provable gamma' f.
Proof.
intros gamma f H0. 
induction H0.
*)


Lemma weakening_intu : forall gamma gamma' f,
  (forall x, In x gamma -> In x gamma') ->
  intu_provable gamma f ->
  intu_provable gamma' f.
Proof.
  intros.
  generalize dependent gamma'.
  induction H0.
  + intros. apply II. apply IHintu_provable.
    intros. destruct H1.
    - left. assumption.
    - right. apply H. assumption.
  + intros. apply (EI gamma' a).
    - apply IHintu_provable1. assumption.
    - apply IHintu_provable2. assumption.
  + intros. apply Ax. apply H0. assumption.
  + intros. apply EF. apply IHintu_provable.
    assumption.
Qed.

Lemma weakening_class : forall gamma gamma' f,
  (forall x, In x gamma -> In x gamma') ->
  class_provable gamma f ->
  class_provable gamma' f.
Proof.
  intros.
  generalize dependent gamma'.
  induction H0.
  + intros. apply IIC. apply IHclass_provable.
    intros. destruct H1.
    - left. assumption.
    - right. apply H. assumption.
  + intros. apply EIC with a.
    - apply IHclass_provable1. assumption.
    - apply IHclass_provable2. assumption.
  + intros. apply AxC. apply H0. assumption.
  + intros. apply EFC. apply IHclass_provable.
    assumption.
  + intros. apply Cheat. apply IHclass_provable.
    assumption.
Qed.

Definition weaker (gamma : env) (gamma' : env) : Prop :=
  forall x, In x gamma ->
    (exists y, In y gamma' /\ class_provable gamma' (y --> x)).

Lemma append_weaker : forall a gamma gamma',
  weaker gamma gamma' ->
  weaker (a::gamma) (a::gamma').
Proof.
intros.
unfold weaker.
intros.
destruct H0.
- exists a.
  split.
  + apply in_eq.
  + rewrite H0. apply IIC. apply AxC. apply in_eq.
- apply H in H0.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  + apply in_cons. apply H0.
  + apply (weakening_class gamma' (a :: gamma') (x0 --> x)).
    * intros. pose proof in_cons a x1 gamma' H2. apply H3.
    * apply H1. 
Qed.

(* custom *)
Lemma strong_weakening_class : forall gamma gamma' f,
  weaker gamma gamma' ->
  class_provable gamma f ->
  class_provable gamma' f.
Proof.
induction gamma; intros.
- apply (weakening_class nil gamma'); easy.
- pose proof (H a). destruct H1.
  + apply in_eq.
  + destruct H1.
    apply IIC in H0.
    assert (weaker gamma (a :: gamma)). {
    unfold weaker.
    intros.
    exists x0.
    split.
    - apply in_cons. assumption.
    - apply IIC. apply AxC. apply in_eq.
    }
    assert (weaker gamma gamma'). {
    unfold weaker.
    intros.
    apply (H x0).
    apply in_cons. assumption.
    }
    pose proof (IHgamma gamma' (a --> f)%form) H4 H0.
    apply (EIC gamma' a f).
    * assumption.
    * apply (EIC gamma' x a).
      ** assumption.
      ** apply AxC. assumption.
Qed.

(* custom *)
Lemma simple_eic : forall gamma_cons a b,
  class_provable ((a --> b)%form :: a :: gamma_cons) b.
Proof.
intros.
pose proof EIC ((a --> b)%form :: a :: gamma_cons) a b.
apply H.
- apply AxC. apply in_eq.
- apply AxC. apply in_cons. apply in_eq.
Qed.

Lemma in_cons_reorder_args : forall (A : Type) (a : A) (l : list A) (b : A),
  In b l -> In b (a :: l).
Proof.
  intros.
  generalize dependent l.
  generalize dependent b.
  apply in_cons.
Qed.

(* custom; żaden z aksjomatów nie pozwala wprost 
   na wciągnięcie czegoś na lewą stronę
*)
Lemma embedded_intro : forall gamma a b,
  class_provable gamma (a --> b) ->
  class_provable (a :: gamma) b.
Proof.
intros.
pose proof weakening_class gamma (a :: gamma) (a --> b)
  (in_cons_reorder_args formula a gamma) H.
pose proof AxC (a :: gamma) a (in_eq a gamma).
pose proof EIC (a :: gamma) a b H0 H1.
apply H2.
Qed.

(* custom *)
Lemma embedded_apply : forall gamma a b,
  class_provable gamma a ->
  class_provable ((a --> b)%form :: gamma) b.
Proof.
intros.
pose proof weakening_class gamma ((a --> b)%form :: gamma) a
  (in_cons_reorder_args formula (a --> b)%form gamma) H.
pose proof AxC ((a --> b)%form :: gamma)
  (a --> b)%form (in_eq ((a --> b)%form) gamma).
pose proof EIC ((a --> b)%form :: gamma) a b H1 H0.
apply H2.
Qed.

(* custom *)
Lemma composition : forall gamma a b c,
 class_provable gamma (a --> b) ->
 class_provable gamma (b --> c) ->
 class_provable gamma (a --> c).
Proof.
intros.
apply IIC.
pose proof embedded_intro gamma a b H.
pose proof weakening_class gamma (a :: gamma) (b --> c)
  (in_cons_reorder_args formula a gamma) H0.
pose proof EIC (a :: gamma) b c H2 H1.
assumption.
Qed.

Lemma permute : forall gamma a a0 b,
  class_provable (a :: a0 :: gamma) b ->
  class_provable (a0 :: a :: gamma) b.
Proof.
intros.
assert (weaker (a :: a0 :: gamma) (a0 :: a :: gamma)). {
unfold weaker.
intros.
exists x.
split.
- destruct H0.
  + rewrite H0. apply in_cons. apply in_eq.
  + destruct H0.
    * rewrite H0. apply in_eq.
    * apply in_cons. apply in_cons. apply H0.
- apply IIC. apply AxC. apply in_eq.
}
pose proof strong_weakening_class (a :: a0 :: gamma) (a0 :: a :: gamma) b H0 H.
assumption.
Qed.


Lemma after_tail_is_weaker : forall gamma,
  weaker (tail gamma) gamma.
Proof.
unfold weaker.
intros.
exists x.
split.
- destruct gamma.
  + simpl in H. simpl. assumption.
  + simpl in H. apply in_cons. assumption.
- apply IIC. apply AxC. apply in_eq.
Qed.

Lemma is_weaker_if_can_merge : forall gamma a a0,
  class_provable gamma (a --> a0) ->
  weaker (a0 :: a :: gamma) (a :: gamma).
Proof.
intros.
unfold weaker.
intros.
destruct H0.
- rewrite <- H0.
  exists a.
  split.
  + apply in_eq.
  + pose proof after_tail_is_weaker (a :: gamma). simpl in H1.
    pose proof strong_weakening_class gamma (a :: gamma) (a --> a0) H1 H.
    assumption.
- destruct H0.
  + rewrite <- H0.
    exists a.
    split.
    * apply in_eq.
    * apply IIC. apply AxC. apply in_eq.
  + exists x.
    split.
    * apply in_cons. assumption.
    * apply IIC. apply AxC. apply in_eq.
Qed.
  
Lemma after_append_is_stronger : forall gamma a,
  weaker gamma (a :: gamma).
Proof.
unfold weaker.
intros.
exists x.
split.
- apply in_cons.
  assumption.
- apply IIC.
  apply AxC.
  apply in_eq.
Qed.


Lemma help : forall gamma a b,
  class_provable gamma a -> class_provable gamma b -> 
  class_provable gamma (a --> b).
Proof.
intros.
apply IIC.
pose proof (after_append_is_stronger gamma a).
apply (strong_weakening_class gamma).
- assumption.
- assumption.
Qed.


Lemma DNIC : forall gamma a,
  class_provable gamma a -> class_provable gamma (~~a).
Proof.
intros.
apply IIC.
unfold notf.
apply embedded_apply.
assumption.
Qed.


(* IIC, EIC, AxC, EFC, Cheat *)
Lemma a_iff_ka : forall a,
  class_provable nil (a -->(k a)) /\
  class_provable nil ((k a) --> a).
Proof.
intros.
induction a.
- split.
  + unfold k. apply IIC. unfold notf. apply IIC. apply simple_eic.
  + unfold k. apply IIC. apply Cheat. apply AxC. apply in_eq. 
- split.
  + simpl. apply IIC. apply DNIC. apply IIC.
    destruct IHa1. destruct IHa2.
    assert (weaker nil (k a1 :: (a1 --> a2)%form :: nil)). {
      unfold weaker. intros. exists x. split.
      - apply in_cons. apply in_cons. assumption.
      - apply IIC. easy.
    }
    remember (k a1 :: (a1 --> a2)%form :: nil) as env.
        pose proof (
      strong_weakening_class
        nil
        env
        (k a1 --> a1)
        H3
        H0).
    pose proof (
      strong_weakening_class
        nil
        env
        (a2 --> k a2)
        H3
        H1).
    pose proof (EIC env a2 (k a2)).
    apply H6.
    * assumption.
    * pose proof (EIC env a1 a2). apply H7.
      ** apply AxC. rewrite Heqenv. apply in_cons. apply in_eq.
      ** apply (EIC env (k a1) a1). *** assumption. *** rewrite Heqenv. apply AxC. apply in_eq.
  + simpl.
    destruct IHa1. destruct IHa2. apply IIC. apply IIC.
    assert (class_provable (a1 :: (~~k a1 --> k a2)%form :: nil) (k a1 --> k a2)). {
      apply Cheat. apply AxC. apply in_cons. apply in_eq.
    }
    assert (weaker nil (a1 :: (~~k a1 --> k a2)%form ::nil)). {
     unfold weaker. intros. exists x. split. - apply in_cons. apply in_cons. assumption.
      - apply IIC. easy.
    }
    pose proof (strong_weakening_class nil (a1 :: (~~k a1 --> k a2)%form :: nil) (a2 --> k a2) H4 H1).
    pose proof (strong_weakening_class nil (a1 :: (~~k a1 --> k a2)%form :: nil) (a1 --> k a1) H4 H).
        pose proof (strong_weakening_class nil (a1 :: (~~k a1 --> k a2)%form :: nil) (k a1 --> a1) H4 H0).
        pose proof (strong_weakening_class nil (a1 :: (~~k a1 --> k a2)%form :: nil) (k a2 --> a2) H4 H2).
    apply (EIC (a1 :: (~~k a1 --> k a2)%form :: nil) (k a2) a2).
    * assumption.
    * apply (EIC (a1 :: (~~k a1 --> k a2)%form :: nil) (k a1) (k a2)).
    ** assumption.
    ** apply (EIC (a1 :: (~~k a1 --> k a2)%form ::nil) a1 (k a1)).
    *** assumption.
    *** apply AxC. apply in_eq.
- simpl. split; apply IIC; apply AxC; apply in_eq.
Qed.

(* custom *)
Lemma a_iff_ka_strong : forall gamma a,
  class_provable gamma (a --> (k a)) /\
  class_provable gamma ((k a) --> a).
Proof.
induction gamma.
- apply a_iff_ka.
- intro.
  pose proof weakening_class gamma (a::gamma) (a0 --> (k a0))
    (in_cons_reorder_args formula a gamma).
  pose proof weakening_class gamma (a::gamma) ((k a0) --> a0)
    (in_cons_reorder_args formula a gamma).
  split.
  + apply H. apply IHgamma.
  + apply H0. apply IHgamma.
Qed.


Lemma intu_to_class : forall f gamma,
  intu_provable gamma f ->
  class_provable gamma f.
Proof.
intros.
induction H.
- apply IIC. assumption.
- pose proof EIC gamma a b IHintu_provable1 IHintu_provable2. assumption.
- apply AxC. assumption.
- apply EFC. assumption.
Qed.

(* custom *)
Lemma a_iff_ka_strong2 : forall gamma a,
  class_provable gamma a <-> class_provable gamma (k a).
Proof.
split.
- intro.
  pose proof a_iff_ka_strong gamma a.
  destruct H0.
  pose proof EIC gamma a (k a) H0 H.
  assumption.
- intro.
  pose proof a_iff_ka_strong gamma a.
  destruct H0.
  pose proof EIC gamma (k a) a H1 H.
  assumption.
Qed.

Lemma k_intu_to_class : forall f gamma,
  intu_provable (map k gamma) (k f) ->
  class_provable gamma f.
Proof.
intros.
pose proof intu_to_class (k f) (map k gamma) H.
assert (weaker (map k gamma) gamma) . {
  unfold weaker.
  intros.
  pose proof in_map_iff k gamma x.
  destruct H2.
  pose proof H2 H1.
  destruct H4.
  exists x0.
  split.
  + destruct H4. assumption.
  + destruct H4.
    rewrite <- H4.
    apply a_iff_ka_strong.
}
pose proof strong_weakening_class (map k gamma) gamma f H1.
apply H2.
pose proof a_iff_ka_strong (map k gamma) f.
destruct H3.
apply a_iff_ka_strong2.
assumption.
Qed.

Lemma map_k_weaker : forall gamma,
  weaker (map k gamma) gamma.
Proof.
intro.
unfold weaker.
intros.
pose proof in_map_iff k gamma x.
destruct H0.
pose proof H0 H.
destruct H2.
exists x0.
split.
+ destruct H2. assumption.
+ destruct H2.
  rewrite <- H2.
  apply a_iff_ka_strong.
Qed.


Lemma map_k_weaker2 : forall gamma,
  weaker gamma (map k gamma).
Proof.
intros.
induction gamma.
- simpl. easy.
- unfold weaker.
  intros.
  destruct H.
  + rewrite <- H.
    exists (k a).
    split.
    * simpl. left. reflexivity.
    * pose proof a_iff_ka_strong (map k (a :: gamma)) a.
      destruct H0.
      apply H1.
  + exists (k x).
    split.
    * simpl. right. apply in_map. assumption.
    * pose proof a_iff_ka_strong (map k (a :: gamma)) x.
      destruct H0.
      apply H1.
Qed.

Lemma DNI: forall gamma a, intu_provable gamma a -> intu_provable gamma (~~a).
Proof.
intros.
apply II.
unfold notf.
assert (intu_provable ((a --> 0)%form :: gamma) a). {
apply (weakening_intu gamma ((a --> 0)%form :: gamma) a).
- intros. apply in_cons. assumption.
- assumption.
}
apply (EI ((a --> 0)%form :: gamma) a 0).
+ apply Ax. apply in_eq. 
+ assumption.
Qed.

(* źródło: wykład *)
Lemma dne_impl : forall (p : Prop) (q : Prop),
  ((~~(p -> ~q)) -> (p -> ~q)).
Proof.
intro.
intro.
intro.
intro.
intro.
apply H.
intro.
apply H2.
- assumption.
- assumption. 
Qed.

Lemma embedded_intro_intu : forall gamma a b,
  intu_provable gamma (a --> b) ->
  intu_provable (a :: gamma) b.
Proof.
intros.
pose proof (weakening_intu gamma (a :: gamma) (a --> b) (in_cons_reorder_args formula a gamma) H).
pose proof (Ax (a :: gamma) a (in_eq a gamma)).
pose proof (EI (a :: gamma) a b H0 H1).
apply H2.
Qed.

Lemma merge_intu2 : forall gamma a b,
  intu_provable (a :: gamma) b -> intu_provable gamma a -> intu_provable gamma b.
Proof.
intros.
apply II in H.
apply (EI gamma a b) in H.
- assumption.
- assumption.
Qed. 

Lemma merge_intu : forall gamma a b c,
  intu_provable (a :: b :: gamma) c -> intu_provable gamma a -> intu_provable gamma b -> intu_provable gamma c.
Proof.
intros.
apply II in H.
apply II in H.
apply (EI gamma b) in H.
- apply (EI gamma a) in H.
  + assumption.
  + assumption.
- assumption.
Qed.

Lemma embedded_apply_intu : forall gamma a b,
  In (a --> b)%form gamma -> intu_provable gamma a -> intu_provable gamma b.
Proof.
intros.
pose proof (Ax gamma (a --> b)%form H).
apply (EI gamma a).
- assumption.
- assumption.
Qed.

Lemma kolmogorov_modus_ponens : forall gamma p q,
  intu_provable gamma (~~(p --> ~q)) ->
  intu_provable gamma p ->
  intu_provable gamma (~q).
Proof.
intros *.
(* intros *)
apply merge_intu.
apply II.
(* apply (~ p --> q) --> 0 *)
assert (In (~~ p --> (~q))%form (q :: (~~ p --> (~q))%form :: p :: gamma)). { apply in_cons. apply in_eq. }
pose proof (embedded_apply_intu (q :: (~~ p --> (~q))%form :: p :: gamma) (~ p --> (~q))%form 0) H.
apply H0.
(* intro *)
apply II.
(* apply p --> ~q *)
assert (intu_provable ((p --> (~ q))%form :: q :: (~ ~ p --> (~ q))%form :: p :: gamma) (~q)). {
  assert(In (p --> (~ q))%form ((p --> (~ q))%form :: q :: (~ ~ p --> (~ q))%form :: p :: gamma)). { apply in_eq. }
  pose proof (embedded_apply_intu ((p --> (~ q))%form :: q :: (~ ~ p --> (~ q))%form :: p :: gamma) p (~q)) H1. 
  apply H2.
  apply Ax.
  apply in_cons. apply in_cons. apply in_cons. apply in_eq.
}
apply (EI ((p --> (~ q))%form :: q :: (~ ~ p --> (~ q))%form :: p :: gamma) q).
- assumption.
- apply Ax. apply in_cons. apply in_eq.
Qed.

Lemma triple_negation_elimination: forall p, ~~~p -> ~p.
Proof.
unfold not.
intros.
apply H.
intros.
apply H1.
apply H0.
Qed.


Lemma embedded_tne: forall gamma p, intu_provable gamma (~~~p)%form -> intu_provable gamma (~p)%form.
Proof.
intros *.
apply merge_intu2.
apply II.
apply (EI (p :: (~~~p)%form :: gamma) (~~p)%form).
- apply Ax. apply in_cons. apply in_eq.
- apply II.
  apply (EI ((~p) :: p :: (~~~p) :: gamma)%form p).
  + apply Ax. apply in_eq.
  + apply Ax. apply in_cons; apply in_eq.
Qed.


Lemma class_to_k_intu : forall f gamma,
  class_provable gamma f ->
  intu_provable (map k gamma) (k f).
Proof.
intros.
induction H.
- simpl in IHclass_provable. simpl. apply II in IHclass_provable. apply DNI. assumption.
- simpl in IHclass_provable1.
  induction b; simpl.
  + simpl in IHclass_provable1.
    pose proof (kolmogorov_modus_ponens (map k gamma) (k a) (~ Var x)%form).
    apply (H1 IHclass_provable1 IHclass_provable2).
  + pose proof (kolmogorov_modus_ponens (map k gamma) (k a) (~ k b1 --> k b2)%form).
    apply (H1 IHclass_provable1 IHclass_provable2).
  + assert (intu_provable (map k gamma) (~ k a)). {
      apply II.
      assert (intu_provable (k a :: map k gamma) (~~~ k a)). {
        apply (weakening_intu (map k gamma) (k a :: map k gamma)).
        - intro. apply in_cons.
        - assumption.
      }
      apply (EI (k a :: map k gamma) (~~ k a)).
      * assumption.
      * apply II.
        apply (EI ((~ k a)%form :: k a :: map k gamma) (k a) 0).
        ** apply Ax. apply in_eq.
        ** apply Ax. apply in_cons. apply in_eq.
    }
    apply (EI (map k gamma) (k a)).
    * assumption.
    * assumption.
- apply Ax. apply in_map. assumption.
- apply EF. assumption.
- destruct a.
  + simpl in IHclass_provable.
    apply (embedded_tne (map k gamma) (~~~~~Var x)) in IHclass_provable.
    apply (embedded_tne (map k gamma) (~~~Var x)) in IHclass_provable.
    apply (embedded_tne (map k gamma) (~Var x)) in IHclass_provable.
    simpl. assumption.
  + simpl in IHclass_provable.
    apply (embedded_tne (map k gamma) (~~~~~k a1 --> k a2)%form) in IHclass_provable.
    apply (embedded_tne (map k gamma) (~~~k a1 --> k a2)%form) in IHclass_provable.
    apply (embedded_tne (map k gamma) (~k a1 --> k a2)%form) in IHclass_provable.
    simpl; assumption.
  + simpl in IHclass_provable. 
    apply (embedded_tne (map k gamma) (~~~0)%form) in IHclass_provable.
    apply (embedded_tne (map k gamma) (~0)) in IHclass_provable.
    apply (EI (map k gamma) (0 --> 0)%form 0) in IHclass_provable.
    * assumption.
    * apply II. apply Ax. apply in_eq.
Qed.

Theorem Kolmogorov : forall f gamma,
  class_provable gamma f <-> intu_provable (map k gamma) (k f).
Proof.
  split.
  apply class_to_k_intu.
  apply k_intu_to_class.
Qed.
