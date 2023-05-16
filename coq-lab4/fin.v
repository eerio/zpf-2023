(* dla typu liczb naturalnych *)

Lemma nat_dec: forall (x y:nat), {x=y}+{~ x=y}.
Proof.
(*decide equality.*)
induction x; destruct y.
 - left; reflexivity.
 - right; congruence.
 - right; congruence.
 - destruct (IHx y).
   * left. congruence.
   * right. congruence.
Qed.

Print or.
Print sumbool.
Print sumor.
Print sig.

Lemma nat_inv: forall (x:nat), (sig (fun y => x = S y)) + {x = 0}.
Proof.
destruct  x.
- right.
  reflexivity.
- left.
  exists x.
  reflexivity.
Qed.


Lemma nat_dec_inv: forall (x y:nat), {x=y}+{~ x=y}.
Proof.
induction x; intro; destruct (nat_inv y). 
 - destruct s; right; congruence.
 - left; congruence.
 - destruct s. destruct (IHx x0).
   * left; congruence.
   * right; congruence.
 - right. congruence.
Qed.

(* Fin *)


Require Import Fin.

Print t.

Check (FS (FS F1)): t 3.
Check (FS F1) : t 3.
Check F1: t 3.
Check @F1 2 : t 3.


(* poprzednik dla t (S n) to liczba w option (t n) *)

Print option.
Check (option nat).
Check (option (t O)).


Definition pred {n} (a: t n) : option (t (pred n)) :=
match a with
| F1 =>  None
| FS f => Some f
end.

(*
Check Empty_set.

Definition rettype n : Type := match n with O => Empty_set | S k => option (t k) end.

Definition predt {n} (a: t n) : rettype n :=
match a in (t k) return (rettype k) with
| F1 =>  None
| FS f => Some f
end.

Print predt. 


Definition pred {n} (a: t (S n)) : option (t n) := predt a.  
*)

Eval compute in (pred ((FS (FS F1)): t 3)).
Eval compute in (pred ((FS (FS F1)): t 5)).


Lemma disc: forall n (a: t n),  FS a <> F1.
Proof.
intros.
induction n.
- congruence.
- congruence.
Qed.

Check f_equal.

Lemma inj: forall n (a b: t n),  FS a = FS b -> a = b.
Proof.
intros.
pose proof (f_equal pred H).

Admitted.

(* różnica między inv i invP *)

Fail Definition invtypeP n (a: t n) := 
match n return Prop with
| O => False
| S k => (ex (fun a' =>  a = FS a')) \/ (a = F1)  
end.



Definition invtypeP n (a: t n) := 
(match n return (t n) -> Prop with
| O => fun a => False
| S k => fun a => (ex (fun a' =>  a = FS a')) \/ (a = F1)  
end) a.

(* Definicja w trybie dowodowym: ciąg taktyk zakończony Defined *)
Definition invP {n} (a: t n) : invtypeP n a.
destruct a.
simpl.
+ constructor 2; reflexivity.
+ constructor 1.
  exists a.
  reflexivity.
Defined.

Print Empty_set.

Definition invtype n (a: t n) := 
(match n return (t n) -> Set with
| O => fun a => Empty_set
| S k => fun a => (sig (fun a' =>  a = FS a')) + {a = F1}  
end) a.

Lemma empty: t O -> False.
Proof.
intros.
pose proof (invP H).
unfold invtypeP in H0.
apply H0.
Qed.

Definition inv {n} (a: t n) : invtype n a.
destruct a.
simpl.
+ constructor 2; reflexivity.
+ constructor 1.
  exists a.
  reflexivity.
Defined.

Print inv.

Lemma t_dec: forall n (a b : t n), {b = a} + {b <> a}.
induction a.
intros; pose proof (inv b); unfold invtype in H; destruct H.

destruct s. right. rewrite e.

(* embedding to numbers *) 

(* Napisz definicję N zanurzenia (t n) w liczby naturalne 
Fixpoint N {n} (a: t n) : nat :=
*)

Require Import Lia.

Lemma less : forall n (a: t n), N a < n.
Proof.
Admitted.

Lemma injN: forall n (a b: t n), N b = N a -> b = a.
Proof.
Admitted.

Fixpoint B (m :nat){n:nat} : t (S n):= 
match m, n return t (S n) with
| O, k => F1 
| S _, O => F1
| S m', S n' => FS (B m' )
end. 

Lemma NB: forall k n, k <= n -> N (@B k n) = k.
Proof.
Admitted.

(* Lemma BN is more difficult; you may need

Lemma lemc:  forall (a: t 1), a = F1.
Proof.
Admitted.

Lemma BN: forall n (a: t (S n)), B (N a) = a.
Proof.
Admitted.
*)

(* Lifting *)

(* napisz definicję L, które każdej wartości w t n przypisze 
tę samą wartość w typie t (S n) 

Fixpoint L {n} (a: t n) : t (S n) :=
*)

Print L.

Lemma NL: forall n (a: t n), N a = N (L a).
Proof.
Admitted.

Lemma injL: forall n (a b: t n), L a  = L b -> a = b.
Proof.
Admitted.
