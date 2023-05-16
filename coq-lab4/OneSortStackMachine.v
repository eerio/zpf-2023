(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)


(** %\chapter{Some Quick Examples}% *)

(** I will start off by jumping right in to a fully worked set of examples, building certified compilers from increasingly complicated source languages to stack machines.  We will meet a few useful tactics and see how they can be used in manual proofs, and we will also see how easily these proofs can be automated instead.  This chapter is not meant to give full explanations of the features that are employed.  Rather, it is meant more as an advertisement of what is possible.  Later chapters will introduce all of the concepts in bottom-up fashion.  In other words, it is expected that most readers will not understand what exactly is going on here, but I hope this demo will whet your appetite for the remaining chapters!

As always, you can step through the source file <<StackMachine.v>> for this chapter interactively in Proof General.  Alternatively, to get a feel for the whole lifecycle of creating a Coq development, you can enter the pieces of source code in this chapter in a new <<.v>> file in an Emacs buffer.  If you do the latter, include these two lines at the start of the file. *)

Require Import Bool Arith List. 
Set Implicit Arguments.

(** ** Source Language *)

Inductive binop : Set := Plus | Times.


Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.


Check mult.
Print Init.Nat.mul.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.


Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.


Eval simpl in expDenote (Const 42).
(** [= 42 : nat] *)

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
(** [= 4 : nat] *)

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= 28 : nat] *)



(** ** Target Language *)


Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.


Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.


Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.



(** ** Translation *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.



Eval simpl in compile (Const 42).
(** [= iConst 42 :: nil : prog] *)

Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
(** [= iConst 2 :: iConst 2 :: iBinop Plus :: nil : prog] *)

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= iConst 7 :: iConst 2 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil : prog] *)

(** %\smallskip{}%We can also run our compiled programs and check that they give the right results. *)

Eval simpl in progDenote (compile (Const 42)) nil.
(** [= Some (42 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
(** [= Some (4 :: nil) : option stack] *)

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2))
  (Const 7))) nil.
(** [= Some (28 :: nil) : option stack] *)


(** ** Translation Correctness *)

SearchRewrite ((_ ++ _) ++ _).


Check app_assoc_reverse.


Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
induction e.
intros.
unfold compile.
unfold expDenote.
unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.
intros.
unfold compile.
fold compile.
unfold expDenote.
fold expDenote.
rewrite app_assoc_reverse.
rewrite IHe2.
rewrite app_assoc_reverse.
rewrite IHe1.
unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.
Qed.


Check app_nil_end.


Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
intros.
rewrite (app_nil_end (compile e)).
rewrite (compile_correct').
reflexivity.
Qed.



