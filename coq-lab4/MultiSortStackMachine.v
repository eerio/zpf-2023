Require Import Extraction.
Require Import Bool List Arith Bool_nat. 
Set Implicit Arguments.


(** * Typed Expressions *)

(** In this section, we will build on the initial example by adding additional expression forms that depend on static typing of terms for safety. *)

(** ** Source Language *)

Inductive type : Set := Tint | Tbool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Tint Tint Tint
| TTimes : tbinop Tint Tint Tint
| TEq : forall t, tbinop t t Tbool
| TLt : tbinop Tint Tint Tbool.


Inductive texp : type -> Set :=
| TNConst : nat -> texp Tint
| TBConst : bool -> texp Tbool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
    | Tint => nat
    | Tbool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in tbinop arg1 arg2 res with
    | TPlus => plus
    | TTimes => mult
    | TEq Tint => beq_nat
    | TEq Tbool => eqb
    | TLt => leb
  end.


Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Print Implicit texpDenote.


Eval simpl in texpDenote (TNConst 42).
(** [= 42 : typeDenote Tint] *)

(* begin hide *)
Eval simpl in texpDenote (TBConst false).
(* end hide *)
Eval simpl in texpDenote (TBConst true).
(** [= true : typeDenote Tbool] *)

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= 28 : typeDenote Tint] *)

Eval simpl in texpDenote (TBinop (TEq Tint) (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= false : typeDenote Tbool] *)

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).
(** [= true : typeDenote Tbool] *)


(** ** Target Language *)

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Tint :: s)
| TiBConst : forall s, bool -> tinstr s (Tbool :: s)
| TiBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.


Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(** ** Translation *)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons i p1 => fun p' => TCons i (tconcat p1 p')
  end.


Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Print tcompile.

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
(** [= (42, tt) : vstack (Tint :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.
(** [= (true, tt) : vstack (Tbool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (28, tt) : vstack (Tint :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop (TEq Tint) (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.
(** [= (false, tt) : vstack (Tbool :: nil)] *)

Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)) nil) tt.
(** [= (true, tt) : vstack (Tbool :: nil)] *)

(** %\smallskip{}%The compiler seems to be working, so let us turn to proving that it _always_ works. *)


(** ** Translation Correctness *)


(** Again, we need to strengthen the theorem statement so that the induction will go through.  This time, to provide an excuse to demonstrate different tactics, I will develop an alternative approach to this kind of proof, stating the key lemma as: *)
(* We need an analogue to the [app_assoc_reverse] theorem that we used to rewrite the goal in the last section.  We can abort this proof and prove such a lemma about [tconcat].
*)


Lemma tconcat_correct : forall ts ts' ts'' 
  (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts),
  tprogDenote (tconcat p p') s = tprogDenote p' (tprogDenote p s).
Proof.
Admitted.


Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
Admitted.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
Proof.
Admitted.

Extraction tcompile.

(* End: *)
