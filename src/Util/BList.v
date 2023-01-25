Require Import List.
Import ListNotations.

Require Import IFOL.Util.Witness.
Require Import IFOL.Util.List_index.

(*
Inductive BList {X} (Y : list X -> Type) : list X -> Type :=
  | bnil : BList Y nil
  | bcons {xs} : Y xs -> BList Y xs -> BList Y xs
  | bump {xs} x : BList Y xs -> BList Y (cons x xs).



Arguments bnil {_} {_}.
Arguments bcons {_} {_} {_} _ _.
Arguments bump {_} {_} {_} _ _.

Inductive bindex {X} {Y : list X -> Type} :
  forall {xs}, BList Y xs -> Type :=
  | biz {xs} {y} {ys : BList Y xs} : bindex (bcons y ys)
  | bis {xs} {y} {ys : BList Y xs} :
      bindex ys -> bindex (bcons y ys)
  | bibump {xs} {ys : BList Y xs} {x} :
      bindex ys -> bindex (bump x ys).

Record bindex_result {X} {Y} {xs : list X} (ys : BList Y xs) : Type := {
  suff : list X;
  suff_wit : suffix_wit suff xs;
  data : Y suff
  }.

Fixpoint bl_proj {X} {Y : list X -> Type} {xs}
  (ys : BList Y xs) (i : bindex ys) : bindex_result ys.
Proof.
  destruct i eqn:?.
  - econstructor.
    2:{ exact y. }
    apply sw_refl.
  - epose (bl_proj X Y xs ys b).
    destruct b0.
    econstructor.
    2:{ exact data0. }
    exact suff_wit0.
  - epose (bl_proj X Y xs ys b).
    destruct b0.
    econstructor.
    apply sw_cons.
    exact suff_wit0.
    exact data0.
Defined.
 *)

Fixpoint BList {X} (Y : list X -> Type) (xs : list X) : Type :=
  match xs with
  | [] => list (Y [])
  | x :: xs' => list (Y xs) * (BList Y xs')
  end.

Definition bnil {X} {Y : list X -> Type} : BList Y nil :=
  nil.

Definition bcons {X} {Y : list X -> Type} {xs : list X}
  : Y xs -> BList Y xs -> BList Y xs :=
  match xs with
  | [] => cons
  | x :: xs' => fun y ys =>
    match ys with
    | (ys, ys') => (y :: ys, ys')
    end
  end.

Definition bump {X} {Y : list X -> Type} {xs : list X} (x : X) :
  BList Y xs -> BList Y (cons x xs) :=
  pair nil.

Fixpoint bindex {X} {Y : list X -> Type} {xs} : BList Y xs -> Type :=
  match xs with
  | [] => list_index
  | _ :: _ => fun '(l, b) => (list_index l + bindex b)%type
  end.

Record bindex_result {X} {Y} {xs : list X} (ys : BList Y xs) : Type := {
  suff : list X;
  suff_wit : suffix_wit suff xs;
  data : Y suff
  }.

Fixpoint bl_proj {X} {Y : list X -> Type} {xs} :
  forall ys : BList Y xs, bindex ys -> bindex_result ys.
Proof.
  destruct xs.
  - intros.
    simpl in *.
    econstructor.
    2:{ exact (list_proj ys X0). }
    constructor.
  - intros.
    simpl in *.
    destruct ys.
    destruct X0.
    + econstructor.
      2:{ exact (list_proj l l0). }
      apply sw_refl.
    + destruct (bl_proj X Y xs b b0).
      econstructor.
      2:{ exact data0. }
      apply sw_cons.
      exact suff_wit0.
Defined.
