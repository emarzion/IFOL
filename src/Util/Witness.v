Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

(** [witness x xs] is an informative proof that
    x is an element of xs. *)
Inductive witness {X} : X -> list X -> Type :=
  | whd {x} {xs} :
      witness x (x :: xs)
  | wtl {x y} {xs} :
      witness y xs ->
      witness y (x :: xs).

(** [part_witness x xs ys is an informative proof that
    x can be placed somewhere in xs to produce ys. *)
Inductive part_witness {X} : X -> list X -> list X -> Type :=
  | pwhd {x} {xs} :
      part_witness x xs (x :: xs)
  | pwtl {x y} {xs ys} :
      part_witness x xs ys ->
      part_witness x (y :: xs) (y :: ys).

Fixpoint witness_weak {X} {xs xs'} {x x' : X}
  (pw : part_witness x' xs' xs)
  {struct pw} : witness x xs' -> witness x xs.
Proof.
  destruct pw.
  - apply wtl.
  - intro w.
    inversion w.
    + apply whd.
    + apply wtl.
      exact (witness_weak _ _ _ _ _ pw X0).
Defined.

Fixpoint witness_invert {X} {xs xs'} {x x' : X}
  (pw : part_witness x' xs' xs)
  (w : witness x xs) {struct pw} :
  (x = x') + witness x xs'.
Proof.
  destruct pw.
  - dependent destruction w.
    + left; reflexivity.
    + right; exact w.
  - dependent destruction w.
    + right. apply whd.
    + destruct (witness_invert _ _ _ _ _ pw w).
      * left; exact e.
      * right; apply wtl; exact w0.
Defined.

Inductive suffix_wit {X} : list X -> list X -> Type :=
  | sw_refl {xs} : suffix_wit xs xs
  | sw_cons {xs} {x} {ys} : suffix_wit xs ys ->
      suffix_wit xs (x :: ys).

Fixpoint sw_nil {X} (xs : list X) : suffix_wit [] xs :=
  match xs with
  | [] => sw_refl
  | x :: ys => sw_cons (sw_nil ys)
  end.
