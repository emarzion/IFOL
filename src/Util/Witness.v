Require Import List.
Import ListNotations.

(** [witness x xs] is an informative proof that
    x is an element of xs. *)
Fixpoint witness {X} (x : X) (xs : list X) : Type :=
  match xs with
  | [] => Empty_set
  | y :: ys => (x = y) + witness x ys
  end.

Definition whd {X} {x : X} {xs : list X} :
  witness x (x :: xs) :=
  inl eq_refl.

Definition wtl {X} {x y : X} {xs : list X} :
  witness x xs -> witness x (y :: xs) :=
  fun w => inr w.

Definition witness_heq {X} {xs} {x x' : X}
  (w : witness x xs) (w' : witness x' xs) : Prop :=
  exists pf : x = x',
    match pf with
    | eq_refl => fun v => w = v
    end w'.

Fixpoint nat_of_wit {X} {x : X} {xs} : witness x xs -> nat :=
  match xs with
  | [] => fun e =>
    match e with
    end
  | y :: ys => fun w =>
    match w with
    | inl _ => 0
    | inr w' => S (nat_of_wit w')
    end
  end.

Definition witness_hneq {X} {xs} {x x' : X}
  (w : witness x xs) (w' : witness x' xs) : Prop :=
  nat_of_wit w <> nat_of_wit w'.

Lemma heq_of_nat_eq {X} {xs} {x x' : X}
  (w : witness x xs) (w' : witness x' xs) :
  nat_of_wit w = nat_of_wit w' -> witness_heq w w'.
Proof.
  intro.
  induction xs.
  - destruct w.
  - destruct w, w'.
    + destruct e0.
      exists e.
      now destruct e.
    + inversion H.
    + inversion H.
    + inversion H as [G].
      destruct (IHxs _ _ G).
      destruct x0.
      exists eq_refl.
      now rewrite H0.
Defined.

(** [part_witness x xs ys is an informative proof that
    x can be placed somewhere in xs to produce ys. *)
Fixpoint part_witness {X} (x : X) (xs ys : list X) {struct ys} : Type :=
  match ys with
  | [] => Empty_set
  | y :: ys' => ((x = y) * (xs = ys')) +
    match xs with
    | [] => Empty_set
    | x' :: xs' => (x' = y) * part_witness x xs' ys'
    end
  end.

Definition pwhd {X} {x : X} {xs : list X} :
  part_witness x xs (x :: xs) :=
  inl (eq_refl, eq_refl).

Definition pwtl {X} {x y : X} {xs ys : list X} :
  part_witness x xs ys -> part_witness x (y :: xs) (y :: ys) :=
  fun w => inr (eq_refl, w).

Fixpoint witness_weak {X} {xs xs'} {x x' : X}
  (pw : part_witness x' xs' xs)
  {struct xs'} : witness x xs' -> witness x xs.
Proof.
  destruct xs'.
  - intro w; destruct w.
  - intro w.
    destruct w.
    + destruct xs.
      * destruct pw.
      * simpl in pw.
        destruct pw.
        ** right.
           destruct e.
           destruct p.
           destruct e0.
           left; reflexivity.
        ** destruct e.
           destruct p.
           destruct e.
           left; reflexivity.
    + destruct xs.
      * destruct pw.
      * simpl in pw.
        destruct pw.
        ** right.
           destruct p.
           destruct e0.
           right; exact w.
        ** right.
           eapply witness_weak.
           apply p.
           apply w.
Defined.

Fixpoint witness_invert {X} {xs xs'} {x x' : X}
  (pw : part_witness x' xs' xs)
  (w : witness x xs) {struct xs} :
  (x = x') + witness x xs'.
Proof.
  destruct xs.
  - destruct w.
  - destruct xs'.
    + left.
      destruct pw.
      * destruct w.
        ** destruct p.
           destruct e.
           destruct e0.
           reflexivity.
        ** destruct p.
           destruct e0.
           destruct w.
      * destruct e.
    + destruct pw.
      * destruct p.
        destruct e.
        destruct w.
        ** left; exact e.
        ** destruct e0.
           right; exact w.
      * destruct w.
        destruct p.
        ** right; left.
           destruct e0.
           exact e.
        ** destruct p.
           destruct (witness_invert _ _ _ _ _ p w).
           *** left. exact e0.
           *** right; right; exact w0.
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
