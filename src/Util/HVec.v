Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

Require Import IFOL.Util.Witness.

Inductive HVec {X} (Y : X -> Type) : list X -> Type :=
  | hvnil : HVec Y []
  | hvcons : forall {x} {xs},
      Y x -> HVec Y xs -> HVec Y (x::xs).

Arguments hvnil {_} {_}.
Arguments hvcons {_} {_} {_} {_}.

Fixpoint hvec_proj {X} {Y : X -> Type} {xs} (v : HVec Y xs) {struct v} :
  forall {x}, witness x xs -> Y x.
Proof.
  destruct v.
  - intros x w.
    dependent destruction w.
  - intros z w.
    dependent destruction w.
    + exact y.
    + exact (hvec_proj X Y xs v y0 w).
Defined.

Fixpoint hvec_map {X} {Y Z : X -> Type} {xs} (f : forall x, Y x -> Z x)
  (ys : HVec Y xs) : HVec Z xs :=
  match ys with
  | hvnil => hvnil
  | hvcons y ys' => hvcons (f _ y) (hvec_map f ys')
  end.

Lemma hvec_proj_map {X} {Y Z : X -> Type} {xs} {x} (f : forall x, Y x -> Z x)
  (ys : HVec Y xs) (w : witness x xs) :
  hvec_proj (hvec_map f ys) w =
  f x (hvec_proj ys w).
Proof.
  induction ys.
  - dependent destruction w.
  - dependent destruction w.
    + reflexivity.
    + simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      apply IHys.
Defined.

Lemma HVec_rect_map {X} {Y Z : X -> Type} {xs} (f : forall x, Y x -> Z x) :
  forall ys : HVec Y xs,
  hvec_map f ys =
  HVec_rect X Y (fun xs0 _ => HVec Z xs0) hvnil
    (fun (x : X) (xs0 : list X) (y : Y x)
      (_ : HVec Y xs0) (IHys : HVec Z xs0) =>
    hvcons (f x y) IHys) xs ys.
Proof.
  induction ys.
  - reflexivity.
  - simpl.
    now rewrite IHys.
Defined.

Fixpoint hvec_insert {X} {Y : X -> Type}
  {xs xs'} {x} (pw : part_witness x xs' xs) {struct pw} :
  Y x -> HVec Y xs' -> HVec Y xs.
Proof.
  destruct pw.
  - exact hvcons.
  - intros u v.
    dependent destruction v.
    + apply (hvcons y0).
      eapply hvec_insert.
      * exact pw.
      * exact u.
      * exact v.
Defined.

Fixpoint hvec_proj_hvec_insert_witness_weak {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x xs' xs) (w : witness x' xs')
  (y : Y x) (v : HVec Y xs') {struct pw} :
  hvec_proj (hvec_insert pw y v) (witness_weak pw w) =
  hvec_proj v w.
Proof.
  destruct pw.
  - reflexivity.
  - dependent destruction w.
    + dependent destruction v.
      reflexivity.
    + dependent destruction v.
      simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      apply hvec_proj_hvec_insert_witness_weak.
Defined.
(* todo: without axioms *)

Lemma hvev_proj_hvec_insert_invert {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x' xs' xs) (w : witness x xs)
  (w' : witness x xs') (v : HVec Y xs') (a : Y x') :
  witness_invert pw w = inr w' ->
  hvec_proj v w' =
  hvec_proj (hvec_insert pw a v) w.
Proof.
  intro H.
  induction pw.
  - simpl in *.
    dependent destruction w.
    + discriminate.
    + simpl in *.
      unfold solution_left in *.
      unfold eq_rect_r in *.
      unfold eq_rect in *.
      simpl in *.
      congruence.
  - dependent destruction v.
    simpl in *.
    dependent destruction w.
    + simpl in *.
      unfold solution_left in *.
      unfold eq_rect_r in *.
      unfold eq_rect in *.
      simpl in *.
      inversion H; reflexivity.
    + unfold solution_left in *.
      unfold eq_rect_r in *.
      unfold eq_rect in *.
      simpl in *.
      destruct (witness_invert pw w) eqn:?.
      * discriminate.
      * inversion H.
        simpl.
        apply IHpw; auto.
Defined.

Lemma hvec_proj_hvec_insert_invert2 {X} {Y : X -> Type}
  {xs xs'} {x} (pw : part_witness x xs' xs) (w : witness x xs)
  (pf : x = x) (v : HVec Y xs') (a : Y x) :
  witness_invert pw w = inl pf ->
  hvec_proj (hvec_insert pw a v) w = a.
Proof.
  intro H.
  induction pw.
  - simpl in *.
    dependent destruction w.
    + reflexivity.
    + discriminate.
  - simpl in *.
    dependent destruction w.
    + discriminate.
    + simpl in *.
      unfold solution_left in *.
      unfold eq_rect_r in *.
      unfold eq_rect in *.
      simpl in *.
      destruct (witness_invert pw w) eqn:?.
      * dependent destruction v; simpl.
        unfold solution_left.
        unfold eq_rect_r.
        unfold eq_rect. simpl.
        eapply IHpw.
        exact Heqs.
      * discriminate.
Defined.

Fixpoint hvec_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (y : Y x) {struct w} : HVec Y xs -> HVec Y xs.
Proof.
  destruct w; intro v; dependent destruction v.
  - exact (hvcons y v).
  - exact (hvcons y1 (hvec_replace _ _ _ _ w y v)).
Defined.

Lemma hvec_map_replace {X} {Y Z : X -> Type} {xs} {x}
  (f : forall x, Y x -> Z x) (w : witness x xs) (y : Y x)
  (ys : HVec Y xs) :
  hvec_map f (hvec_replace w y ys) =
  hvec_replace w (f x y) (hvec_map f ys).
Proof.
  induction ys.
  - dependent destruction w.
  - dependent destruction w.
    + reflexivity.
    + simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      now rewrite IHys.
Defined.

Lemma hvec_replace_proj {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : HVec Y xs) :
  hvec_replace w (hvec_proj ys w) ys = ys.
Proof.
  induction ys.
  - dependent destruction w.
  - dependent destruction w.
    + reflexivity.
    + simpl.
      unfold solution_left.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      now rewrite IHys.
Defined.

Fixpoint hvec_suff {X} {Y : X -> Type} {xs} {ys}
  (w : suffix_wit xs ys) : HVec Y ys -> HVec Y xs.
Proof.
  destruct w.
  - exact (fun x => x).
  - intro v.
    dependent destruction v.
    exact (hvec_suff X Y xs ys w v).
Defined.
