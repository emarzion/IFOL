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
    destruct w.
  - intros z w.
    destruct w.
    + destruct e.
      exact y.
    + exact (hvec_proj X Y xs v _ w).
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
  - destruct w.
  - destruct w.
    + destruct e.
      reflexivity.
    + simpl.
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
  {xs xs'} {x} (pw : part_witness x xs' xs)
  (y : Y x) (v : HVec Y xs') {struct v} : HVec Y xs.
Proof.
  destruct v.
  - destruct xs.
    + destruct pw.
    + destruct pw.
      * destruct p.
        destruct e,e0.
        exact (hvcons y hvnil).
      * destruct e.
  - destruct xs.
    + destruct pw.
    + destruct pw.
      * destruct p.
        destruct e,e0.
        exact (hvcons y (hvcons y0 v)).
      * destruct p.
        destruct e.
        apply (hvcons y0).
        eapply hvec_insert.
        ** exact p.
        ** exact y.
        ** exact v.
Defined.

Fixpoint hvec_proj_hvec_insert_witness_weak
  {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x xs' xs)
  (w : witness x' xs')
  (y : Y x) (v : HVec Y xs') {struct v} :
  hvec_proj (hvec_insert pw y v) (witness_weak pw w) =
  hvec_proj v w.
Proof.
  destruct v.
  - destruct w.
  - simpl.
    destruct xs.
    + destruct pw.
    + destruct pw.
      * destruct p.
        destruct e, e0.
        destruct w.
        ** now destruct e.
        ** reflexivity.
      * destruct p.
        destruct e.
        destruct w.
        ** destruct e.
           reflexivity.
        ** simpl.
           apply hvec_proj_hvec_insert_witness_weak.
Defined.

Lemma inl_inj {A B} :
  forall x y : A, @inl A B x = inl y ->
  x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Defined.

Lemma inr_inj {A B} :
  forall x y : B, @inr A B x = inr y ->
  x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Defined.

Fixpoint hvec_proj_hvec_insert_invert {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x' xs' xs) (w : witness x xs)
  (w' : witness x xs') (v : HVec Y xs') (a : Y x')
  {struct v} :
  witness_invert pw w = inr w' ->
  hvec_proj v w' =
  hvec_proj (hvec_insert pw a v) w.
Proof.
  destruct v.
  - intro.
    destruct w'.
  - intro.
    simpl.
    destruct w'.
    + destruct e.
      destruct xs.
      * destruct pw.
      * destruct pw.
        ** destruct p.
           destruct e, e0.
           simpl in H.
           destruct w.
           *** discriminate.
           *** now inversion H.
        ** destruct p.
           destruct e.
           simpl in H.
           destruct w.
           *** assert (eq_refl = e).
               { eapply inl_inj.
                 eapply inr_inj.
                 symmetry in H.
                 exact H.
               }
               destruct H0.
               reflexivity.
           *** destruct (witness_invert p w); discriminate.
    + destruct xs.
      * destruct pw.
      * destruct pw.
        ** destruct p.
           destruct e, e0.
           simpl.
           destruct w.
           *** discriminate.
           *** inversion H.
               reflexivity.
        ** destruct p.
           destruct e.
           
           simpl in *.
           destruct w.
           *** simpl.
               destruct e.
           simpl.
           inversion H.
           *** destruct witness_invert eqn:?.
               **** discriminate.
               **** erewrite hvec_proj_hvec_insert_invert.
                    reflexivity.
                    inversion H.
                    destruct H1.
                    exact Heqs.
Defined.

(*
Fixpoint hvec_proj_hvec_insert_invert2 {X} {Y : X -> Type}
  {xs xs'} {x} (pw : part_witness x xs' xs) (w : witness x xs)
  (v : HVec Y xs') (a : Y x) {struct v} :
  witness_invert pw w = inl eq_refl ->
  hvec_proj (hvec_insert pw a v) w = a.
Proof.
  destruct v; intro H.
  - simpl.
    destruct xs.
    + destruct pw.
    + destruct pw.
      destruct p.
      destruct e, e0.
      simpl in *.
      destruct w.
      simpl.
      simpl in H.
      dependent destruction e.
      reflexivity.
      simpl.
      destruct e.
      destruct e.
  - simpl.
    destruct xs.
    destruct pw.
    destruct pw.
    destruct p.
    + destruct e.
      destruct e0.
      simpl.
      simpl in H.
      destruct w.
      assert (e = eq_refl).
      { eapply inl_inj. exact H. }
      rewrite H0.
      reflexivity.
      discriminate.
    + destruct p.
      destruct e.
      simpl.
      destruct w.
      * discriminate.
      * apply hvec_proj_hvec_insert_invert2.
        simpl in H.
        destruct witness_invert.
        ** f_equal.
           eapply inl_inj.
           exact H.
        ** discriminate.
Defined.
Print Assumptions hvec_proj_hvec_insert_invert2.
(* FIXME*)
*)

Fixpoint hvec_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (y : Y x) (v : HVec Y xs) {struct v} : HVec Y xs.
Proof.
  destruct v.
  - destruct w.
  - destruct w.
    + destruct e.
      exact (hvcons y v).
    + exact (hvcons y0
        (hvec_replace _ _ _ _ w y v)).
Defined.

Lemma hvec_map_replace {X} {Y Z : X -> Type} {xs} {x}
  (f : forall x, Y x -> Z x) (w : witness x xs) (y : Y x)
  (ys : HVec Y xs) :
  hvec_map f (hvec_replace w y ys) =
  hvec_replace w (f x y) (hvec_map f ys).
Proof.
  induction ys.
  - destruct w.
  - destruct w.
    + destruct e.
      reflexivity.
    + simpl.
      now rewrite IHys.
Defined.

Lemma hvec_replace_proj {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : HVec Y xs) :
  hvec_replace w (hvec_proj ys w) ys = ys.
Proof.
  induction ys.
  - destruct w.
  - destruct w.
    + destruct e.
      reflexivity.
    + simpl.
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
