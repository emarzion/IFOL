Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

Require Import IFOL.Util.List_index.
Require Import IFOL.Util.HVec.
Require Import IFOL.Util.Witness.

Fixpoint RHVec {X} (Y : X -> Type) (xs : list X) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => Y x * RHVec Y xs'
  end.

Fixpoint rhv_proj {X} {Y : X -> Type} {xs}
  {x} (w : witness x xs) {struct xs}
  : RHVec Y xs -> Y x.
Proof.
  destruct xs.
  - destruct w.
  - destruct w.
    + destruct e.
      exact fst.
    + intros [_ tl].
      exact (rhv_proj _ _ _ _ w tl).
Defined.

Fixpoint rhv_map {X} {Y Z : X -> Type} (f : forall x, Y x -> Z x)
  {xs : list X} : RHVec Y xs -> RHVec Z xs :=
  match xs with
  | [] => fun _ => tt
  | x :: xs' => fun '(hd, tl) => (f x hd, rhv_map f tl)
  end.

Fixpoint of_hvec {X} {Y : X -> Type} {xs} (v : HVec Y xs)
  : RHVec Y xs :=
  match v with
  | hvnil => tt
  | hvcons y ys => (y, of_hvec ys)
  end.

Fixpoint rhv_insert {X} {Y : X -> Type}
  {xs xs'} {x} (pw : part_witness x xs' xs) {struct xs} :
  Y x -> RHVec Y xs' -> RHVec Y xs.
Proof.
  destruct xs.
  - destruct pw.
  - destruct pw.
    destruct p.
    destruct e,e0.
    + exact pair.
    + destruct xs'.
      * destruct y.
      * destruct y.
        destruct e.
        intros y1 [y2 tl].
        apply (pair y2).
        eapply rhv_insert.
        ** exact p.
        ** exact y1.
        ** exact tl.
Defined.

Lemma HVec_rect_map {X} {Y Z : X -> Type} {xs} (f : forall x, Y x -> Z x) :
  forall ys : HVec Y xs,
  rhv_map f (of_hvec ys) =
  HVec_rect X Y (fun xs0 _ => RHVec Z xs0) tt
    (fun (x : X) (xs0 : list X) (y : Y x)
      (_ : HVec Y xs0) (IHys : RHVec Z xs0) =>
    pair (f x y) IHys) xs ys.
Proof.
  induction ys.
  - reflexivity.
  - simpl.
    now rewrite IHys.
Defined.

Fixpoint rhv_replace {X} {Y : X -> Type}
  {xs} {x} (w : witness x xs) {struct xs} : Y x -> RHVec Y xs -> RHVec Y xs.
Proof.
  destruct xs.
  - destruct w.
  - destruct w.
    + destruct e.
      intros y [_ tl].
      exact (y, tl).
    + intros y1 [y2 tl].
      apply (pair y2).
      eapply rhv_replace.
      exact w.
      exact y1.
      exact tl.
Defined.

Lemma of_hvec_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (y : Y x) (v : HVec Y xs) :
  of_hvec (hvec_replace w y v) = rhv_replace w y (of_hvec v).
Proof.
  induction v.
  - destruct w.
  - destruct w.
    + now destruct e.
    + simpl.
      now rewrite IHv.
Defined.

Lemma rhv_map_replace {X} {Y Z : X -> Type} {xs} {x}
  (f : forall x, Y x -> Z x) (w : witness x xs) (y : Y x)
  (ys : RHVec Y xs) :
  rhv_map f (rhv_replace w y ys) =
  rhv_replace w (f x y) (rhv_map f ys).
Proof.
  induction xs.
  - destruct w.
  - simpl.
    destruct w.
    + destruct e.
      now destruct ys.
    + destruct ys.
      now rewrite IHxs.
Defined.

Lemma rhv_proj_of_hvec {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : HVec Y xs) :
  rhv_proj w (of_hvec ys) = hvec_proj ys w.
Proof.
  induction ys.
  - destruct w.
  - simpl.
    destruct w.
    + now destruct e.
    + apply IHys.
Defined.

Lemma rhv_proj_map {X} {Y Z : X -> Type} {xs} {x} (f : forall x, Y x -> Z x)
  (ys : RHVec Y xs) (w : witness x xs) :
  rhv_proj w (rhv_map f ys) =
  f x (rhv_proj w ys).
Proof.
  induction xs.
  - destruct w.
  - destruct w.
    + simpl.
      destruct e.
      now destruct ys.
    + destruct ys.
      simpl.
      apply IHxs.
Defined.

Lemma rhv_proj_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : RHVec Y xs) (y : Y x) :
  rhv_proj w (rhv_replace w y ys) = y.
Proof.
  induction xs.
  - destruct w.
  - destruct w.
    + destruct e.
      now destruct ys.
    + destruct ys; simpl.
      apply IHxs.
Defined.

Lemma rhv_proj_replace_neq {X} {Y : X -> Type} {xs} {x x'}
  (w : witness x xs) (w' : witness x' xs) (ys : RHVec Y xs) (y : Y x') :
  nat_of_wit w <> nat_of_wit w' ->
  rhv_proj w (rhv_replace w' y ys) = rhv_proj w ys.
Proof.
  intro Hneq.
  induction xs.
  - destruct w.
  - destruct w.
    + destruct e.
      destruct w'.
      * destruct e.
        now destruct ys.
      * now destruct ys.
    + destruct w'.
      * destruct e.
        now destruct ys.
      * simpl.
        destruct ys.
        apply IHxs.
        intro Heq.
        apply Hneq.
        simpl.
        now destruct Heq.
Defined.

Lemma rhv_replace_proj {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : RHVec Y xs) :
  rhv_replace w (rhv_proj w ys) ys = ys.
Proof.
  induction xs.
  - destruct w.
  - destruct w.
    + destruct e.
      now destruct ys.
    + simpl.
      destruct ys.
      now rewrite IHxs.
Defined.

Fixpoint rhv_suff {X} {Y : X -> Type} {xs} {ys}
  (w : suffix_wit xs ys) : RHVec Y ys -> RHVec Y xs :=
  match w with
  | sw_refl => fun v => v
  | sw_cons w' => fun '(_, tl) => rhv_suff w' tl
  end.

Fixpoint rhv_index_proj {X} {Y : X -> Type}
  {xs : list X} (i : list_index xs)
  (v : RHVec Y xs) {struct xs} : Y (list_proj xs i).
Proof.
  destruct xs.
  - destruct i.
  - simpl in *.
    destruct i.
    + exact (fst v).
    + exact (rhv_index_proj X Y xs l (snd v)).
Defined.

Fixpoint rhv_proj_rhv_insert_witness_weak
  {X} {Y : X -> Type}
  {xs xs'} {x x'}
  (pw : part_witness x xs' xs)
  (w : witness x' xs')
  (y : Y x) (v : RHVec Y xs') {struct xs} :
  rhv_proj (witness_weak pw w) (rhv_insert pw y v) =
  rhv_proj w v.
Proof.
  destruct xs.
  - destruct pw.
  - destruct pw.
    + destruct xs'.
      * destruct w.
      * destruct w.
        ** simpl.
           destruct p.
           destruct e0.
           destruct e1.
           now destruct e.
        ** simpl.
           destruct p.
           destruct e.
           destruct e0.
           now destruct v.
    + destruct xs'.
      * destruct y0.
      * simpl.
        destruct w.
        ** destruct e.
           destruct y0.
           destruct e.
           now destruct v.
        ** destruct y0.
           destruct e.
           destruct v.
           apply rhv_proj_rhv_insert_witness_weak.
Defined.

Fixpoint rhv_proj_rhv_insert_invert {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x' xs' xs) (w : witness x xs)
  (w' : witness x xs') (v : RHVec Y xs') (a : Y x') {struct xs} :
  witness_invert pw w = inr w' ->
  rhv_proj w' v =
  rhv_proj w (rhv_insert pw a v).
Proof.
  intro H.
  destruct xs.
  - destruct w.
  - destruct w.
    + simpl.
      destruct e.
      destruct pw.
      * destruct p.
        destruct e.
        destruct e0.
        simpl in *.
        destruct xs'.
        ** destruct w'.
        ** discriminate.
      * simpl in *.
        destruct xs'.
        ** destruct y.
        ** destruct y.
           destruct e.
           destruct v.
           now inversion H.
    + simpl.
      destruct pw.
      * destruct p.
        destruct e.
        destruct e0.
        simpl in H.
        destruct xs'.
        ** destruct w.
        ** now inversion H.
      * destruct xs'.
        destruct y.
        destruct y.
        destruct e.
        destruct v.
        simpl in *.
        destruct witness_invert eqn:G.
        ** discriminate.
        ** inversion H.
           eapply rhv_proj_rhv_insert_invert.
           exact G.
Defined.

Fixpoint rhv_proj_rhv_insert_invert2 {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x xs' xs) (w : witness x' xs)
  (pf : x' = x)
  (v : RHVec Y xs') (a : Y x) {struct xs} :
  witness_invert pw w = inl pf
 ->
  rhv_proj w (rhv_insert pw a v)
  = match eq_sym pf with
    | eq_refl => a
    end.
Proof.
  intro.
  destruct xs.
  - destruct w.
  - destruct w.
    + simpl.
      destruct e.
      destruct pw.
      * destruct p.
        destruct e,e0.
        simpl in H.
        destruct xs'.
        ** assert (eq_refl = pf).
           { eapply inl_inj. exact H. }
           destruct H0.
           reflexivity.
        ** assert (eq_refl = pf).
           { eapply inl_inj. exact H. }
           destruct H0.
           reflexivity.
      * simpl in H.
        destruct xs'.
        ** destruct y.
        ** destruct y.
           discriminate.
    + simpl.
      destruct pw.
      * simpl in H.
        destruct xs'.
        ** destruct p.
           destruct e,e0.
           destruct w.
        ** destruct p.
           destruct e, e0.
           discriminate.
      * destruct xs'.
        ** destruct y.
        ** destruct y.
           simpl in H.
           destruct witness_invert eqn:G.
           *** destruct e.
               destruct v.
               eapply rhv_proj_rhv_insert_invert2.
               rewrite G.
               now rewrite (inl_inj _ _ H).
           *** discriminate.
Defined.
