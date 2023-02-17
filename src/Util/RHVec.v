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

Fixpoint rhv_proj {X} {Y : X -> Type} {xs} {x} (w : witness x xs)
  : RHVec Y xs -> Y x :=
  match w with
  | whd => fst
  | wtl w' => fun '(_, tl) => rhv_proj w' tl
  end.

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
  {xs xs'} {x} (pw : part_witness x xs' xs) {struct pw} :
  Y x -> RHVec Y xs' -> RHVec Y xs :=
  match pw with
  | pwhd => pair
  | pwtl pw' => fun y '(hd, tl) => (hd, rhv_insert pw' y tl)
  end.

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

Fixpoint rhv_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) {struct w} : Y x -> RHVec Y xs -> RHVec Y xs :=
  match w with
  | whd => fun y '(_, tl) => (y, tl)
  | wtl w' => fun y '(hd, tl) => (hd, rhv_replace w' y tl)
  end.

Lemma of_hvec_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (y : Y x) (v : HVec Y xs) :
  of_hvec (hvec_replace w y v) = rhv_replace w y (of_hvec v).
Proof.
  induction w; dependent destruction v.
  - reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma rhv_map_replace {X} {Y Z : X -> Type} {xs} {x}
  (f : forall x, Y x -> Z x) (w : witness x xs) (y : Y x)
  (ys : RHVec Y xs) :
  rhv_map f (rhv_replace w y ys) =
  rhv_replace w (f x y) (rhv_map f ys).
Proof.
  induction w; destruct ys; simpl.
  - reflexivity.
  - now rewrite IHw.
Defined.

Lemma rhv_proj_of_hvec {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : HVec Y xs) :
  rhv_proj w (of_hvec ys) = hvec_proj ys w.
Proof.
  induction w; dependent destruction ys.
  - reflexivity.
  - apply IHw.
Defined.

Lemma rhv_proj_map {X} {Y Z : X -> Type} {xs} {x} (f : forall x, Y x -> Z x)
  (ys : RHVec Y xs) (w : witness x xs) :
  rhv_proj w (rhv_map f ys) =
  f x (rhv_proj w ys).
Proof.
  induction w.
  - now destruct ys.
  - destruct ys; simpl.
    now rewrite IHw.
Defined.

Lemma rhv_proj_replace {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : RHVec Y xs) (y : Y x) :
  rhv_proj w (rhv_replace w y ys) = y.
Proof.
  induction w; simpl; now destruct ys.
Qed.

Lemma rhv_proj_replace_neq {X} {Y : X -> Type} {xs} {x x'}
  (w : witness x xs) (w' : witness x' xs) (ys : RHVec Y xs) (y : Y x') :
  nat_of_wit w <> nat_of_wit w' ->
  rhv_proj w (rhv_replace w' y ys) = rhv_proj w ys.
Proof.
  intro Hneq.
  induction w.
  - dependent destruction w'.
    + now elim Hneq.
    + simpl; now destruct ys.
  - dependent destruction w'.
    + simpl; now destruct ys.
    + simpl; destruct ys.
      apply IHw.
      simpl in Hneq; auto.
Qed.

Lemma rhv_replace_proj {X} {Y : X -> Type} {xs} {x}
  (w : witness x xs) (ys : RHVec Y xs) :
  rhv_replace w (rhv_proj w ys) ys = ys.
Proof.
  induction w.
  - now destruct ys.
  - simpl.
    destruct ys.
    now rewrite IHw.
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

Fixpoint rhv_proj_rhv_insert_witness_weak {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x xs' xs) (w : witness x' xs')
  (y : Y x) (v : RHVec Y xs') {struct pw} :
  rhv_proj (witness_weak pw w) (rhv_insert pw y v) =
  rhv_proj w v.
Proof.
  destruct pw.
  - reflexivity.
  - dependent destruction w.
    + simpl.
      now destruct v.
    + simpl.
      destruct v.
      apply rhv_proj_rhv_insert_witness_weak.
Defined.

Lemma rhv_proj_rhv_insert_invert {X} {Y : X -> Type}
  {xs xs'} {x x'} (pw : part_witness x' xs' xs) (w : witness x xs)
  (w' : witness x xs') (v : RHVec Y xs') (a : Y x') :
  witness_invert pw w = inr w' ->
  rhv_proj w' v =
  rhv_proj w (rhv_insert pw a v).
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
  - destruct v; simpl in *.
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

Lemma rhv_proj_rhv_insert_invert2 {X} {Y : X -> Type}
  {xs xs'} {x} (pw : part_witness x xs' xs) (w : witness x xs)
  (pf : x = x) (v : RHVec Y xs') (a : Y x) :
  witness_invert pw w = inl pf ->
  rhv_proj w (rhv_insert pw a v) = a.
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
      destruct (witness_invert pw w) eqn:?.
      * destruct v; simpl.
        eapply IHpw.
        exact Heqs.
      * unfold solution_left in H.
        unfold eq_rect_r in H.
        unfold eq_rect in H.
        simpl in H.
        rewrite Heqs in H.
        discriminate.
Defined.
