Require Import List.
Import ListNotations.

Require Import Coq.Program.Equality.

Require Import IFOL.Util.RHVec.
Require Import IFOL.Util.BList.

(* Inductive BVec {X} {Y : list X -> Type} {F : X -> Type}
  (G : forall xs, HVec F xs -> Y xs -> Type)
  : forall {xs}, HVec F xs -> BList Y xs -> Type :=
  | bvnil : BVec G hvnil bnil
  | bvcons {xs} (y : Y xs) {v : HVec F xs}
      (b : BList Y xs) :
      G xs v y -> BVec G v b -> BVec G v (bcons y b)
  | bvbump {x} {xs} {v : HVec F xs} (f : F x)
      (b : BList Y xs) :
      BVec G v b -> BVec G (hvcons f v) (bump x b).

Arguments bvnil {_} {_} {_} {_}.
Arguments bvcons {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments bvbump {_} {_} {_} {_} {_} {_} {_} {_} {_}.

Axiom cheat : forall {X}, X.

(*
HVec F (x :: xs)

*)

Definition hv_tail {X} {F : X -> Type} {x} {xs} :
  HVec F (x :: xs) -> HVec F xs.
Proof.
  intro.
  dependent destruction X0.
  exact X0.
Defined.

Definition de_bump {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, HVec F xs -> Y xs -> Type} {x} {xs} {f} {fs : HVec F xs}
  {ys} : BVec G (hvcons f fs) (bump x ys) -> BVec G fs ys.
Proof.
  intro.
  dependent destruction X0.
  exact X0.
Defined.

Fixpoint bv_proj {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, HVec F xs -> Y xs -> Type}
  {xs} {fs : HVec F xs} {ys : BList Y xs}
  (bv : BVec G fs ys) (i : bindex ys) {struct i} :
  G (suff _ (bl_proj ys i))
    (hvec_suff (suff_wit _ (bl_proj ys i)) fs)
    (data _ (bl_proj ys i)).
Proof.
  destruct i eqn:?.
  - simpl.
    dependent destruction bv.
    exact g.
  - simpl.
    dependent destruction bv.
    epose proof (bv_proj X Y F G xs v ys bv b).
    destruct (bl_proj ys b).
    simpl in *.
    exact X0.
  - epose proof (bv_proj X Y F G xs (hv_tail fs) ys _ b).
    apply cheat.
    Unshelve. apply cheat.
Defined. *)

Fixpoint BVec {X} {Y : list X -> Type} {F : X -> Type}
  (G : forall xs, RHVec F xs -> Y xs -> Type) {xs} :
  RHVec F xs -> BList Y xs -> Type :=
  match
    xs as l return (RHVec F l -> BList Y l -> Type)
  with
  | [] => fun v bl =>
    RHVec (G [] v) bl
  | x :: xs' => fun v bl =>
    (RHVec (G (x :: xs') v) (fst bl) *
    BVec G (snd v) (snd bl))%type
  end.

Definition bvnil {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, RHVec F xs -> Y xs -> Type} :
  BVec G (tt : RHVec F nil) bnil := tt.

Definition bvcons {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, RHVec F xs -> Y xs -> Type}
  {xs : list X} (y : Y xs) {v : RHVec F xs}
  {b : BList Y xs} (g : G xs v y) (bv : BVec G v b)
  : BVec G v (bcons y b).
Proof.
  destruct xs.
  simpl in *.
  - constructor.
    + exact g.
    + exact bv.
  - simpl.
    destruct b.
    simpl.
    destruct v.
    simpl.
    destruct bv.
    repeat split.
    + exact g.
    + exact r0.
    + exact b0.
Defined.

Definition bv_bump {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, RHVec F xs -> Y xs -> Type}
  {x} {xs : list X} {v : RHVec F xs} (f : F x)
  (b : BList Y xs) :
  BVec G v b -> BVec G ((f, v) : RHVec F (x :: xs)) (bump x b) :=
  pair tt.

Fixpoint bv_proj {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, RHVec F xs -> Y xs -> Type}
  {xs} {fs : RHVec F xs} {ys : BList Y xs}
  (bv : BVec G fs ys) (i : bindex ys) {struct xs} :
  G (suff _ (bl_proj ys i))
    (rhv_suff (suff_wit _ (bl_proj ys i)) fs)
    (data _ (bl_proj ys i)).
Proof.
  destruct xs.
  - simpl in *.
    apply rhv_index_proj.
    exact bv.
  - simpl in *.
    destruct ys.
    simpl in *.
    destruct i.
    + simpl.
      destruct fs.
      simpl in *.
      apply rhv_index_proj.
      exact (fst bv).
    + destruct fs.
      pose proof (bv_proj
      X Y F G xs _ b (snd bv) b0).
      destruct (bl_proj b b0).
      simpl in *.
      exact X0.
Defined.



(*
Inductive BVec {X} {Y : list X -> Type} {F : X -> Type}
  (G : forall xs, HVec F xs -> Y xs -> Type)
  : forall {xs}, HVec F xs -> BList Y xs -> Type :=
  | bvnil : BVec G hvnil bnil
  | bvcons {xs} (y : Y xs) {v : HVec F xs}
      (b : BList Y xs) :
      G xs v y -> BVec G v b -> BVec G v (bcons y b)
  | bvbump {x} {xs} {v : HVec F xs} (f : F x)
      (b : BList Y xs) :
      BVec G v b -> BVec G (hvcons f v) (bump x b).

Arguments bvnil {_} {_} {_} {_}.
Arguments bvcons {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments bvbump {_} {_} {_} {_} {_} {_} {_} {_} {_}.

Axiom cheat : forall {X}, X.

(*
HVec F (x :: xs)

*)

Definition hv_tail {X} {F : X -> Type} {x} {xs} :
  HVec F (x :: xs) -> HVec F xs.
Proof.
  intro.
  dependent destruction X0.
  exact X0.
Defined.

Definition de_bump {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, HVec F xs -> Y xs -> Type} {x} {xs} {f} {fs : HVec F xs}
  {ys} : BVec G (hvcons f fs) (bump x ys) -> BVec G fs ys.
Proof.
  intro.
  dependent destruction X0.
  exact X0.
Defined.

Fixpoint bv_proj {X} {Y : list X -> Type} {F : X -> Type}
  {G : forall xs, HVec F xs -> Y xs -> Type}
  {xs} {fs : HVec F xs} {ys : BList Y xs}
  (bv : BVec G fs ys) (i : bindex ys) {struct i} :
  G (suff _ (bl_proj ys i))
    (hvec_suff (suff_wit _ (bl_proj ys i)) fs)
    (data _ (bl_proj ys i)).
Proof.
  destruct i eqn:?.
  - simpl.
    dependent destruction bv.
    exact g.
  - simpl.
    dependent destruction bv.
    epose proof (bv_proj X Y F G xs v ys bv b).
    destruct (bl_proj ys b).
    simpl in *.
    exact X0.
  - epose proof (bv_proj X Y F G xs (hv_tail fs) ys _ b).
    apply cheat.
    Unshelve. apply cheat.
Defined.
*)
