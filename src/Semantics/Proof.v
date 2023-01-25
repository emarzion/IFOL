Require Import Coq.Program.Equality.

Require Import IFOL.Util.BList.
Require Import IFOL.Util.BVec.
Require Import IFOL.Util.HVec.
Require Import IFOL.Util.Witness.

Require Import IFOL.Syntax.Signature.
Require Import IFOL.Syntax.Term.
Require Import IFOL.Syntax.Formula.
Require Import IFOL.Syntax.Proof.

Require Import IFOL.Semantics.Signature.
Require Import IFOL.Semantics.Term.
Require Import IFOL.Semantics.Formula.

Definition seq_dom {S} {sg : sig S} {env}
  (eval_S : sort_dom S) (eval_sig : sig_dom eval_S sg) (args : env_dom eval_S env)
  (seq : BList (Formula sg) env) : Type :=
  BVec (eval_Formula eval_S sg eval_sig) args seq.

Fixpoint eval_Proof {S} eval_S {sg : sig S} {env}
  {seq : BList (Formula sg) env} eval_sig args {phi}
  (eval_seq : seq_dom eval_S eval_sig args seq)
  (pf : Proof seq phi) :
  eval_Formula eval_S sg eval_sig env args phi.
Proof.
  destruct pf eqn:?.
  - unfold seq_dom in eval_seq.
    pose proof (bv_proj eval_seq i).
    unfold proj_with_weakenings.
    destruct (bl_proj seq i).
    simpl in *.
    apply eval_Formula_suff_weaken.
    exact H.
  - destruct (
      eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p).
  - exact I.
  - left.
    exact (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p).
  - right.
    exact (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p).
  - simpl in p1.
    destruct (
      eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p1).
    + pose (eval_seq' :=
      bvcons _ H eval_seq).
      exact (eval_Proof S eval_S sg env _ eval_sig args _ eval_seq' p2).
    + pose (eval_seq' :=
      bvcons _ H eval_seq).
      exact (eval_Proof S eval_S sg env _ eval_sig args _ eval_seq' p3).
  - exact (conj
      (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p1)
      (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p2)
    ).
  - exact (proj1
      (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p)
    ).
  - exact (proj2
      (eval_Proof S eval_S sg env seq eval_sig args _ eval_seq p)
    ).
  - intro q.
    pose (eval_seq' :=
      bvcons _ q eval_seq).
    exact (eval_Proof S eval_S sg env _ eval_sig args _ eval_seq' p).
  - simpl.
    apply (eval_Proof S eval_S sg env _ eval_sig args _ eval_seq p1).
    exact (eval_Proof S eval_S sg env _ eval_sig args _ eval_seq p2).
  - simpl.
    intro.
    exact (eval_Proof S eval_S sg (cons s env) _ eval_sig (x, args) _
      (bv_bump _ _ eval_seq) p).
  - epose (eval_Proof S eval_S sg _ _ eval_sig args _ eval_seq p).
    simpl in e.
    epose (eval_Term eval_S (func_dom _ _ eval_sig) args t).
    pose (e e0).
    unfold e0 in e1.
    rewrite eval_Formula_subst.
    exact e1.
  - exists (eval_Term eval_S (func_dom _ _ eval_sig) args t).
    epose (eval_Proof S eval_S sg _ _ eval_sig args _ eval_seq p).
    rewrite eval_Formula_subst in e.
    exact e.
  - destruct (eval_Proof S eval_S sg _ _ eval_sig args _ eval_seq p1)
      as [x pf_x].
    epose proof (eval_Proof S eval_S sg (cons s env) (bcons phi (bump s seq)) eval_sig (x, args) _
      (pf_x, tt, eval_seq) p2).
    eapply eval_Formula_weaken; exact H.
  - reflexivity.
  - pose (eval_Proof S eval_S sg _ _ eval_sig args _ eval_seq p1).
    pose (eval_Proof S eval_S sg _ _ eval_sig args _ eval_seq p2).
    simpl in e0.
    now rewrite eval_Formula_subterm_subst in e.
Defined.

Print Assumptions eval_Proof.
