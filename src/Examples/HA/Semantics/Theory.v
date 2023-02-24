Require Import Lia.

Require Import IFOL.Semantics.Signature.
Require Import IFOL.Semantics.Theory.

Require Import IFOL.Examples.HA.Syntax.Signature.
Require Import IFOL.Examples.HA.Syntax.Theory.
Require Import IFOL.Examples.HA.Semantics.Signature.
Require Import IFOL.Examples.HA.Semantics.Sort.

Definition eval_HA_theory :
  theory_dom eval_HA_sort HA_sig eval_HA_sig HA_theory.
Proof.
  intro ax.
  destruct ax.
  - exact PeanoNat.Nat.neq_0_succ.
  - exact eq_add_S.
  - exact plus_O_n.
  - exact PeanoNat.Nat.add_succ_l.
  - exact PeanoNat.Nat.mul_0_l.
  - exact PeanoNat.Nat.mul_succ_l.
  - simpl.
    rewrite Formula.eval_Formula_subst.
    simpl.
    intros.
    induction x.
    + exact H.
    + pose proof (H0 x IHx) as G.
      rewrite Formula.eval_Formula_var_subst in G.
      exact G.
Defined.

Print Assumptions eval_HA_theory.

Require Import IFOL.Syntax.Formula.
Require Import IFOL.Syntax.Proof.
Require Import IFOL.Semantics.Proof.

Lemma HA_con : @Proof _ HA_sig HA_theory nil nil
  (NullProp _ Bot) -> False.
Proof.
  intro pf.
  pose (@eval_Proof
    _
    eval_HA_sort
    _
    nil
    _
    nil
    eval_HA_sig
    tt
    _
    eval_HA_theory
    tt
    pf
  ).
  simpl in e.
  exact e.
Qed.

Print NullOp.
