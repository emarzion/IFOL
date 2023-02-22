Require Import IFOL.Util.Witness.
Require Import IFOL.Util.HVec.

Require Import IFOL.Syntax.Term.
Require Import IFOL.Syntax.Formula.
Require Import IFOL.Syntax.Proof.

Require Import IFOL.Semantics.Formula.

Require Import IFOL.Examples.HA.Syntax.Sort.
Require Import IFOL.Examples.HA.Syntax.Signature.
Require Import IFOL.Examples.HA.Syntax.Theory.

Require Import IFOL.Examples.HA.Semantics.Sort.
Require Import IFOL.Examples.HA.Semantics.Signature.
Require Import IFOL.Examples.HA.Semantics.Theory.

Definition all_even_or_odd_aux :
  Formula HA_sig (Nat :: nil).
Proof.
  apply (QuantifierProp _ Nat Sigma).
  apply (BinProp _ Sum).
  - apply (EqualityProp _ _ Nat).
    + apply (@f_app HA_sort HA_f_sig _ Plus).
      apply hvcons.
      * apply var.
        exact whd.
      * apply hvcons.
        ** apply var.
           exact whd.
        ** exact hvnil.
    + apply var.
      apply wtl.
      exact whd.
  - apply (EqualityProp _ _ Nat).
    + apply (@f_app HA_sort HA_f_sig _ Succ).
      apply hvcons; [|exact hvnil].
      apply (@f_app HA_sort HA_f_sig _ Plus).
      apply hvcons.
      * apply var.
        exact whd.
      * apply hvcons.
        ** apply var.
           exact whd.
        ** exact hvnil.
    + apply var.
      apply wtl.
      exact whd.
Defined.

Definition all_even_or_odd : Formula HA_sig nil.
Proof.
  apply (QuantifierProp _ Nat Pi).
  exact all_even_or_odd_aux.
Defined.

Definition all_even_or_odd_pf
 : @Proof _ _ HA_theory nil nil all_even_or_odd.
Proof.
  pose (@Ax _ _ HA_theory
    (Induction all_even_or_odd_aux)
    nil nil) as ind_pf.
  simpl in ind_pf.
  unfold Induction_formula in ind_pf.
  Set Printing All.
  assert (
@Proof HA_sort HA_sig HA_theory 
     (@nil HA_sort)
     (@nil (@Formula HA_sort HA_sig (@nil HA_sort)))
    (@Formula_subst HA_sort HA_sig
           (@cons HA_sort Nat (@nil HA_sort))
           (@nil HA_sort) Nat
           (@pwhd HA_sort Nat (@nil HA_sort))
           (@f_app HA_sort HA_f_sig 
              (@nil HA_sort) Zero
              (@hvnil HA_sort
                 (@Term HA_sort HA_f_sig
                    (@nil HA_sort))))
           all_even_or_odd_aux)) as P0.
  { simpl.
    unfold eq_rect_r.
    unfold eq_rect.
    simpl.
    pose (Z :=
      (@f_app HA_sort HA_f_sig nil Zero hvnil)).
    apply (Sigma_intro HA_theory Nat _ Z).
    simpl.
    unfold eq_rect_r.
    unfold eq_rect.
    simpl.
    apply Sum_intro_l.
    pose (@Ax _ _ HA_theory Zero_Plus nil nil)
      as pi_zplus.
    simpl in pi_zplus.
    unfold Zero_Plus_formula in pi_zplus.
    epose Pi_elim.
    simpl in pi_zplus.
    unfold suff_weaken in pi_zplus.
    simpl in pi_zplus.
    exact (Pi_elim _ _ _ pi_zplus Z).
  }
  epose proof
    (Exp_elim HA_theory _ _ ind_pf P0) as p.
  simpl in p.
  admit.
Admitted.
