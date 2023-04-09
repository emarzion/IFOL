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

Definition plus_commutes_aux :
  Formula HA_sig (Nat :: nil).
Proof.
  apply (QuantifierProp _ Nat Pi).
  apply (EqualityProp _ _ Nat).
  - apply (@f_app _ HA_f_sig _ Plus).
    + apply hvcons.
      * exact (var _ (wtl whd)).
      * apply hvcons.
        ** exact (var _ whd).
        ** exact hvnil.
  - apply (@f_app _ HA_f_sig _ Plus).
    + apply hvcons.
      * exact (var _ whd).
      * apply hvcons.
        ** exact (var _ (wtl whd)).
        ** exact hvnil.
Defined.

Definition plus_commutes :
  Formula HA_sig nil.
Proof.
  apply (QuantifierProp _ Nat Pi).
  exact plus_commutes_aux.
Defined.

Lemma plus_commutes_pf :
  @Proof _ _ HA_theory nil nil plus_commutes.
Proof.
  apply Pi_intro.
  pose proof (@Ax _ _ HA_theory
    (Induction plus_commutes_aux)
    (Nat :: nil)
    (BList.bump Nat (nil : BList.BList _ nil))
  ) as ind_pf.
  simpl in *.
  apply 
  simpl suff_weaken in ind_pf.
  simpl in *.

Admitted.

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
    simpl in pi_zplus.
    unfold suff_weaken in pi_zplus.
    simpl in pi_zplus.
    exact (Pi_elim _ _ _ pi_zplus Z).
  }
  pose proof
    (Exp_elim HA_theory _ _ ind_pf P0) as p.
  simpl in p.
  eapply Exp_elim.
  exact p.
  simpl.
  apply Pi_intro.
  simpl.
  apply Exp_intro.
  simpl.
  assert
    (@Proof _ _ HA_theory (Nat :: nil)%list
 ((all_even_or_odd_aux :: nil)%list, nil)
    all_even_or_odd_aux).
pose (i := (inl (inl tt) : (@BList.bindex _ _ (Nat :: nil)%list
((all_even_or_odd_aux :: nil)%list, nil)
))).
  exact (Assumption
    HA_theory i
  ).
  apply (Sigma_elim _ _ _ _ X).
  simpl.
  pose ((inl (inl tt)) : (@BList.bindex _ _ (Nat :: Nat :: nil)%list
((BinProp HA_sig Sum
      (EqualityProp HA_sig (Nat :: Nat :: nil) Nat
         (@f_app HA_sort HA_f_sig _ Plus
            (hvcons (var Nat whd)
               (hvcons (var Nat whd) hvnil)))
         (var Nat (wtl whd)))
      (EqualityProp HA_sig (Nat :: Nat :: nil) Nat
         (@f_app HA_sort HA_f_sig _ Succ
            (hvcons
               (@f_app HA_sort HA_f_sig _ Plus
                  (hvcons (var Nat whd)
                     (hvcons (var Nat whd) hvnil)))
               hvnil)) (var Nat (wtl whd))) :: nil)%list,
   ((all_even_or_odd_aux :: nil)%list, nil))
  )) as i.
  pose proof (Assumption HA_theory i).
  apply (Sum_elim _ _ _ _ X0).
  + clear X0 i p P0 ind_pf.
    simpl.
    apply (Sigma_intro
      HA_theory Nat _ (var Nat whd)).
    apply Sum_intro_r.
    simpl.
    unfold eq_rect_r.
    unfold eq_rect.
    simpl.
    pose (inl eq_refl : witness Nat (Signature.f_args
      (@Signature.f_arities _ HA_f_sig Succ))).
    unshelve epose (_ : (Formula_subterm_witness 
(@f_app _ (Signature.func HA_sig) _ Plus
                          (hvcons 
                             (var Nat whd)
                             (hvcons
                                (var Nat whd)
                                hvnil)))
  (EqualityProp HA_sig
                 (Nat :: Nat :: nil) Nat
                 (@f_app _ HA_f_sig _ Succ
                    (hvcons
                       (@f_app _ HA_f_sig _ Plus
                          (hvcons 
                             (var Nat whd)
                             (hvcons
                                (var Nat whd)
                                hvnil))) hvnil))
                 (@f_app _ HA_f_sig _ Succ
                    (hvcons
                       (var Nat
                         (wtl whd))
                       hvnil))))
    ).
    { apply subterm_Equality_left.
      apply (subterm_app w).
      apply subterm_refl.
    }
    eapply (Eq_elim _ _ _ _ f).
    * apply Eq_intro.
    * simpl.
      unshelve epose (_ : BList.BList (Formula HA_sig) (Nat :: Nat :: nil)).
      { exact
        ((EqualityProp HA_sig
      (Nat :: Nat :: nil) Nat
      (@f_app _ HA_f_sig _ Plus
         (hvcons (var Nat whd)
            (hvcons (var Nat whd) hvnil)))
      (var Nat (wtl whd))
    :: BinProp HA_sig Sum
         (EqualityProp HA_sig
            (Nat :: Nat :: nil) Nat
            (@f_app _ HA_f_sig _ Plus
               (hvcons (var Nat whd)
                  (hvcons (var Nat whd)
                     hvnil)))
            (var Nat (wtl whd)))
         (EqualityProp HA_sig
            (Nat :: Nat :: nil) Nat
            (@f_app _ HA_f_sig _ Succ
               (hvcons
                  (@f_app _ HA_f_sig _ Plus
                     (hvcons
                        (var Nat whd)
                        (hvcons
                          (var Nat whd)
                          hvnil))) hvnil))
            (var Nat (wtl whd))) :: nil)%list,
   ((all_even_or_odd_aux :: nil)%list,
    nil)). }
    pose (i := inl (inl tt) : BList.bindex b).
    exact (Assumption HA_theory i).
  + clear X0 i p P0 ind_pf.
    simpl.
    apply (Sigma_intro
      HA_theory Nat _
      (@f_app HA_sort HA_f_sig _ Succ
        (hvcons (var Nat whd) hvnil)
      )).
    apply Sum_intro_l.
    simpl.
    unfold eq_rect_r.
    unfold eq_rect.
    simpl.
    unshelve epose (_ : Formula_subterm_witness
      (@f_app _ (Signature.func HA_sig) _ Plus
        (hvcons _
          (hvcons _ hvnil)))
(EqualityProp HA_sig
     (Nat :: Nat :: nil) Nat
     (@f_app _ HA_f_sig _ Plus
        (hvcons
           (@f_app _ HA_f_sig _ Succ
              (hvcons (var Nat whd)
                 hvnil))
           (hvcons
              (@f_app _ HA_f_sig _ Succ
                 (hvcons (var Nat whd)
                    hvnil)) hvnil)))
     (@f_app _ HA_f_sig _ Succ 
        (hvcons
           (var Nat (wtl whd))
           hvnil)))).
    3:{ apply subterm_Equality_left.
        apply subterm_refl.
      }
    eapply (Eq_elim _ _ _ _ f).
    2:{ epose (sp :=
      @Ax _ _ HA_theory Succ_Plus (Nat :: Nat :: nil) _).
    simpl in sp.
    unfold Succ_Plus_formula in sp.
    simpl in sp.
    pose (sp1 := Pi_elim _ _ _ sp (var Nat whd)).
    pose (sp2 := Pi_elim _ _ _ sp1 (var Nat (wtl whd))).
    simpl in sp2.
    unfold eq_rect_r in sp2.
    unfold eq_rect in sp2.
    simpl in sp2.
    exact sp2.
q 
  }
  admit.
Admitted.
