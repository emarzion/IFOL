Require Import List.
Import ListNotations.

Require Import IFOL.Util.HVec.
Require Import IFOL.Util.Witness.

Require Import IFOL.Syntax.Term.
Require Import IFOL.Syntax.Formula.
Require Import IFOL.Syntax.Theory.

Require Import IFOL.Examples.HA.Syntax.Sort.
Require Import IFOL.Examples.HA.Syntax.Signature.

Inductive HA_axioms :=
  | Zero_Succ_dist
  | Succ_inj
  | Zero_Plus
  | Succ_Plus
  | Zero_Mult
  | Succ_Mult
  | Induction (P : Formula HA_sig [Nat]).

(* forall x, 0 = S x -> False *)
Definition Zero_Succ_dist_formula : Formula HA_sig nil.
Proof.
  apply (QuantifierProp _ Nat Pi).
  apply (BinProp _ Exp).
  - apply (EqualityProp _ _ Nat).
    + exact (@f_app HA_sort HA_f_sig [Nat] Zero hvnil).
    + apply (@f_app HA_sort HA_f_sig [Nat] Succ).
      apply hvcons.
      * apply var.
        apply whd.
      * apply hvnil.
  - apply NullProp.
    exact Bot.
Defined.

(* forall x y, S x = S y -> x = y *)
Definition Succ_inj_formula : Formula HA_sig nil.
Proof.
  do 2 apply (QuantifierProp _ Nat Pi).
  apply (BinProp _ Exp).
  - apply (EqualityProp _ _ Nat).
    + apply (@f_app HA_sort HA_f_sig _ Succ).
      simpl.
      apply hvcons.
      * apply var.
        apply wtl.
        apply whd.
      * apply hvnil.
    + apply (@f_app HA_sort HA_f_sig _ Succ).
      apply hvcons.
      * apply var.
        apply whd.
      * apply hvnil.
  - apply (EqualityProp _ _ Nat).
    + apply var.
      apply wtl.
      apply whd.
    + apply var.
      apply whd.
Defined.

(* forall x, 0 + x = x *)
Definition Zero_Plus_formula : Formula HA_sig nil.
Proof.
  apply (QuantifierProp _ Nat Pi).
  apply (EqualityProp _ _ Nat).
  - apply (@f_app HA_sort HA_f_sig _ Plus).
    apply hvcons.
    + apply (@f_app HA_sort HA_f_sig _ Zero).
      exact hvnil.
    + apply hvcons.
      * apply var.
        apply whd.
      * exact hvnil.
  - apply var.
    apply whd.
Defined.

(* forall x y, S x + y = S (x + y) *)
Definition Succ_Plus_formula : Formula HA_sig nil.
Proof.
  do 2 apply (QuantifierProp _ Nat Pi).
  apply (EqualityProp _ _ Nat).
  - apply (@f_app HA_sort HA_f_sig _ Plus).
    apply hvcons.
    + apply (@f_app HA_sort HA_f_sig _ Succ).
      apply hvcons.
      * apply var.
        apply wtl.
        apply whd.
      * apply hvnil.
    + apply hvcons.
      * apply var.
        apply whd.
      * apply hvnil.
  - apply (@f_app HA_sort HA_f_sig _ Succ).
    apply hvcons.
    + apply (@f_app HA_sort HA_f_sig _ Plus).
      apply hvcons.
      * apply var.
        apply wtl.
        apply whd.
      * apply hvcons.
        ** apply var.
           apply whd.
        ** apply hvnil.
    + apply hvnil.
Defined.

(* forall x, 0 * x = 0 *)
Definition Zero_Mult_formula : Formula HA_sig nil.
Proof.
  apply (QuantifierProp _ Nat Pi).
  apply (EqualityProp _ _ Nat).
  - apply (@f_app HA_sort HA_f_sig _ Mult).
    apply hvcons.
    + apply (@f_app HA_sort HA_f_sig _ Zero).
      apply hvnil.
    + apply hvcons.
      * apply var.
        apply whd.
      * apply hvnil.
  - apply (@f_app HA_sort HA_f_sig _ Zero).
    apply hvnil.
Defined.

(* forall x y, S x * y = x * y + y *)
Definition Succ_Mult_formula : Formula HA_sig nil.
Proof.
  do 2 apply (QuantifierProp _ Nat Pi).
  apply (EqualityProp _ _ Nat).
  - apply (@f_app HA_sort HA_f_sig _ Mult).
    apply hvcons.
    + apply (@f_app HA_sort HA_f_sig _ Succ).
      apply hvcons.
      * apply var.
        apply wtl.
        apply whd.
      * apply hvnil.
    + apply hvcons.
      * apply var.
        apply whd.
      * apply hvnil.
  - apply (@f_app HA_sort HA_f_sig _ Plus).
    + apply hvcons.
      * apply (@f_app HA_sort HA_f_sig _ Mult).
        apply hvcons.
        ** apply var.
           apply wtl.
           apply whd.
        ** apply hvcons.
           *** apply var.
               apply whd.
           *** apply hvnil.
      * apply hvcons.
        ** apply var.
           apply whd.
        ** apply hvnil.
Defined.

(*
P 0 -> (forall x, P x -> P (S x)) -> forall x, P x
*)
Definition Induction_formula (P : Formula HA_sig [Nat]) : Formula HA_sig nil.
Proof.
  apply (BinProp _ Exp).
  - apply (Formula_subst (@pwhd _ Nat _)).
    + apply (@f_app HA_sort HA_f_sig _ Zero).
      apply hvnil.
    + exact P.
  - apply (BinProp _ Exp).
    + apply (QuantifierProp _ Nat Pi).
      apply (BinProp _ Exp).
      * exact P.
      * assert (Term (Signature.func HA_sig) [Nat] Nat) as Sx.
        { apply (@f_app HA_sort HA_f_sig _ Succ).
          apply hvcons.
          - apply var.
            apply whd.
          - apply hvnil.
        }
        eapply Formula_var_subst.
        ** exact Sx.
        ** exact P.
        ** exact whd.
    + apply (QuantifierProp _ Nat Pi).
      exact P.
Defined.

Definition HA_theory : Theory HA_sig := {|
  carrier := HA_axioms;
  formula := fun i =>
    match i with
    | Zero_Succ_dist => Zero_Succ_dist_formula
    | Succ_inj => Succ_inj_formula
    | Zero_Plus => Zero_Plus_formula
    | Succ_Plus => Succ_Plus_formula
    | Zero_Mult => Zero_Mult_formula
    | Succ_Mult => Succ_Mult_formula
    | Induction P => Induction_formula P
    end
  |}.
