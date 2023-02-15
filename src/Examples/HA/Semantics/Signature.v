Require Import IFOL.Semantics.Signature.

Require Import IFOL.Examples.HA.Syntax.Signature.
Require Import IFOL.Examples.HA.Semantics.Sort.

Definition eval_Zero_sym : f_sym_dom eval_HA_sort Zero_arity :=
  fun _ => 0.

Definition eval_Succ_sym : f_sym_dom eval_HA_sort Succ_arity :=
  fun '(x,_) => S x.

Definition eval_Plus_sym : f_sym_dom eval_HA_sort Plus_arity :=
  fun '(x,(y,_)) => x + y.

Definition eval_Mult_sym : f_sym_dom eval_HA_sort Mult_arity :=
  fun '(x,(y,_)) => x * y.

Definition eval_HA_f_sig : f_sig_dom eval_HA_sort HA_f_sig :=
  fun s =>
    match s with
    | Zero => eval_Zero_sym
    | Succ => eval_Succ_sym
    | Plus => eval_Plus_sym
    | Mult => eval_Mult_sym
    end.

Definition eval_HA_r_sig : r_sig_dom eval_HA_sort HA_r_sig :=
  fun s =>
    match s with
    end.

Definition eval_HA_sig : sig_dom eval_HA_sort HA_sig.
Proof.
  constructor.
  - exact eval_HA_f_sig.
  - exact eval_HA_r_sig.
Defined.
