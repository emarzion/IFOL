Require Import IFOL.Util.RHVec.
Require Import IFOL.Util.Witness.
Require Import IFOL.Syntax.Signature.

Definition sort_dom S : Type := S -> Type.

Definition f_sym_dom {S} (eval_S : sort_dom S) (f : f_arity S) : Type :=
  RHVec eval_S (f_args f) -> eval_S (f_out f).

Definition f_sig_dom {S} (eval_S : sort_dom S) (f_sg : f_sig S) : Type :=
  forall (f : f_symbols f_sg), f_sym_dom eval_S (f_arities f).

Definition r_sym_dom {S} (eval_S : sort_dom S) (r : r_arity S) : Type :=
  RHVec eval_S (r_args r) -> Prop.

Definition r_sig_dom {S} (eval_S : sort_dom S) (r_sg : r_sig S) : Type :=
  forall (r : r_symbols r_sg), r_sym_dom eval_S (r_arities r).

Record sig_dom {S} (eval_S : sort_dom S) (sg : sig S) : Type := {
  func_dom : f_sig_dom eval_S (func sg);
  rel_dom : r_sig_dom eval_S (rel sg)
  }.
