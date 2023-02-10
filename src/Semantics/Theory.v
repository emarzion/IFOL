Require Import IFOL.Syntax.Signature.
Require Import IFOL.Syntax.Theory.

Require Import IFOL.Semantics.Signature.
Require Import IFOL.Semantics.Formula.

Definition theory_dom {S} (eval_S : sort_dom S) (sg : sig S)
  (eval_sig : sig_dom eval_S sg) (th : Theory sg) : Type :=
  forall i : carrier sg th, eval_Formula eval_S sg eval_sig nil tt
    (formula sg th i).
