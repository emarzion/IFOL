Require Import IFOL.Syntax.Signature.
Require Import IFOL.Syntax.Formula.

Record Theory {S} (sg : sig S) : Type := {
  carrier : Type;
  formula : carrier -> Formula sg nil
  }.
