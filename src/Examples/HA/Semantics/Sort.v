Require Import IFOL.Semantics.Signature.

Require Import IFOL.Examples.HA.Syntax.Sort.

Definition eval_HA_sort : sort_dom HA_sort :=
  fun s =>
    match s with
    | Nat => nat
    end.
