Require Import List.
Import ListNotations.

Require Import IFOL.Syntax.Signature.

Require Import IFOL.Examples.HA.Syntax.Sort.

Inductive HA_f_symbols : Type :=
  | Zero | Succ | Plus | Mult.

Definition Zero_arity : f_arity HA_sort := {|
  f_args := [];
  f_out := Nat
  |}.

Definition Succ_arity : f_arity HA_sort := {|
  f_args := [Nat];
  f_out := Nat
  |}.

Definition Plus_arity : f_arity HA_sort := {|
  f_args := [Nat; Nat];
  f_out := Nat
  |}.

Definition Mult_arity : f_arity HA_sort := {|
  f_args := [Nat; Nat];
  f_out := Nat
  |}.

Definition HA_f_sig : f_sig HA_sort := {|
  f_symbols := HA_f_symbols;
  f_arities := fun s =>
    match s with
    | Zero => Zero_arity
    | Succ => Succ_arity
    | Plus => Plus_arity
    | Mult => Mult_arity
    end
  |}.

Definition HA_r_sig : r_sig HA_sort := {|
  r_symbols := Empty_set;
  r_arities := fun s =>
    match s with
    end
  |}.

Definition HA_sig : sig HA_sort := {|
  func := HA_f_sig;
  rel := HA_r_sig
  |}.
