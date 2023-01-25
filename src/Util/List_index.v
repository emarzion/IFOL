Require Import List.
Import ListNotations.

Fixpoint list_index {X} (xs : list X) : Type :=
  match xs with
  | [] => Empty_set
  | x :: ys => unit + list_index ys
  end.

Fixpoint list_proj {X} (xs : list X) : list_index xs -> X :=
  match xs with
  | [] => fun e =>
    match e with
    end
  | x :: ys => fun i =>
    match i with
    | inl _ => x
    | inr j => list_proj ys j
    end
  end.
