Require Import IFOL.Util.HVec.
Require Import IFOL.Util.Witness.

Require Import IFOL.Syntax.Signature.

Inductive Term {S} (f_sg : f_sig S) (env : list S) : S -> Type :=
  | var (s : S) :
      witness s env ->
      Term f_sg env s
  | f_app (f : f_symbols f_sg) :
      HVec (Term f_sg env) (f_args (f_arities f)) ->
      Term f_sg env (f_out (f_arities f)).

Arguments var {_} {_} {_} _ _.
Arguments f_app {_} {_} {_} _ _.

Fixpoint Term_weaken {S} {f_sg : f_sig S} {env env'} {s s'}
  (pw : part_witness s' env' env)
  (t : Term f_sg env' s) {struct t} :
  Term f_sg env s :=
  match t with
  | var s w => var s (witness_weak pw w)
  | f_app f terms => f_app f
      (HVec_rect _ _ _ hvnil
      (fun x xs y _
               (acc : 
                HVec
                (Term f_sg
                env) xs)
             =>
             hvcons
               (Term_weaken
                 pw y)
               acc) (f_args (f_arities f)) terms)
  end.

Fixpoint Term_subst {S} {f_sg : f_sig S} {s'} {env env'} {s}
  (pw : part_witness s' env' env)
  (u : Term f_sg env' s')
  (t : Term f_sg env s) {struct t} :
  Term f_sg env' s.
Proof.
  destruct t.
  - destruct (witness_invert pw w).
    + rewrite e.
      exact u.
    + apply var. exact w0.
  - apply (f_app f).
    induction h.
    + apply hvnil.
    + apply hvcons.
      * exact (Term_subst S f_sg _ _ _ _ pw u y).
      * exact IHh.
Defined.

Inductive subterm_witness {S} {f_sg : f_sig S}
  {env : list S} : forall {s s'}, Term f_sg env s -> Term f_sg env s' -> Type :=
  | subterm_refl {s} (t : Term f_sg env s) : subterm_witness t t
  | subterm_app {s s'} {f : f_symbols f_sg}
      {terms : HVec (Term f_sg env) (f_args (f_arities f)) }
      {u : Term f_sg env s'}
      (w : witness s (f_args (f_arities f))) :
      subterm_witness u (hvec_proj terms w) ->
      subterm_witness u (f_app f terms).

Fixpoint subterm_subst {S} {f_sg : f_sig S} {env} {s s'}
  (u u' : Term f_sg env s) (t : Term f_sg env s')
  (sw : subterm_witness u t) : Term f_sg env s'.
Proof.
  destruct sw.
  - exact u'.
  - pose (t :=
      subterm_subst _ _ _ _ _
      u u' (hvec_proj terms w) sw).
    apply (f_app f).
    exact (hvec_replace w t terms).
Defined.

Fixpoint Term_var_subst {S} {f_sg : f_sig S} {env} {s s'}
  (u : Term f_sg env s') (t : Term f_sg env s)
  (w : witness s' env) : Term f_sg env s.
Proof.
  destruct t.
  - destruct (PeanoNat.Nat.eq_dec
      (nat_of_wit w0)
      (nat_of_wit w)).
    + assert (s = s').
      { destruct (heq_of_nat_eq _ _ e).
        exact x.
      }
      destruct H.
      exact u.
    + exact (var s w0).
  - apply (f_app f).
    induction h.
    + exact hvnil.
    + apply hvcons.
      * exact (Term_var_subst S _ _ _ _ u y w).
      * exact IHh.
Defined.
