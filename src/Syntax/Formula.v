Require Import CoqFol.Util.HVec.
Require Import CoqFol.Util.Witness.

Require Import CoqFol.Syntax.Signature.
Require Import CoqFol.Syntax.Term.

Inductive NullOp :=
  | Bot
  | Top.

Inductive BinOp :=
  | Sum
  | Prod
  | Exp.

Inductive Quantifier :=
  | Sigma
  | Pi.

Inductive Formula {S} (sg : sig S) : list S -> Type :=
  | NullProp {env} : NullOp -> Formula sg env
  | BinProp {env} : BinOp ->
      Formula sg env ->
      Formula sg env ->
      Formula sg env
  | QuantifierProp {env} s : Quantifier ->
      Formula sg (s :: env) -> Formula sg env
  | EqualityProp : forall env s,
      Term (func sg) env s ->
      Term (func sg) env s ->
      Formula sg env
  | RelAppProp : forall env (r : r_symbols (rel sg)),
      HVec (Term (func sg) env) (r_args (r_arities r)) ->
      Formula sg env.

Fixpoint Formula_subst {S} {sg : sig S} {env env'} {s}
  (pw : part_witness s env' env)
  (u : Term (func sg) env' s)
  (p : Formula sg env) {struct p} :
  Formula sg env'.
Proof.
  destruct p eqn:?.
  - exact (NullProp sg n).
  - exact (BinProp sg b
    (Formula_subst S sg _ _ s pw u f1)
    (Formula_subst S sg _ _ s pw u f2)
    ).
  - eapply (QuantifierProp sg s0 q).
    eapply Formula_subst.
    + eapply pwtl. exact pw.
    + eapply (Term_weaken pwhd).
      exact u.
    + exact f.
  - eapply (EqualityProp sg _ s0).
    exact (Term_subst pw u t).
    exact (Term_subst pw u t0).
  - eapply (RelAppProp _ _ r).
    eapply hvec_map.
    2:{ exact h. }
    intro; eapply Term_subst. exact pw. exact u.
Defined.

Fixpoint Formula_weaken {S} {sg : sig S} {env env'} {s}
  (pw : part_witness s env' env) (phi : Formula sg env') : Formula sg env.
Proof.
  destruct phi eqn:?.
  - exact (NullProp sg n).
  - exact (BinProp sg b
      (Formula_weaken _ _ _ _ _ pw f1)
      (Formula_weaken _ _ _ _ _ pw f2)
    ).
  - eapply (QuantifierProp sg _ q).
    eapply Formula_weaken.
    exact (pwtl pw).
    exact f.
  - exact (EqualityProp sg _ _
      (Term_weaken pw t)
      (Term_weaken pw t0)
    ).
  - apply (RelAppProp _ _ r).
    eapply hvec_map.
    2:{ exact h. }
    intro; eapply (Term_weaken pw).
Defined.

Inductive Formula_subterm_witness {S} {sg : sig S}
  {env : list S} {s} : Term (func sg) env s -> Formula sg env -> Type :=
  | subterm_BinOp_left {t} o (p q : Formula sg env) :
      Formula_subterm_witness t p ->
      Formula_subterm_witness t (BinProp _ o p q)
  | subterm_BinOp_right {t} o (p q : Formula sg env) :
      Formula_subterm_witness t q ->
      Formula_subterm_witness t (BinProp _ o p q)
  | subterm_Quantifier {s} q (p : Formula sg (s :: env)) {t} :
      Formula_subterm_witness (Term_weaken pwhd t) p ->
      Formula_subterm_witness t (QuantifierProp _ _ q p)
  | subterm_Equality_left {u} t t' :
      subterm_witness u t ->
      Formula_subterm_witness u (EqualityProp _ _ s t t')
  | subterm_Equality_right {u} t t' :
      subterm_witness u t' ->
      Formula_subterm_witness u (EqualityProp _ _ s t t')
  | subterm_RelApp {u} r terms {s}
      (w : witness s (r_args (r_arities r))) :
      subterm_witness u (hvec_proj terms w) ->
      Formula_subterm_witness u (RelAppProp _ _  r terms).

Fixpoint Formula_subterm_subst {S} {sg : sig S} {env} {s}
  {u : Term (func sg) env s} (p : Formula sg env)
  (sw : Formula_subterm_witness u p) (t : Term (func sg) env s) : Formula sg env :=
  match sw with
  | subterm_BinOp_left o p q sw =>
      BinProp _ o (Formula_subterm_subst p sw t) q
  | subterm_BinOp_right o p q sw =>
      BinProp _ o p (Formula_subterm_subst q sw t)
  | subterm_Quantifier q p sw =>
      QuantifierProp _ _ q (Formula_subterm_subst p sw (Term_weaken pwhd t))
  | subterm_Equality_left a b sw =>
      EqualityProp _ _ _ (subterm_subst _ t a sw) b
  | subterm_Equality_right a b sw =>
      EqualityProp _ _ _ a (subterm_subst _ t b sw)
  | subterm_RelApp r terms w sw =>
      RelAppProp _ _ r
        (hvec_replace w
          (subterm_subst _ t (hvec_proj terms w) sw)
          terms
        )
  end.
