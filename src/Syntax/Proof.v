Require Import IFOL.Util.BList.
Require Import IFOL.Util.Witness.

Require Import IFOL.Syntax.Signature.
Require Import IFOL.Syntax.Term.
Require Import IFOL.Syntax.Formula.

Lemma foo {S} {sg : sig S} :
  forall x env, Formula sg env -> Formula sg (x :: env).
  intros.
  eapply Formula_weaken.
  - exact pwhd.
  - exact X.
Defined.

Fixpoint suff_weaken {S} {sg : sig S} {env suff}
  (suff_wit : suffix_wit suff env) : Formula sg suff -> Formula sg env.
Proof.
  destruct suff_wit.
  - exact (fun x => x).
  - intro f.
    epose (suff_weaken S sg ys xs suff_wit f).
    exact (Formula_weaken pwhd f0).
Defined.

Definition proj_with_weakenings {S} {sg : sig S} {env}
  (seq : BList (Formula sg) env) (i : bindex seq) : Formula sg env.
Proof.
  epose (bl_proj seq i).
  eapply suff_weaken.
  exact (suff_wit _ b).
  exact (data _ b).
Defined.

Inductive Proof {S} {sg : sig S} : forall {env},
  BList (Formula sg) env -> Formula sg env -> Type :=
  | Assumption {env} {seq : BList (Formula sg) env}
      (i : bindex seq)
      : Proof seq (proj_with_weakenings seq i)
  | Bot_elim {env} {seq : BList (Formula sg) env} phi :
      Proof seq (NullProp _ Bot) -> Proof seq phi
  | Top_intro {env} {seq : BList (Formula sg) env} :
      Proof seq (NullProp _ Top)
  | Sum_intro_l {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq phi -> Proof seq (BinProp _ Sum phi psi)
  | Sum_intro_r {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq psi -> Proof seq (BinProp _ Sum phi psi)
  | Sum_elim {env} {seq : BList (Formula sg) env} phi psi rho :
      Proof seq (BinProp _ Sum phi psi) ->
      Proof (bcons phi seq) rho -> Proof (bcons psi seq) rho ->
      Proof seq rho
  | Prod_intro {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq phi -> Proof seq psi ->
      Proof seq (BinProp _ Prod phi psi)
  | Prod_elim_l {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq (BinProp _ Prod phi psi) ->
      Proof seq phi
  | Prod_elim_r {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq (BinProp _ Prod phi psi) ->
      Proof seq psi
  | Exp_intro {env} {seq : BList (Formula sg) env} phi psi :
      Proof (bcons phi seq) psi ->
      Proof seq (BinProp _ Exp phi psi)
  | Exp_elim {env} {seq : BList (Formula sg) env} phi psi :
      Proof seq (BinProp _ Exp phi psi) ->
      Proof seq phi ->
      Proof seq psi
  | Pi_intro {env} {seq} s
      (phi : Formula sg (s :: env)) :
      Proof (bump s seq) phi -> Proof seq (QuantifierProp _ _ Pi phi)
  | Pi_elim {env} {seq} s
      (phi : Formula sg (s :: env)) :
      Proof seq (QuantifierProp _ _ Pi phi) ->
      forall (t : Term (func sg) env s),
      Proof seq (Formula_subst pwhd t phi)
  | Sigma_intro {env} {seq} s
      (phi : Formula sg (s :: env))
      (t : Term (func sg) env s) :
      Proof seq (Formula_subst pwhd t phi) ->
      Proof seq (QuantifierProp _ _ Sigma phi)
  | Sigma_elim {env} {seq} s
      (phi : Formula sg (s :: env)) psi :
      Proof seq (QuantifierProp _ _ Sigma phi) ->
      Proof (bcons phi (bump s seq)) (Formula_weaken pwhd psi) ->
      Proof seq psi
  | Eq_intro {env} {seq} {s}
      (t : Term (func sg) env s) :
      Proof seq (EqualityProp _ _ _ t t)
  | Eq_elim {env} {seq} {s} phi
      (t u : Term (func sg) env s)
      (fw : Formula_subterm_witness t phi) :
      Proof seq (Formula_subterm_subst phi fw u) ->
      Proof seq (EqualityProp _ _ _ t u) ->
      Proof seq phi.
