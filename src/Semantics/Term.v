Require Import Coq.Program.Equality.

Require Import CoqFol.Util.HVec.
Require Import CoqFol.Util.RHVec.
Require Import CoqFol.Util.Witness.

Require Import CoqFol.Syntax.Signature.
Require Import CoqFol.Syntax.Term.

Require Import CoqFol.Semantics.Signature.

Definition env_dom {S} (eval_S : sort_dom S) (env : list S) : Type :=
  RHVec eval_S env.

Fixpoint eval_Term {S} {f_sg : f_sig S} {env} {s}
  (eval_S : S -> Type) (eval_f_sig : f_sig_dom eval_S f_sg)
  (args : env_dom eval_S env) (t : Term f_sg env s) {struct t} : eval_S s :=
  match t with
  | var _ i => rhv_proj i args
  | f_app f terms =>
      eval_f_sig f
        (HVec_rect S (Term f_sg env)
           (fun l _ =>
            RHVec eval_S l) tt
           (fun (x : S) (xs : list S)
              (y : Term f_sg env x) _
              (IHterms : RHVec eval_S xs) =>
            pair
              (eval_Term eval_S eval_f_sig args y) IHterms) (f_args (f_arities f)) terms)
  end.

Fixpoint eval_Term_weaken {S} {f_sg} {env env'} {s s'}
  (eval_S : S -> Type) (eval_f_sig : f_sig_dom eval_S f_sg)
  (args : env_dom eval_S env') (t : Term f_sg env' s)
  (pw : part_witness s' env' env) (x : eval_S s') {struct t} :
  eval_Term eval_S eval_f_sig (rhv_insert pw x args) (Term_weaken pw t) =
  eval_Term eval_S eval_f_sig args t.
Proof.
  destruct t.
  - simpl.
    unfold env_dom in args.
    apply rhv_proj_rhv_insert_witness_weak.
  - simpl.
    f_equal.
    generalize h.
    intro h0.
    induction h0.
    + reflexivity.
    + simpl.
      f_equal.
      * apply eval_Term_weaken.
      * apply IHh0.
        exact h0.
Defined.

Fixpoint eval_Term_subst {S} {f_sg} {env env'} {s s'}
  (eval_S : S -> Type) (eval_f_sig : f_sig_dom eval_S f_sg)
  (args : env_dom eval_S env') (t : Term f_sg env s) (u : Term f_sg env' s')
  (pw : part_witness s' env' env) {struct t} :
  eval_Term eval_S eval_f_sig args (Term_subst pw u t) =
  eval_Term eval_S eval_f_sig
    (rhv_insert pw (eval_Term eval_S eval_f_sig args u) args) t.
Proof.
  destruct t.
  - simpl.
    destruct (witness_invert pw w) eqn:?.
    + destruct e.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      erewrite rhv_proj_rhv_insert_invert2.
      * reflexivity.
      * exact Heqs0.
    + simpl.
      unfold env_dom in args.
      erewrite rhv_proj_rhv_insert_invert; eauto.
  - simpl.
    f_equal.
    generalize h.
    intro h0.
    induction h0.
    + reflexivity.
    + simpl.
      f_equal.
      * apply eval_Term_subst.
      * apply IHh0.
        exact h0.
Defined.

Fixpoint eval_Term_subterm_subst {S} (eval_S : S -> Type)
  {sg : sig S} {eval_sig : sig_dom eval_S sg} {env}
  {args : env_dom eval_S env} {s s'} {u u' : Term (func sg) env s}
  {t : Term (func sg) env s'} {sw : subterm_witness u t}
  {struct sw}
  :
  eval_Term eval_S (func_dom eval_S sg eval_sig) args u =
  eval_Term eval_S (func_dom eval_S sg eval_sig) args u' ->
  eval_Term eval_S (func_dom eval_S sg eval_sig) args
    (subterm_subst u u' t sw) =
  eval_Term eval_S (func_dom eval_S sg eval_sig) args t.
Proof.
  destruct sw; intros.
  - simpl; congruence.
  - simpl.
    f_equal.
    repeat rewrite <- HVec_rect_map.
    rewrite of_hvec_replace.
    rewrite rhv_map_replace.
    rewrite eval_Term_subterm_subst; [|exact H].
    rewrite <- rhv_proj_of_hvec.
    rewrite <- (rhv_proj_map
      (fun x y => eval_Term eval_S (func_dom eval_S sg eval_sig) args y)).
    now rewrite rhv_replace_proj.
Defined.
