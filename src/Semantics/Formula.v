Require Import Coq.Program.Equality.

Require Import CoqFol.Util.RHVec.
Require Import CoqFol.Util.Witness.

Require Import CoqFol.Syntax.Signature.
Require Import CoqFol.Syntax.Term.
Require Import CoqFol.Syntax.Formula.

Require Import CoqFol.Semantics.Signature.
Require Import CoqFol.Semantics.Term.

Definition eval_NullOp (o : NullOp) : Prop :=
  match o with
  | Bot => False
  | Top => True
  end.
 
Definition eval_BinOp (o : BinOp) : Prop -> Prop -> Prop :=
  match o with
  | Sum => or
  | Prod => and
  | Exp => fun P Q => P -> Q
  end.

Definition eval_Quantifier (q : Quantifier) :
  forall {X}, (X -> Prop) -> Prop :=
  match q with
  | Sigma => ex
  | P => fun X P => forall x : X, P x
  end.

Fixpoint eval_Formula {S} (eval_S : sort_dom S)
  (sg : sig S)
  (eval_sig : sig_dom eval_S sg)
  (env : list S)
  (args : env_dom eval_S env)
  (p : Formula sg env) {struct p} : Prop.
Proof.
  destruct p.
  - exact (eval_NullOp n).
  - exact (eval_BinOp b
      (eval_Formula S eval_S sg eval_sig env args p1)
      (eval_Formula S eval_S sg eval_sig env args p2)
    ).
  - eapply (eval_Quantifier q).
    exact (fun x =>
      eval_Formula S eval_S sg eval_sig (cons s env) (x, args) p).
  - exact (eval_Term eval_S (func_dom eval_S _ eval_sig)
      args t =
    eval_Term eval_S (func_dom eval_S _ eval_sig)
      args t0).
  - apply (rel_dom eval_S _ eval_sig r).
    apply (rhv_map (fun x => eval_Term eval_S (func_dom eval_S _ eval_sig) args
    )).
    exact (of_hvec h).
Defined.

(*
Axiom cheat : forall {X},X.
*)

Lemma rel_equal {X} (P : X -> Prop) :
  forall x y : X, x = y -> P x <-> P y.
Proof.
  intros.
  rewrite H.
  tauto.
Defined.

(* TODO: complete this*)
Fixpoint eval_Formula_subst {S} (eval_S : S -> Type)
  (sg : sig S)
  (eval_sig : sig_dom eval_S sg)
  (env env' : list S)
  (args : env_dom eval_S env')
  (s : S)
  (pw : part_witness s env' env)
  (phi : Formula sg env)
  (t : Term (func sg) env' s) :
  eval_Formula eval_S sg eval_sig env' args
    (Formula_subst pw t phi) <->
  eval_Formula eval_S sg eval_sig env
    (rhv_insert pw
      (eval_Term eval_S (func_dom eval_S _ eval_sig) args t) args) phi.
Proof.
  destruct phi.
  - reflexivity.
  - simpl; split; intro.
    + destruct b; simpl in *;
      repeat rewrite eval_Formula_subst in H;
      exact H.
    + destruct b; simpl in *;
      repeat rewrite eval_Formula_subst;
      exact H.
  - destruct q; simpl.
    + split.
      * intros [x Hx].
        exists x.
        rewrite eval_Formula_subst in Hx.
        simpl in Hx.
        unfold solution_left in Hx.
        unfold eq_rect_r in Hx.
        unfold block in Hx.
        unfold eq_rect in Hx.
        unfold eq_sym in Hx.
        erewrite <- (eval_Term_weaken eval_S
          (func_dom eval_S sg eval_sig) args t pwhd _
        ).
        exact Hx.
      * intros [x Hx].
        exists x.
        rewrite eval_Formula_subst.
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        unfold block.
        unfold eq_rect.
        unfold eq_sym.
        erewrite <- (eval_Term_weaken eval_S
          (func_dom eval_S sg eval_sig) args t pwhd _
        ) in Hx.
        exact Hx.
    + split.
      * intros H x.
        pose (H x) as Hx.
        simpl in Hx.
        rewrite eval_Formula_subst in Hx.
        simpl in Hx.
        unfold solution_left in Hx.
        unfold eq_rect_r in Hx.
        unfold block in Hx.
        unfold eq_rect in Hx.
        unfold eq_sym in Hx.
        erewrite <- (eval_Term_weaken eval_S
          (func_dom eval_S sg eval_sig) args t pwhd _
        ).
        exact Hx.
      * intros H x.
        pose (H x) as Hx.
        simpl in Hx.
        rewrite eval_Formula_subst.
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        unfold block.
        unfold eq_rect.
        unfold eq_sym.
        erewrite <- (eval_Term_weaken eval_S
          (func_dom eval_S sg eval_sig) args t pwhd _
        ) in Hx.
        exact Hx.
  - simpl.
    split; intro.
    + simpl in H.
      repeat rewrite eval_Term_subst in H.
      exact H.
    + repeat rewrite eval_Term_subst.
      exact H.
  - simpl.
    apply rel_equal.
    induction h.
    + reflexivity.
    + simpl; f_equal.
      * rewrite eval_Term_subst.
        reflexivity.
      * exact IHh.
Defined.

Fixpoint eval_Formula_weaken {S} (eval_S : S -> Type)
  (sg : sig S)
  (eval_sig : sig_dom eval_S sg)
  (env env' : list S)
  (args : env_dom eval_S env')
  (s : S)
  (pw : part_witness s env' env)
  (phi : Formula sg env')
  (x : eval_S s) {struct phi} :
  eval_Formula eval_S sg eval_sig env
    (rhv_insert pw x args)
    (Formula_weaken pw phi) <->
  eval_Formula eval_S sg eval_sig env' args phi.
Proof.
  destruct phi.
  - simpl. reflexivity.
  - simpl.
    destruct b; simpl; repeat rewrite eval_Formula_weaken; tauto.
  - destruct q.
    + split; intros [a Ha]; simpl in *.
      * exists a.
        eapply eval_Formula_weaken.
        exact Ha.
      * exists a.
        epose (eval_Formula_weaken S eval_S sg eval_sig _ (cons s0 env0) (a, args) _ (pwtl pw) phi x).
        apply i.
        exact Ha.
    + split; simpl in *; intros H y.
      * pose proof (Hy := H y).
        rewrite <- eval_Formula_weaken.
        exact Hy.
      * pose proof (Hy := H y).
        assert ((y, (rhv_insert pw x args)) =
          rhv_insert (pwtl pw) x (y, args)) by reflexivity.
        simpl.
        unfold env_dom.
        rewrite H0.
        rewrite eval_Formula_weaken.
        exact Hy.
  - simpl.
    now repeat rewrite eval_Term_weaken.
  - simpl.
    apply rel_equal.
    induction h.
    + reflexivity.
    + simpl.
      f_equal.
      * now rewrite eval_Term_weaken.
      * simpl.
        apply IHh.
Defined.

Fixpoint eval_Formula_subterm_subst {S} (eval_S : S -> Type)
  {sg : sig S} {eval_sig : sig_dom eval_S sg} {env}
  {args : env_dom eval_S env} {s} {t u : Term (func sg) env s}
  {phi : Formula sg env} {fw : Formula_subterm_witness t phi}
  {struct fw}
  :
  eval_Term eval_S (func_dom eval_S sg eval_sig) args t =
  eval_Term eval_S (func_dom eval_S sg eval_sig) args u ->
  eval_Formula eval_S sg eval_sig env args
    (Formula_subterm_subst phi fw u) <->
  eval_Formula eval_S sg eval_sig env args phi.
Proof.
  destruct fw; intros; simpl.
  - destruct o; simpl; now rewrite eval_Formula_subterm_subst.
  - destruct o; simpl; now rewrite eval_Formula_subterm_subst.
  - destruct q; simpl.
    + split; intros [x Hx].
      * exists x.
        rewrite eval_Formula_subterm_subst in Hx.
        ** exact Hx.
        ** repeat rewrite eval_Term_weaken.
           assert ((x, args) = rhv_insert pwhd x args) by reflexivity.
           repeat rewrite H0.
           now repeat rewrite eval_Term_weaken.
      * exists x.
        rewrite eval_Formula_subterm_subst.
        ** exact Hx.
        ** assert ((x, args) = rhv_insert pwhd x args) by reflexivity.
           repeat rewrite H0.
           now repeat rewrite eval_Term_weaken.
    + split; intros G x.
      * pose (Gx :=  G x).
        rewrite eval_Formula_subterm_subst in Gx.
        ** exact Gx.
        ** assert ((x, args) = rhv_insert pwhd x args) by reflexivity.
           repeat rewrite H0.
           now repeat rewrite eval_Term_weaken.
      * rewrite eval_Formula_subterm_subst.
        ** apply G.
        ** assert ((x, args) = rhv_insert pwhd x args) by reflexivity.
           repeat rewrite H0.
           now repeat rewrite eval_Term_weaken.
  - now rewrite eval_Term_subterm_subst.
  - now rewrite eval_Term_subterm_subst.
  - apply rel_equal.
    induction terms.
    + dependent destruction w.
    + dependent destruction w.
      * simpl.
        f_equal.
        unfold solution_left.
        unfold eq_rect_r.
        unfold eq_rect.
        simpl.
        now rewrite eval_Term_subterm_subst.
      * simpl.
        f_equal.
        apply IHterms.
Defined.

Require Import CoqFol.Syntax.Proof.
(* TODO: move suff_weaken *)

Lemma eval_Formula_suff_weaken {S} {eval_S} {sg : sig S}
  {eval_sig} {env} {suff} {args}
  {suff_wit : suffix_wit suff env} phi :
  eval_Formula eval_S sg eval_sig suff
    (rhv_suff suff_wit args) phi <->
  eval_Formula eval_S sg eval_sig env args
    (suff_weaken suff_wit phi).
Proof.
  induction suff_wit.
  - reflexivity.
  - simpl.
    destruct args.
    rewrite IHsuff_wit.
    simpl.
    epose (eval_Formula_weaken eval_S sg eval_sig _ _ _ _ pwhd)
      as eFw.
    simpl in eFw.
    rewrite eFw.
    reflexivity.
Defined.
