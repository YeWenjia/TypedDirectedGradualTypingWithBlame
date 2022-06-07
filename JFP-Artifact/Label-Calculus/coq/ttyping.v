Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               rulesb_inf
               Typing_b
               Infrastructure_b
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.


Lemma lc_lcb: forall E e t dir A,
 ttyping E e dir A t ->
 lc_exp e ->
 lc_term t.
Proof.
  introv typ H. 
  inductions typ; eauto. 
  -
    inverts H1. 
    pick fresh x.
    forwards*: H.
  - inverts* H1.
  - inverts* H.
  - inverts* H.
Qed.


(* Common Lemmas *)
Lemma ttyping_regular_1 : forall e G dir A t,
    ttyping G e dir A t -> lc_exp e.
Proof.
  introv H.
  induction H;
    eauto.
Qed.

Lemma ttyping_regular_2 : forall G e dir T t,
    ttyping G e dir T t -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
  pick fresh y.
  assert (uniq ((y, t_dyn) :: G)) by auto.
  solve_uniq.
Qed.


Lemma ttyping_weaken : forall G E F e dir T t,
    ttyping (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    ttyping (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply ttyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply ttyp_sugar; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.




Lemma ttyping_weakening : forall (E F : ctx) e dir T t,
    ttyping E e dir T t ->
    uniq (F ++ E) ->
    ttyping (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ ttyping_weaken.
Qed.



(** Typing is preserved by substitution. *)

Lemma ttfv_in_dom: forall G e dir T t,
    ttyping G e dir T t -> fv_exp e [<=] dom G.
Proof.
  introv H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (open_exp_wrt_exp e (e_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (open_exp_wrt_exp e (e_var_f x))) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (open_exp_wrt_exp e (e_var_f x)) [<=] dom ([(x,t_dyn)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (open_exp_wrt_exp e (e_var_f x))) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma ttvalue_no_fv : forall v dir T t,
    ttyping [] v dir T t -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_dom [] v).
  intuition eauto.
Qed.

Lemma ttsubst_value : forall v dir T t z u,
    ttyping [] v dir T t -> subst_exp u z v = v.
Proof.
  introv Typ.
  lets* Fv: ttvalue_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma lambda_decidable: forall e,
  nlam e \/ not(nlam e).
Proof.
  introv.
  inductions e; try solve[left*; exists*];
  try solve[right; unfold not; intros nt; inverts* nt; inverts H].
Qed.

Lemma ttyping_subst_1 : forall (E F : ctx) e u uu S l1 b1 T (z : atom) t,
    ttyping (F ++ [(z,S)] ++ E) e (Chk2 l1 b1) T t ->
    ttyping E u Inf2 S uu ->
    nlam u ->
    ttyping (F ++ E) ([z ~> u] e) (Chk2 l1 b1) T ([z ~> uu]' t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F . 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ ttyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply ttyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
    forwards*: lc_lcb H0.
  -
    pick fresh x and apply ttyp_sugar; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, t_dyn)] ++ F) ++ E).
    apply~ H2.
    forwards*: lc_lcb H0.
  -
    forwards*: IHttyping.
    destruct(lambda_decidable ([z ~> u] (e))). 
    eapply ttyp_sim; eauto.
    inductions e; try solve[inverts H3];
    try solve[exfalso; apply H5; unfold subst_exp; eauto].
    unfold subst_exp in H5.
    destruct(x == z). inverts e; try solve[exfalso;apply H5; eauto].
    exfalso. apply H5. auto.   
Qed.


Lemma ttyping_c_subst_simpl : forall E e u uu t p b  S T z,
  ttyping ([(z,S)] ++ E) e (Chk2 p b) T t ->
  ttyping E u Inf2 S uu ->
  nlam u ->
  ttyping E ([z ~> u] e) (Chk2 p b) T ([z ~> uu]' t).
Proof.
  intros E e u uu t p b  S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply ttyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.

(* Lemma ttyping_subst_11 : forall (E F : ctx) e u uu dir S p b T (z : atom) t,
    ttyping (F ++ [(z,S)] ++ E) e dir p b T t ->
    ttyping E u Inf p b S uu ->
    ttyping (F ++ E) ([z ~> u] e) dir p b T ([z ~> uu]' t) 
with  ttyping_subst_2 : forall (E F : ctx) e u uu S p b T (z : atom) t,
ttyping (F ++ [(z,S)] ++ E) e Chk p (negb b) T t ->
ttyping E u Inf p b S uu ->
ttyping (F ++ E) ([z ~> u] e) Chk p (negb b) T ([z ~> uu]' t) .
Proof.
  + intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F . 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ ttyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply ttyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    (* apply~ H1.
    forwards*: lc_lcb H0. *)
    admit.
    admit.
  + intros.
    remember (F ++ [(z,S)] ++ E) as E'. gen F . 
    inverts* H; try solve [intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0].
    - 
    intros.
    applys ttyp_sim. 
    subst.
    applys* ttyping_subst_11.
    admit.
    auto.
Qed. *)

(* Lemma ttyping_subst_1 : forall (E F : ctx) e u uu dir S l1 b1 l2 b2 T (z : atom) t,
    ttyping (F ++ [(z,S)] ++ E) e dir l1 b2 T t ->
    ttyping E u Inf l2 b2 S uu ->
    ttyping (F ++ E) ([z ~> u] e) dir l1 b1 T ([z ~> uu]' t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F . 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ ttyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply ttyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
    forwards*: lc_lcb H0.
  - eapply ttyp_app;auto.
    admit.
Qed. *)


(* Lemma ttyping_c_subst_simpl : forall E e u uu p b t dir S T z,
  ttyping ([(z,S)] ++ E) e dir p b T t ->
  ttyping E u Inf p b S uu ->
  ttyping E ([z ~> u] e) dir p b T ([z ~> uu]' t).
Proof.
  intros E e u uu p b t dir S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply ttyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed. *)


(* Lemma ttinference_unique : forall G e t p b A1 A2,
    ttyping G e Inf p b A1 t ->
    ttyping G e Inf p b A2 t->
    A1 = A2.
Proof.
  introv Ty1.
  gen A2.
  inductions Ty1; introv Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H7.
    inverts* H.
Qed.
 *)


Lemma elaboration_soundness : forall G e t dir A,
    ttyping G e dir A t ->
    Btyping G t A.
Proof.
  introv Ty1.
  inductions Ty1; intros; eauto.
Qed.