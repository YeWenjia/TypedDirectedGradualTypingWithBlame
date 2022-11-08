Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.




Lemma sim_refl: forall A,
  sim A A.
Proof.
  introv.
  induction* A.
Qed.

Hint Resolve sim_refl: core.

Lemma Typing_chk2: forall G e A,
  Typing G e Inf A ->
  Typing G e Chk A.
Proof.
  introv Typ.
  inductions Typ; eauto; try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H0];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H1];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H2].
Qed.



Lemma etyping_Typing: forall G A e1 e2 dir,
 etyping G e1 dir A e2 ->
 Typing G e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



(* 
Lemma Typing_chk2: forall G e A,
  Typing G e Chk A ->
  exists B, Typing G e Inf B.
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed. *)


(* Common Lemmas *)
Lemma Typing_regular_1 : forall e G dir A,
    Typing G e dir A -> lc_exp e.
Proof.
  intros e G dir A H.
  inductions H;
    eauto.
Qed.

Lemma Typing_regular_2 : forall G e dir T,
    Typing G e dir T -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
  pick fresh y.
  assert (uniq ((y, t_dyn) :: G)) by auto.
  solve_uniq.
  pick fresh y.
  assert (uniq ((y, t_dyn) :: G)) by auto.
  solve_uniq.
Qed.


Lemma Typing_weaken : forall G E F e dir T,
    Typing (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    Typing (E ++ F ++ G) e dir T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply Typ_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply Typ_absd; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply Typ_sugar; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma Typing_weakening : forall (E F : ctx) e dir T,
    Typing E e dir T ->
    uniq (F ++ E) ->
    Typing (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weaken.
Qed.


(** Typing is preserved by substitution. *)

Lemma fv_in_dom: forall G e dir T,
    Typing G e dir T -> fv_exp e [<=] dom G.
Proof.
  intros G e dir T H.
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
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (open_exp_wrt_exp e (e_var_f x)) [<=] dom ([(x,t_dyn)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (open_exp_wrt_exp e (e_var_f x))) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma value_no_fv : forall v dir T,
    Typing [] v dir T -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.

Lemma subst_value : forall v dir T z u,
    Typing [] v dir T -> subst_exp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma nlam_open: forall e v x,
  nlam v ->
  nlam e ->
  nlam [x ~> v] e.
Proof.
  introv nl1 nl2.
  inverts nl2; unfold subst_exp; eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
Qed.


Lemma lambda_decidable: forall e,
  nlam e \/ not(nlam e).
Proof.
  introv.
  inductions e; try solve[left*; exists*];
  try solve[right; unfold not; intros nt; inverts* nt; inverts H].
Qed.




Lemma Typing_subst_1 : forall (E F : ctx) e u dir S T (z : atom),
    Typing (F ++ [(z,S)] ++ E) e dir T ->
    Typing E u Inf S ->
    nlam u ->
    Typing (F ++ E) ([z ~> u] e) dir T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : Typing_regular_1 H0;
    lets Uni : Typing_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ Typing_weakening.
    solve_uniq.
  -
    pick fresh x and apply Typ_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply Typ_absd; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, t_dyn)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply Typ_sugar; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, t_dyn)] ++ F) ++ E).
    apply~ H2.
  -
    forwards*: IHTyping.
    destruct(lambda_decidable ([z ~> u] (e))). 
    eapply Typ_sim; eauto.
    inductions e; try solve[inverts H3];
    try solve[exfalso; apply H5; unfold subst_exp; eauto].
    unfold subst_exp in H5.
    destruct(x == z). inverts e; try solve[exfalso;apply H5; eauto].
    exfalso. apply H5. auto.
  - 
    forwards* h1: IHTyping1.
    forwards* h2: IHTyping2.
    destruct(lambda_decidable ([z ~> u] (e2))); eauto.
    forwards*:  nlam_open H1 H3.
Qed.

Lemma typing_c_subst_simpl : forall E e u dir S T z,
  Typing ([(z,S)] ++ E) e dir T ->
  Typing E u Inf S ->
  nlam u ->
  Typing E ([z ~> u] e) dir T.
Proof.
  intros E e u dir S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply Typing_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.

Lemma principle_inf: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

Lemma pattern_uniq: forall A A1 A2,
 pattern A A1 ->
 pattern A A2 ->
 A1 = A2.
Proof.
  introv pa1 pa2.
  inductions pa1; try solve[inverts* pa2].
Qed.



(* stronger than inf unique *)
Lemma Typing_strenthening : forall G e A1 A2,
    []  ⊢ e ⇒ A1 ->
    G ⊢ e ⇒ A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 G.
  inductions Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    inverts H0.
  - (* t_app *)
    forwards * : IHTy1_1 H7.
    subst.
    forwards*: pattern_uniq H H4.
    inverts* H0.
  - (* t_app *)
    forwards * : IHTy1_1 H2.
    subst*.
    congruence.
Qed.

Lemma inference_unique : forall G e A1 A2,
    Typing G e Inf A1 ->
    Typing G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
  forwards * : IHTy1_1 H7.
  subst.
  forwards*: pattern_uniq H H4.
  inverts* H0.
  - (* t_app *)
  forwards * : IHTy1_1 H2.
  subst.
  congruence.
Qed.

Lemma Typing_c_rename2 : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Chk T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Chk T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst*; eauto.
  Case "x <> y".
    assert (J : uniq (((x , T1) :: E))).
      eapply Typing_regular_2; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , T1) :: E)).
    apply Typing_subst_1 with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply Typing_weaken. eauto. auto.
    SCase "y is well-typed". eauto.
    eauto.
Qed.

Lemma Typing_chk: forall G e A,
  Typing G e Inf A ->
  exists B, Typing G e Chk B.
Proof.
  introv Typ.
  inductions Typ; eauto; try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H0];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H1];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H2].
  (* pick fresh x.
  forwards*: H0 x.
  inverts* H1.
  exists(t_arrow t_dyn x0).
  eapply Typ_abs with (L := union L (union (dom G) (fv_exp e)));intros;eauto.
  forwards*: Typing_c_rename2 x1 H2. *)
Qed.


Lemma atyping_regular_1 : forall e e2 G dir A,
    atyping G e dir A e2 -> lc_exp e2.
Proof.
  introv H.
  inductions H;
    eauto.
Qed.

Lemma atyping_regular_1r : forall e e2 G dir A,
    atyping G e dir A e2 -> lc_exp e.
Proof.
  introv H.
  inductions H;
    eauto.
Qed.



Lemma atyping_inf : forall v v2 G A,
    value v -> atyping G v Inf A v2 -> principal_type v = A.
Proof.
  introv val H.
  inductions H;
    eauto; try solve[inverts val].
Qed.



Lemma atyping_inf2 : forall v v2 G A,
    value v2 -> atyping G v Inf A v2 -> principal_type v2 = A.
Proof.
  introv val H.
  inductions H;
    eauto; try solve[inverts val].
Qed.


Lemma atyping_weaken : forall G E F e dir T t,
    atyping (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    atyping (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply atyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
(*       
    + (* abs *)
      pick fresh x and apply typ_abs2; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq. *)
    + (* abs *)
      pick fresh x and apply atyp_absd; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
(*       
    + (* abs *)
      pick fresh x and apply typ_absd2; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq. *)
    + (* abs *)
      pick fresh x and apply atyp_sugar; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
(*       
    + (* abs *)
      pick fresh x and apply typ_sugar2; eauto.
      rewrite_env (([(x, t_dyn)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq. *)
Qed.




Lemma atyping_weakening : forall (E F : ctx) e dir T t,
    atyping E e dir T t ->
    uniq (F ++ E) ->
    atyping (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ atyping_weaken.
Qed.



Lemma exists_decidable: forall e,
  (exists e' ll bb, e = e_abs e' ll bb) \/ not(exists e' l b, e = e_abs e' l b).
Proof.
  introv.
  inductions e; try solve[left*; exists*];
  try solve[right; unfold not; intros nt; inverts* nt; inverts H; inverts H0;
  inverts H].
Qed.


Lemma nlam_not_exist: forall e,
  nlam e ->
  not(exists e' ll bb, e = (e_abs e' ll bb)).
Proof.
  introv nl.
  inductions nl; 
  try solve[unfold not; intros nt; inverts* nt; inverts H;inverts H0;
  inverts H].
Qed.


Lemma nlam_exist: forall e,
  not(nlam e) ->
  (exists e' l b, e = (e_abs e' l b)).
Proof.
  introv nl.
  inductions e; try solve[exfalso; apply nl; eauto];eauto.
Qed.




Lemma nlam_open2: forall e v x,
  nlam v ->
  nlam e ->
  nlam [x ~> v] e.
Proof.
  introv nl1 nl2.
  inverts nl2; unfold subst_exp; eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
Qed.



Lemma not_nlam_open: forall v e x,
  not(nlam e) ->
  not(nlam [x ~> v] e).
Proof.
  introv nl.
  forwards*: nlam_exist nl.
  inverts* H. inverts H0. inverts H.
  unfold not;intros nt; inverts* nt.
Qed.


Lemma atyping_subst_1 : forall (E F : ctx) e u uu S T (z : atom) t,
    atyping (F ++ [(z,S)] ++ E) e Chk T t ->
    atyping E u Inf S uu ->
    nlam u ->
    atyping (F ++ E) ([z ~> u] e) Chk T ([z ~> uu] t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F .
  lets H': H. 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : atyping_regular_1 H0;
    lets Uni : atyping_regular_1r H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ atyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply atyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply atyp_absd; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, t_dyn)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply atyp_sugar; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, t_dyn)] ++ F) ++ E).
    apply~ H2.
  -
    forwards*: IHatyping. 
    destruct(lambda_decidable ([z ~> u] (e))).
    forwards*: nlam_not_exist H5.
    forwards*: nlam_exist H5.
    forwards*: atyping_regular_1 H4.
    inverts* H6. 
    inverts H8. inverts H6.
    rewrite H8 in *.
    inductions e; 
    try solve[inverts H3];
    try solve[inverts* H8].
    unfold subst_exp in H8.
    destruct(x == z). inverts e; try solve[inverts* H8].
    inverts* H8.
Qed.



Lemma atyping_c_subst_simpl : forall E e u uu t  S T z,
  atyping ([(z,S)] ++ E) e Chk T t ->
  atyping E u Inf S uu ->
  nlam u ->
  atyping E ([z ~> u] e) Chk T ([z ~> uu] t).
Proof.
  intros E e u uu t S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply atyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.


Lemma ainference_unique : forall G e e2 A1 A2,
    atyping G e Inf A1 e2 ->
    atyping G e Inf A2 e2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
  forwards * : IHTy1_1 H5.
  subst.
  inverts* H.
  - (* t_app *)
  forwards * : IHTy1_1 H9.
  subst.
  forwards*: pattern_uniq H H7.
  congruence.
Qed.