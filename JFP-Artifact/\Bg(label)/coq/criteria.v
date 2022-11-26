Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Bool.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.



Lemma abs_epre_true2: forall G1 G2 e1 e2 l b,
 nlam e2 ->
 epre G1 G2 (e_abs e1 l b) e2 ->
 False.
Proof.
  introv typ ep.
  inductions ep; try solve[inverts H3];
  try solve[inverts typ];eauto.
Qed.



Lemma absr_epre_true2: forall G1 G2 e1 e2 l b,
 nlam e1 ->
 epre G1 G2 e1  (e_abs e2 l b) ->
 False.
Proof.
  introv typ ep.
  inductions ep; try solve[inverts H3];
  try solve[inverts typ];eauto.
Qed.




Lemma flike_int: 
 FLike t_int ->
 False.
Proof.
  introv fl.
  inverts* fl.
  inverts* H0.
  inverts* H2.
Qed.

Hint Resolve  flike_int abs_epre_true2 absr_epre_true2: falseHd.

Ltac solve_false := try intro; try solve [false; eauto with falseHd].





Lemma abs_epre_true: forall e1 e2 l b,
 nlam e2 ->
 precision (e_abs e1 l b) e2 ->
 False.
Proof.
  introv typ ep.
  inductions ep; try solve[inverts H3];
  try solve[inverts typ];eauto.
Qed.



Lemma absr_epre_true: forall e1 e2 l b,
 nlam e1 ->
 precision e1  (e_abs e2 l b) ->
 False.
Proof.
  introv typ ep.
  inductions ep; try solve[inverts H3];
  try solve[inverts typ];eauto.
Qed.



Lemma tpre_refl: forall A,
  tpre A A.
Proof.
   inductions A; eauto.
Qed.


Lemma sim_refl: forall A,
 sim A A.
Proof.
  introv.
  inductions A; eauto.
Qed.



Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
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



Lemma env_less_precise_binds : forall x A E F,
    binds x A E ->
    cpre E F ->
    exists B, binds x B F /\ tpre A B.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  forwards*: IHcp.
  inverts* H1.
Qed.


Lemma cpre_notin: forall x E F,
 x # E ->
 cpre E F ->
 x # F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
Qed.



Lemma cpre_uniq: forall E F,
 uniq E ->
 cpre E F ->
 uniq F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
  inverts* uq.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.

Lemma epre_sim : forall A1 B1 A2 B2,
  sim A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  sim A2 B2.
Proof.
  introv s1 tp1 tp2. gen A2 B2.
  inductions s1; intros; eauto.
  - inverts tp1. inverts* tp2. inverts* tp2.
  - inverts* tp1.
    inverts* tp2.
  - inverts* tp1.
  - inverts* tp2. 
Qed.


Lemma dmatch_tpre: forall t1 t2 t3,
 tpre t1 t2 ->
 pattern t1 t3 ->
 exists t4, pattern t2 t4 /\
 tpre t3 t4.
Proof.
  introv tp dm. gen t3.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
Qed.


Lemma binds_tpre: forall x T T' E1 E2,
 uniq E1 ->
 uniq E2 ->
 cpre E1 E2 ->
 binds x T E1 ->
 binds x T' E2 ->
 tpre T T'.
Proof.
  introv uq1 uq2 cp bind1 bind2. gen x T T'.
  inductions cp; intros;try solve[inverts uq1;inverts uq2;inverts bind1;inverts* bind2].
  inverts uq1;inverts uq2;inverts bind1;inverts* bind2;
  try solve[inverts* H0;inverts* H1]; try solve[inverts* H0];
  try solve[inverts* H1].
  inverts* H0. 
  exfalso. apply H6;eauto.
  inverts H1.
  exfalso. apply H4;eauto.
Qed.



Lemma dmatch_tpre2: forall t1 t2 t3 t4,
 tpre t1 t2 ->
 pattern t1 t3 ->
 pattern t2 t4 ->
 tpre t3 t4.
Proof.
  introv tp dm1 dm2. gen t3 t4.
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm1; inverts* dm2].
Qed.



Lemma Principle_inf: forall E v T,
 value v ->
 Typing E v Inf T ->
 principal_type v = T.
Proof.
  introv val typ.
  inductions val; simpl in *;try solve[inverts* typ].
Qed.



Theorem precise_type: forall E1 E2 e e' T T',
epre nil nil e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
 introv ep cp Typ1 Typ2.
 gen E1 E2 T T'.
 inductions ep; intros;
 try solve[inverts* Typ1; inverts* Typ2].
 - 
   inverts Typ1. inverts Typ2.
   forwards*: binds_tpre H4 H6.
 - 
   inverts* Typ1.
   inverts* Typ2.
   forwards*: IHep1 H7 H10.
   forwards*: dmatch_tpre2 H4 H5.
    inverts* H1.
 -
   inverts* Typ2.
   inverts* H10; try solve[inverts H0].
  +
    forwards*: Typing_strenthening H Typ1.
    substs*.
  +
  forwards*: Typing_strenthening H Typ1.
    substs*.
- 
  inverts* Typ1. 
  inverts* H10; try solve[inverts H];
  try solve[forwards*: abs_epre_true2 ep].
  +
  forwards*: Typing_strenthening H0 Typ2.
  substs*.
 -
   inverts Typ1. inverts Typ2.
   forwards*:  IHep1 H1 H2.
   inverts* H.
 (* -
   inverts Typ1. inverts Typ2.
   forwards*: Typing_weakening E2 H12.
   simpl_env in *.
   forwards*:  IHep1 H10 H3.
   inverts* H4.
   inverts* H7.
  -
   inverts Typ1. inverts Typ2.
   forwards*: Typing_weakening E1 H7.
   simpl_env in *.
   forwards*:  IHep1 H1 H13.
   inverts* H10. inverts* H2. *)
  -
     inverts* Typ1.
   inverts* Typ2.
   forwards*: IHep1 H10 H13.
   forwards*: dmatch_tpre2 H7 H8.
    inverts* H4.
Qed.


Theorem precise_type2: forall E1 E2 e e' T T',
precision e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
  introv ep cp Typ1 Typ2.
  gen E1 E2 T T'.
  inductions ep; intros;
  try solve[inverts* Typ1; inverts* Typ2].
  - inverts Typ1. inverts Typ2.
    forwards*: binds_tpre H2 H4.
  - 
    inverts* Typ1.
    inverts* Typ2.
    forwards*: IHep1 H6 H9.
    forwards*: dmatch_tpre2 H3 H4.
     inverts* H0.
Qed.


Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 precision e1 e2 ->
 Typing E1 e1 Chk t ->
 tpre t t2 ->
 Typing E2 e2 Chk t2.
Proof.
  introv cp ep typ tp. gen E1 E2 t t2.
  inductions ep; intros.
  + inverts typ.
    inverts H.
    forwards*: env_less_precise_binds H5. inverts H. inverts H2.
    forwards*: cpre_uniq cp.
    forwards*: epre_sim H0 H4 tp.
  + inverts typ. inverts H.
    forwards*: cpre_uniq cp.
    assert(tpre t_int t_int);eauto.
    forwards*: epre_sim H0 H2 tp.
  + 
    inverts* typ; try solve[forwards*: abs_nlam].
    *
    inverts tp.
    pick fresh x and apply Typ_absd.
    assert(cpre ((x, A) :: E1) ((x, t_dyn) :: E2));eauto.
    pick fresh x and apply Typ_abs.
    assert(cpre ((x, A) :: E1) ((x, C) :: E2));eauto.
    *
    inverts tp.
    pick fresh x and apply Typ_absd.
    assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
  + 
    inverts typ. inverts H.
    forwards*: Typing_chk H9. inverts H.
    forwards*: IHep1.
    inverts H;try solve[forwards*: abs_nlam].
    *
    forwards*: IHep2 H10.
    *
    forwards*: precise_type2 ep1 H9 H3.
    forwards*: dmatch_tpre H H6.
    inverts H7. inverts H8. inverts H11; try solve[inverts H7].
    forwards*: IHep2 H10 H13.
    forwards*: epre_sim H0 H15 tp.
  + 
    inverts typ. inverts H0.
    forwards*: IHep H.
    forwards*: epre_sim H1 H tp.
  (* +
    forwards*: IHep typ  tp.
    inverts typ; try solve[inverts H];
    try solve[forwards*: abs_nlam].
    forwards*: Typing_strenthening H H5.
    subst.
    forwards*: epre_sim H6 H1 tp.
    (* assert(sim A0 A0). apply sim_refl.
    forwards*: epre_sim H9 H2 H1. *)
  +
    inverts typ. inverts H4.
    forwards*: epre_sim H5 H1 tp.
    forwards*: IHep H13 H1.
    inverts H7; try solve[inverts* H0].
    * 
    forwards*: Typing_strenthening H0 H8.
    substs*. *)
  +
    inverts typ. inverts H. 
    assert(tpre (t_arrow t_int (t_arrow t_int t_int)) (t_arrow t_int (t_arrow t_int t_int))); auto.
    forwards*: epre_sim H0 H tp.
    forwards*: cpre_uniq cp.
  +
    inverts typ. inverts H. 
    assert(tpre (t_arrow t_int t_int) ((t_arrow t_int t_int))); auto.
    forwards*: epre_sim H0 H tp.
    forwards*: cpre_uniq cp.
Qed.



Theorem SGG_chk: forall e e' T E1 E2,
   precision e e' ->  
   Typing E1 e Chk T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' Chk T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp.
  assert(tpre T T).
  apply tpre_refl.
  forwards*: tpre_chk Typ1 H.
Qed.


Lemma precision_abs: forall e e1 l b,
 precision (e_abs e l b) e1 ->
 exists e' ll bb, e1 = (e_abs e' ll bb).
Proof.
  introv ep.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.


Lemma precision_absr: forall e e1 l b,
 precision  e1 (e_abs e l b) ->
 exists e' ll bb, e1 = (e_abs e' ll bb).
Proof.
  introv ep.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.


Lemma precision_nlam: forall e e1,
 precision e1 e ->
 nlam e1 ->
 nlam e.
Proof.
  introv ep nl.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.

Lemma precision_nlamr: forall e e1,
 precision e1 e ->
 nlam e ->
 nlam e1.
Proof.
  introv ep nl.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.



Theorem SGG_both: forall e e' T E1 E2 dir,
   precision e e' ->  
   Typing E1 e dir T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp. gen E1 E2 T dir.
  inductions ep; intros;
  try solve[destruct dir;
  try solve[
  forwards*: Typing_chk Typ1; inverts H;
  forwards*: SGG_chk H0;
  inverts H;inverts H1;
  inverts H0; try solve[forwards*:abs_epre_true ep];
  inverts H; try  solve[forwards*:absr_epre_true ep];
  forwards*: precise_type2 H1 H0;
  forwards*: inference_unique Typ1 H1; substs*];
  try solve[
  forwards*: SGG_chk Typ1]].
  -
    destruct dir.
    +
    inverts Typ1.
    exists. splits.
    pick fresh x and apply Typ_sugar.
    assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
    forwards* ha: H6 x.
    forwards* hb: H0 H1 t_dyn ha.
    lets(tt1&hc&hd):hb.
    inverts* hd.
    auto.
    +
    forwards*: SGG_chk Typ1.
  -
  destruct dir.
  +
  forwards*: Typing_chk Typ1. inverts H0.
  forwards*: SGG_chk H1.
  inverts H0. inverts H2.
  inverts H0; try solve[forwards*:abs_epre_true ep].
  inverts H1; try  solve[forwards*:absr_epre_true ep].
  forwards*: precise_type2 H0 H2.
  forwards*: inference_unique Typ1 H0. substs*.
  +
  forwards*: SGG_chk Typ1.
Qed.


Lemma epre_lc: forall G1 G2 e1 e2,
 epre G1 G2 e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. 
  inductions ep; intros; eauto;
  try solve [inverts lc; eauto].
  pick fresh x.
  inverts lc. 
  forwards*: H0. inverts* H1.
  forwards*: lc_e_abs_exists H4.
  apply lc_e_anno.
  inverts lc. inverts H5.
  pick fresh x.
  forwards*: H0 x.
  inverts H4.
  forwards*: lc_e_abs_exists H7.
  inverts* lc.
  forwards*: IHep2. inverts* H3.
Qed.

Lemma epre_lc2: forall G1 G2 e1 e2,
 epre G1 G2 e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. 
  inductions ep; intros; eauto;
  try solve [inverts lc; eauto].
  pick fresh x.
  inverts lc. 
  forwards*: H0 x. inverts H1.
  forwards*: lc_e_abs_exists H4.
  inverts lc. inverts H5.
  pick fresh x.
  forwards*: H6 x.
  forwards*: H0 x.
  inverts* H5.
  forwards*: lc_e_abs_exists H8.
  inverts lc.
  forwards*: IHep2. inverts* H3.
Qed.



Lemma epre_llc: forall G1 G2 e1 e2,
 epre G1 G2 e1 e2 ->
 lc_exp e1 /\
 lc_exp e2.
Proof.
  introv ep. 
  inductions ep; intros; eauto;
  try solve[inverts* IHep];
  try solve[inverts* IHep1].
  -
  splits.
  +
  pick fresh x.
  forwards*: H0 x. inverts* H1. inverts H2.
  forwards*: lc_e_abs_exists H4.
  +
  pick fresh x.
  forwards*: H0 x. inverts* H1. inverts H3.
  forwards*: lc_e_abs_exists H4.
  -
  splits.
  +
  pick fresh x.
  forwards*: H0 x. inverts H4. 
  eapply lc_e_anno. inverts H5.
  forwards*: lc_e_abs_exists H7.
  +
  pick fresh x.
  forwards*: H0 x. inverts H4. inverts H6. 
  eapply lc_e_anno.
  forwards*: lc_e_abs_exists H7.
  -
  inverts IHep2. inverts* H3. inverts* H4.
Qed.


Lemma epre_uniq: forall G1 G2 e1 e2,
 epre G1 G2 e1 e2 ->
 uniq G1 /\ uniq G2.
Proof.
  introv ep.
  inductions ep;eauto.
  -
  splits.
  +
  pick fresh y.
  forwards*: H0 y. inverts H1.
  assert (uniq ((y, t_dyn) :: G1)) by auto.
  solve_uniq.
  +
  pick fresh y.
  forwards*: H0 y. inverts H1.
  assert (uniq ((y, t_dyn) :: G1)) by auto.
  solve_uniq.
  -
  splits.
  +
  pick fresh y.
  forwards*: H0 y. inverts H4.
  assert (uniq ((y, A1) :: G1)) by auto.
  solve_uniq.
  +
  pick fresh y.
  forwards*: H0 y. inverts H4.
  assert (uniq ((y, A1) :: G1)) by auto.
  solve_uniq.
Qed.


Lemma epre_weaken: forall  F1 F2 G1 G2 G3 G4 e1 e2,
 epre (G3 ++ G1) ((G4 ++ G2)) e1 e2 ->
 uniq (G3 ++F1 ++  G1) ->
 uniq (G4 ++F2 ++ G2) ->
 epre (G3 ++F1 ++  G1) ((G4 ++F2 ++ G2)) e1 e2.
Proof.
  introv ep. gen F1 F2.
  inductions ep; intros;eauto.
  -
    pick fresh y. apply ep_abs with (L := union L
    (union (dom G1)
      (union (dom G3)
          (union (dom G2)
            (union (dom G4)
                (union (dom F1)
                  (union (dom F2) (union (fv_exp e1) (fv_exp e2)))))))));intros.
    rewrite_env (((x, t_dyn) :: G3) ++ F1 ++ G1).
    rewrite_env (((x, t_dyn) :: G4) ++ F2 ++ G2).
    forwards: H0 x G1 G2 ([(x, t_dyn)] ++ G3) ([(x, t_dyn)] ++ G4). 
    auto.
    auto.
    auto.
    assert(uniq (((x, t_dyn) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H4. 
    assert(uniq ((((x, t_dyn) :: G4) ++ F2 ++ G2))).
    solve_uniq.
    apply H4.
    auto.
  -
  pick fresh y. 
  eapply ep_absn with (L := union L
    (union (dom G1)
      (union (dom G3)
          (union (dom G2)
            (union (dom G4)
                (union (dom F1)
                  (union (dom F2) (union (fv_exp e1) (fv_exp e2)))))))));intros.
    rewrite_env (((x, A1) :: G3) ++ F1 ++ G1).
    rewrite_env (((x, B1) :: G4) ++ F2 ++ G2).
    forwards: H0 x G1 G2 ([(x, A1)] ++ G3) ([(x, B1)] ++ G4). 
    auto.
    auto.
    auto.
    assert(uniq (((x, A1) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H7. 
    assert(uniq ((((x, B1) :: G4) ++ F2 ++ G2))).
    solve_uniq.
    apply H7.
    apply H7.
    apply H1.
    apply H2.
    auto.
  -
    forwards*: Typing_weaken H H4.
    forwards*: Typing_weaken H0 H5.
  -
    forwards*: Typing_weaken H H4.
    forwards*: Typing_weaken H0 H5.
  -
    forwards*: Typing_weaken H H3.
    forwards*: Typing_weaken H0 H4.
Qed.


Lemma epre_weakening : forall E1 E2 F1 F2 e1 e2,
    epre E1 E2 e1 e2 ->
    uniq (F1 ++ E1) ->
    uniq (F2 ++ E2) ->
    epre (F1 ++ E1) (F2 ++ E2) e1 e2.
Proof.
  intros.
  rewrite_env (nil ++ F1 ++ E1).
  rewrite_env (nil ++ F2 ++ E2).
  apply~ epre_weaken.
Qed.


Lemma epre_open1: forall e1 e2 u1 u2 x A B GG1 GG2 G1 G2,
 epre (GG1 ++ [(x,A)] ++ G1) (GG2 ++ [(x,B)] ++ G2) e1 e2 ->
 epre G1 G2 u1 u2 ->
 nlam u1 ->
 nlam u2 ->
 Typing G1 u1 Inf A ->
 Typing G2 u2 Inf B ->
 epre (GG1++G1) (GG2++G2) [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 wal1 wal2 ty1 ty2. gen u1 u2.
  inductions ep1; intros; 
  simpl; eauto.
  -
    forwards*: Typing_weakening ty1.
    forwards*: Typing_weakening ty2.
    forwards*: Typing_weaken H1 H.
    forwards*: Typing_weaken H2 H0.
    forwards* h1: Typing_regular_2 H1.
    forwards* h2: Typing_regular_2 H2.
    forwards*: epre_weakening ep2 h1 h2.
    destruct (x0 == x); eauto.
  -
    pick fresh y.
    apply ep_abs with (L := union L
    (union (singleton x)
       (union (dom GG1)
          (union 
             (dom G1)
             (union 
               (dom GG2)
               (union 
               (dom G2)
               (union
               (fv_exp e1)
               (union
               (fv_exp e2)
               (union
               (fv_exp u1)
               (fv_exp u2))))))))));intros.
     forwards* lc: epre_llc ep2. inverts lc.
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     assert(([x ~> u2] (e2) ^^ e_var_f x0) = [x ~> u2] (e2 ^^ e_var_f x0) ).
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     rewrite H4.
     rewrite_env (([(x0, t_dyn)] ++ GG1) ++ G1).
     rewrite_env (([(x0, t_dyn)] ++ GG2) ++ G2).
     forwards*: H0 x0 x  ty1 ty2.
     auto.
     auto.
  -
    apply ep_app;eauto.
    forwards*: nlam_open wal1 H.
  -
    apply ep_anno; auto.
    forwards*: IHep1 ty1 ty2.
    forwards*: nlam_open wal1 H0.
  -
    pick fresh y.
    eapply ep_absn with (L := union L
    (union (singleton x)
       (union (singleton l1)
          (union
             (singleton l2)
             (union 
               (dom GG1)
               (union 
               (dom G1)
               (union
               (dom GG2)
               (union 
               (dom G2)
               (union
               (fv_exp e1)
               (union
               (fv_exp e2)
               (union
               (fv_exp u1)
               (fv_exp u2)))))))))))); intros.
    forwards* lc: epre_llc ep2. inverts lc.
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     assert(([x ~> u2] (e2) ^^ e_var_f x0) = [x ~> u2] (e2 ^^ e_var_f x0) ).
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     rewrite H7.
     rewrite_env (([(x0, A1)] ++ GG1) ++ G1).
     rewrite_env (([(x0, B1)] ++ GG2) ++ G2).
     forwards*: H0 x0 x  ty1 ty2.
     auto.
     auto.
     apply H1.
     apply H2.
     auto.
  -
    forwards*: IHep1 ep2.
    eapply ep_annor; eauto.
    forwards*: Typing_subst_1 H ty1.
    forwards*: Typing_subst_1 H0 ty2.
    forwards*: nlam_open wal1 H3.
  -
    forwards*: IHep1 ep2.
    eapply ep_annol; eauto.
    forwards*: Typing_subst_1 H ty1.
    forwards*: Typing_subst_1 H0 ty2.
    forwards*: nlam_open wal2 H3.
  -
    forwards*: Typing_subst_1 H ty1.
    forwards*: Typing_subst_1 H0 ty2.
    forwards*: IHep1_1 ep2.
    forwards*: IHep1_2 ep2.
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x A B  G1 G2,
 epre ( [(x,A)] ++ G1) ([(x,B)] ++ G2) e1 e2 ->
 epre G1 G2 u1 u2 ->
 nlam u1 ->
 nlam u2 ->
 Typing G1 u1 Inf A ->
 Typing G2 u2 Inf B ->
 epre (G1) (G2) [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 wal1 wal2 ty1 ty2.
  introv.
  rewrite_env (nil ++ G1).
  rewrite_env (nil ++ G2).
  eapply epre_open1; eauto.
Qed.


Lemma anno_chk: forall e t1 t2 l b,
 [] ⊢ e_anno e l b t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.


Lemma tpre_principle: forall v1 v2,
 epre nil nil v1 v2 ->
 value v1 ->
 value v2 ->
 tpre (principal_type v1) (principal_type v2).
Proof.
  introv ep val1 val2.
  inductions ep; try solve_false;
  simpl;
  try solve[inverts* val1];
  try solve[inverts* val2].
  inverts* val2.
  forwards*: Principle_inf H. rewrite H4; auto.
  inverts* val1.
  forwards*: Principle_inf H0. rewrite H4; auto.
  inverts H1.
  forwards*: Principle_inf H0. rewrite H1; auto.
Qed.



Lemma epre_dyn: forall e1 e2 t1 t2 l b,
 Typing nil e1 Inf (t_arrow t1 t2) ->
 Typing nil e2 Inf (t_arrow t_dyn t_dyn) ->
 value e1 ->
 walue e2 ->
 value (e_anno e2 l b t_dyn) ->
 epre nil nil e1 (e_anno e2 l b t_dyn) ->
 epre nil nil e1 e2.
Proof.
  introv ty1 ty2 val1 wal val2 ep. gen t1 t2.
  inductions ep; intros;try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep]; eauto.
  -
  inverts ty1.
  inverts* H7; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep].
  inverts val1.
  forwards*: Principle_inf H1.
  rewrite H4 in H10. subst*.
  -
  inverts wal.
  -
  inverts ty1. inverts val1.
  inverts* H10; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep].
  forwards*: Principle_inf H4.
  rewrite <- H11 in *. substs*.
  forwards*: IHep.
Qed.



Lemma epre_nlam: forall G1 G2 e e1,
 epre G1 G2 e1 e ->
 nlam e1 ->
 nlam e.
Proof.
  introv ep nl.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.

Lemma epre_nlamr: forall G1 G2 e e1,
 epre G1 G2 e1 e ->
 nlam e ->
 nlam e1.
Proof.
  introv ep nl.
  inductions ep;eauto;
  try solve[forwards*: abs_nlam].
Qed.

Lemma epre_value_arrow: forall v1 v2 t1 t2 tt1 tt2,
 Typing nil v1 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 epre nil nil v1 v2 ->
 value v1 ->
 value v2 ->
 nlam v1 ->
 nlam v2 ->
 principal_type v1 = (t_arrow t1 t2) ->
 ( exists v2' l b , v2 = (e_anno v2' l b t_dyn) /\ 
 principal_type v2' = t_arrow t_dyn t_dyn) \/
 (exists t3 t4 ,  principal_type v2 = (t_arrow t3 t4))  .
Proof.
  introv typ1 typ2 ep val1 val2 nl1 nl2 ty. gen tt1 tt2 t1 t2.
  inductions ep; intros;try solve[inverts* val1];
  try solve[inverts* ty];
  try solve[simpl in *; subst; inverts* H1;
  try solve[inverts* val1]];
  try solve[inverts nl1].
  -
  simpl in ty. inverts ty.
  inverts* H.
  inverts val1. inverts val2.
  forwards*: tpre_principle ep.
  rewrite <- H6 in *.
  inverts* H.
  rewrite <- H7 in *. inverts H3.
  rewrite <- H7 in *. inverts* H3.
  right. exists*.
  -
  inverts ty;simpl in *. inverts H4.
  inverts H1.
  inverts* H2.
  -
  inverts val2.
  forwards*: tpre_principle ep.
  right.  exists*.
  left.
  rewrite ty in *.
  forwards*: tpre_principle ep.
  rewrite ty in *.
  inverts H9; simpl in *;inverts* H4; try solve[inverts* H6].
  -
  simpl in *;inverts* ty.
  inverts* val1. inverts* typ1.
  forwards*: epre_nlamr ep.
Qed. 


Lemma flike_tpre: forall A B,
 tpre A B ->
 FLike A ->
 exists t1 t2, (A = (t_arrow t1 t2)) /\ ((B = t_dyn) \/ (exists t3 t4, B = (t_arrow t3 t4))).
Proof.
  introv tp fl.
  inverts fl. inverts H0. inverts* H2.
  inverts tp.
  exists. splits*.
  exists. splits*.
Qed.


Lemma flike_left: forall A B,
 A <> t_dyn ->
 FLike (t_arrow A B).
Proof.
  introv eq.
  unfold FLike; intros.
  splits*.
  unfold not; intros nt; inverts* nt.
  unfold not; intros nt; inverts* nt.
Qed.

Lemma flike_right: forall A B,
 B <> t_dyn ->
 FLike (t_arrow A B).
Proof.
  introv eq.
  unfold FLike; intros.
  splits*.
  unfold not; intros nt; inverts* nt.
  unfold not; intros nt; inverts* nt.
Qed.


Hint Resolve flike_left flike_right: core.


Lemma tpre_v_dyn_int: forall i v l b,
 value (e_anno v l b t_dyn) ->
 epre nil nil (e_lit i) (e_anno v l b t_dyn) ->
 principal_type v = t_int.
Proof.
  introv val ep.
  inductions ep; eauto.
  inductions ep; eauto.
  inverts* val; simpl in *. 
  inverts* H13.
  forwards*: tpre_principle ep; simpl in *.
  rewrite <- H16 in *. inverts H9.
  forwards*: tpre_principle ep; simpl in *.
  inverts H11.
Qed.



Lemma nlam_not_exist: forall e,
  nlam e ->
  not(exists e' l b, e = (e_abs e' l b)).
Proof.
  introv nl.
  inductions nl; 
  try solve[unfold not; intros nt; inverts* nt; inverts H;
  inverts H0;inverts H].
Qed.


Lemma nlam_exist: forall e,
  not(nlam e) ->
  (exists e' l b, e = (e_abs e' l b)).
Proof.
  introv nl.
  inductions e; try solve[exfalso; apply nl; eauto];eauto.
Qed.


Lemma tpre_v_dyn_fun: forall v1 v2 l1 b1 l2 b2,
 value (e_anno v1 l1 b1 (t_arrow t_dyn t_dyn))  ->
 value (e_anno v2 l2 b2 t_dyn) ->
 epre nil nil (e_anno v1 l1 b1 (t_arrow t_dyn t_dyn)) (e_anno v2 l2 b2 t_dyn) ->
 principal_type v2 = t_arrow t_dyn t_dyn.
Proof.
  introv val1 val2  ep.
  inductions ep; eauto; simpl in *.
  -
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep.
  rewrite <- H7 in *.
  inverts H6; inverts H1; inverts* H4. 
  -
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep; simpl in *.
  inverts H9; inverts H4; inverts* H7. 
  -
  clear IHep.
  inverts val1. inverts val2.
  forwards*: epre_value_arrow ep.
  forwards*: epre_nlamr ep.
  inverts H4.
  +
  lets(v2'&ll&bb&eq1&eq2): H5.
  inverts* eq1.
  +
  lets(t3&t4&eq): H5.
  inverts* eq. 
Qed.


Lemma remove_left_dyn: forall v1 v2 t1 t2 tt1 tt2 l b,
 Typing nil v1 Inf tt1 ->
 Typing nil (e_anno v2 l b t_dyn) Inf tt2 ->
 value v1 ->
 value (e_anno v2 l b t_dyn) ->
 principal_type v1 = (t_arrow t1 t2) ->
 principal_type v2 = (t_arrow t_dyn t_dyn) ->
 epre nil nil v1 (e_anno v2 l b t_dyn) ->
 epre nil nil v1 v2 \/ (exists e' l b, v2 = e_abs e' l b).
Proof.
  introv typ1 typ2 val1 val2 ty1 ty2 ep. gen tt1 tt2 t1 t2.
  inductions ep;intros; eauto.
  -
  inverts ty1; simpl in *. subst.
  inverts typ1. inverts typ2.
  inverts H7;  try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_nlam].
  inverts val2.
  forwards*: Principle_inf H1.
  rewrite ty2 in *. subst.
  inverts val1. auto.
  inverts H8; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  right. exists*.
  forwards*: Principle_inf H5.
  rewrite <- H8 in *. subst.
  left.
  eapply ep_annol; eauto.
  rewrite ty2 in *. subst*.
  inverts val1.
  rewrite <- H15 in *. subst.
  rewrite ty2 in *. subst.
  auto.
  -
  inverts* val2. inverts ty1; simpl in *. subst.
  inverts val1.
  forwards*: IHep v2.
  inverts H0. 
  inverts H15; inverts ty2; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  right. exists*. 
  forwards*: Principle_inf H.
  rewrite H10 in *. subst.
  forwards*: Principle_inf H0.
  rewrite H12 in *. subst.
  inverts H4.
  left.
  eapply ep_annol; eauto.
  inverts* H10.
Qed.


Lemma remove_left_dynarr: forall v1 v2 tt1 tt2 l1 b1 l2 b2,
 Typing nil v1 Inf tt1 ->
 Typing nil (e_anno v2 l1 b1 (t_arrow t_dyn t_dyn)) Inf tt2 ->
 value v1 ->
 value (e_anno v2 l1 b1 (t_arrow t_dyn t_dyn)) ->
 epre nil nil v1 (e_anno (e_anno v2 l1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow t_dyn t_dyn)) ->
 epre nil nil v1 (e_anno v2 l1 b1 (t_arrow t_dyn t_dyn)) .
Proof.
  introv typ1 typ2 val1 val2 ep. gen tt1 tt2.
  inductions ep; intros; eauto; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  -
  inverts typ1. inverts H.
  inverts typ2.
  inverts val1. 
  inverts H7; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  forwards*: Principle_inf H.
  rewrite <- H6 in *. subst.
  eapply ep_annol; eauto.
  rewrite <- H10 in *. subst.
  auto.
  -
  inverts H0. inverts H1. inverts val1.
  inverts typ2.  
  forwards*: IHep. 
Qed.



Lemma epre_ignore_label:forall e1 e2 l1 b1 l2 b2 t G1 G2,
 epre G1 G2 e1 (e_anno e2 l1 b1 t) ->
 epre G1 G2 e1 (e_anno e2 l2 b2 t).
Proof.
  introv ep1. gen l2 b2.
  inductions ep1; intros;eauto.
  inverts* H0.
Qed.



Lemma epre_ignore_labelr:forall e1 e2 l1 b1 l2 b2 t G1 G2,
 epre G1 G2  (e_anno e2 l1 b1 t)  e1 ->
 epre G1 G2  (e_anno e2 l2 b2 t)  e1.
Proof.
  introv ep1. gen l2 b2.
  inductions ep1; intros;eauto.
  inverts* H.
Qed.


Lemma tred_dyn_same: forall v0 v1 A v2 v3 tt1 tt2 l1 b1 l2 b2,
 Typing nil v3 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 value v3 ->
 walue v1 ->
 epre nil nil v0 v1 ->
 epre nil nil v3 v2 ->
 value (e_anno v1 l1 b1 t_dyn) ->
 TypedReduce v1 l2 b2 A (e_exp v2) ->
 TypedReduce (e_anno v1 l1 b1 t_dyn) l2 b2 A (e_exp v2) \/
 (exists v4, 
  TypedReduce (e_anno v1 l1 b1 t_dyn) l2 b2 A (e_exp v4) /\ epre nil nil v3 v4).
Proof.
  introv typ1 typ2 val3 wal ep0 ep val red.
  inductions red; eauto;
  try solve[inverts val; inverts H2];
  try solve[inverts val; inverts H1];
  try solve[inverts val; inverts H4].
  -
  inverts val. rewrite H0 in *.
  inverts H3.
  destruct(eq_type A). destruct(eq_type B). subst.
  + 
  inverts H5; inverts* H0.
  inverts wal.
  right.
  exists. splits.
  apply TReduce_vany; eauto.
  inverts typ2. inverts H8.
  forwards*: remove_left_dynarr ep.
  +
  inverts H5; inverts H0; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  inverts wal.
  left.
  apply TReduce_dyna; eauto.
  +
  inverts H5; inverts H0;try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  inverts wal.
  left.
  apply TReduce_dyna; eauto.
  -
  inverts val.
  forwards*: value_lc H4.
  forwards*: epre_ignore_label l1 b1 ep. 
  -
  assert(principal_type (e_lit i5) = t_int); simpl; auto.
  rewrite <- H; eauto.
  -
  inverts val. 
  forwards*: flike_not_ground H.
Qed.




Lemma not_lam_epre: forall e1 e2,
 epre nil nil e1 e2 ->
 ~ (exists e l b, e2 = e_abs e l b) ->
 ~ (exists e ll bb, e1 = e_abs e ll bb).
Proof.
  introv ep nt.
  inductions ep; eauto; 
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H0];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H4];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H3].
Qed.


Lemma not_lam_eprer: forall e1 e2,
 epre nil nil e1 e2 ->
 ~ (exists e l b, e1 = e_abs e l b) ->
 ~ (exists e ll bb, e2 = e_abs e ll bb).
Proof.
  introv ep nt.
  inductions ep; eauto; 
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H0];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H4];
  try solve[unfold not; intros nnt;inverts* nnt;inverts* H3].
Qed.


Lemma epre_absr_aux: forall v e l1 b1 ll1 bb1,
  value v ->
  principal_type v = t_dyn ->
  epre nil nil (e_anno (e_abs e ll1 bb1) l1 b1 t_dyn) v ->
  epre nil nil (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t_dyn t_dyn))  v.
Proof.
  introv val ty ep. 
  inductions ep; intros;try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep]; simpl in *;eauto; subst.
  -
  lets ep':ep.
  inductions ep; try solve[forwards*: abs_epre_true2 ep'];
  try solve[forwards*: abs_epre_true2 ep']; eauto.
  -
  inverts H1. inverts* H2.
  -
  inverts H. inverts H2.
  inverts val; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: abs_epre_true2 ep].
  forwards*: principle_inf H0. rewrite H in *. 
  inverts H4.
Qed.


Lemma epre_absr: forall v e l1 b1 l2 b2 ll1 bb1,
  value v ->
  principal_type v = t_dyn ->
  epre nil nil (e_anno (e_abs e ll1 bb1) l1 b1 t_dyn) v ->
  epre nil nil (e_anno (e_abs e ll1 bb1) l2 b2 (t_arrow t_dyn t_dyn))  v.
Proof.
  introv val ty ep. 
  forwards*: epre_absr_aux ep.
  forwards*: epre_ignore_labelr H.
Qed.




Lemma tred_left: forall v1 v2 v1' t2 t l b,
 Typing nil v1 Chk t ->
 Typing nil v2 Inf t2 ->
 value v1 ->
 value v2 ->
 epre nil nil v1 v2 ->
 tpre t t2 ->
 TypedReduce v1 l b t (e_exp v1') ->
 nlam v1 ->
 epre nil nil v1' v2.
Proof.
  introv typ1 typ2 val1 val2 ep tp red nl.
  destruct t.
  -
    gen t2 v1'.
    lets ep': ep.
    inductions ep;intros; try solve[forwards: abs_epre_true2 ep'];
    try solve[forwards: abs_epre_true2 ep'];
    try solve[inverts val1];
    try solve[inverts red].
    +
    inverts* red.
    +
    inverts typ1. inverts typ2.
    inverts H1.
    inverts H10;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: abs_epre_true2 ep]; try solve[inverts tp];
    try solve[inverts H1].
    *
    inductions ep; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: abs_epre_true2 ep]; inverts red;
    try solve[
      forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    *
    inverts H11; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; try solve[inverts H2];
    try solve[inverts* red;inverts H12; inverts H7;
    inverts H9];
    try solve[inverts tp].
    inverts red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; eauto;
    try solve[inverts H11;inverts H5; inverts H7].
    inverts* H.
    inverts val1. inverts val2.
    forwards*: Principle_inf H1.
    forwards*: Principle_inf H6.
    forwards*: tpre_principle ep.
    rewrite H in *.
    rewrite H9 in *.
    eapply ep_annor; eauto.
    +
    inverts red.
    forwards*: flike_int H13.
    forwards*: abs_nlam.
    +
    inverts typ2. 
    inverts tp; try solve[inverts val2].
    inverts val2.
    lets red': red.
    inverts red; try solve[forwards: abs_epre_true2 ep];
    try solve[forwards: absr_epre_true2 ep];
    try solve[
      forwards hh1: flike_int H5;inverts hh1];
    try solve[forwards: abs_nlam].
    *
    inverts H.
    inverts* H2.
    *
    forwards h1: flike_int H12. inverts h1.
    *
    inverts H. inverts H2.
    forwards*: IHep.
    inverts H15; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep];
    try solve[exfalso; apply H11; eauto];
    try solve[
      forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    eapply ep_annor; eauto.
    +
    inverts typ1. inverts H4.  
    inverts tp; try solve[inverts val2].
    *
    inverts red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]; eauto.
    *
    inverts red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]; eauto.
  -
    inverts ep; intros; try solve[inverts val1];
    try solve[inverts typ2; inverts tp];
    try solve[forwards*: abs_nlam].
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    inverts typ1; simpl in *.
    inverts typ2; simpl in *.
    *
    inverts* H2.
    (* *
    inverts typ1. inverts H2.
    inverts H13; try solve[forwards*: abs_epre_true2 ];
    try solve[forwards*: absr_epre_true2]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    inverts H. inverts typ2.
    eapply ep_annol; eauto.
    inverts H5. *)
    *
    inverts val1. 
    inverts* H.
    inverts* H6; simpl in *;try solve[forwards*: abs_epre_true2 ];
    try solve[forwards*: absr_epre_true2]; 
    try solve[forwards*: flike_int];
    try solve[inverts H9];
    try solve[exfalso; apply H7; eauto];
    try solve[simpl in *;inverts H4];
    try solve[forwards*: abs_nlam].
    inverts typ1. inverts H3. inverts H15.
    inverts H3. inverts typ2.
    inverts H17; try solve[forwards*: abs_epre_true2 H0];
    try solve[forwards*: absr_epre_true2 H0];
    try solve[simpl in *;inverts H3].
    inverts H4. simpl in *.
    inverts val2.
    forwards*: tpre_principle H0; simpl in *.
    inverts* H16; simpl in *;try solve[simpl in *;inverts* H3];
    try solve[forwards*: abs_epre_true2 H0];
    try solve[forwards*: absr_epre_true2 H0].
    forwards* h1: principle_inf H4.
    rewrite h1 in *.
    inverts H11; try solve[inverts H3].
    rewrite <- TEMP in *. inverts H3. 
    inverts H2. 
    eapply ep_annor; eauto.
    inverts* H16; simpl in *;try solve[simpl in *;inverts* H3];
    try solve[forwards*: abs_epre_true2 H0];
    try solve[forwards*: absr_epre_true2 H0].
    inverts val2.
    forwards* h1: principle_inf H13.
    forwards*: tpre_principle H0; simpl in *.
    rewrite h1 in *.
    inverts* H16.
    rewrite <- TEMP in *. inverts H18.
    rewrite <- TEMP in *. inverts H18.
    eapply ep_annor; eauto.
    +
    inverts red; simpl in *; subst.
    *
    inverts typ1. inverts H3.
    inverts typ2.
    eapply ep_annol; eauto.
    *
    inverts typ1. inverts H3.
    inverts typ2. inverts H2.
    inverts H13; try solve[forwards*: abs_nlam].
    eapply ep_annol; eauto.
    inverts H12; try solve[forwards*: abs_nlam].
    inverts H0. inverts H1.
    eapply ep_absn; eauto.
    *
    inverts H0. inverts H2. inverts H1.
    inverts typ1. inverts H0. 
    inverts H9; try solve[forwards*: abs_nlam].
    inverts typ2. 
    inverts H9; try solve[forwards*: abs_nlam].
    eapply ep_absn; eauto.
    *
    forwards*: abs_nlam.
    *
    forwards*: abs_nlam.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int].
    *
    inverts H. inverts H3.
    inverts H2. inverts val2.
    forwards*: principle_inf H0.
    forwards*: epre_absr H1.
    *
    inverts H. inverts H3.
    inverts H2. inverts val2.
    forwards*: principle_inf H0.
    forwards*: epre_absr l1 b0 H1.
    inverts H6; try solve[inverts H].
    inverts H3.   
    *
    inverts H. inverts H3. inverts H2.
    inverts val2.
    inverts H8; simpl in *; inverts H3; inverts H0.
    *
    inverts H. inverts H3. inverts H2.
    inverts val2.
    inverts H7; simpl in *; inverts H3; inverts H0.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int].
    *
    inverts typ1.
    forwards*: inference_unique typ2 H0.
    subst*.  inverts H5.
    eapply ep_annol; eauto.
    *
    inverts* H2.
    +
    inverts* red; simpl in *. inverts H8.
    inverts* typ2.
    eapply ep_annol; eauto.
    + 
    inverts* red; simpl in *. inverts H8.
    inverts H7.
    inverts* typ2.
    inverts* tp.
    eapply ep_annol;eauto.
  -
    inductions red; try solve[inverts* tp].
    +
    inverts* tp.
    inverts typ1; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    eapply ep_annol; eauto.
    forwards*: epre_nlam ep.
    +
    inverts* H. inverts tp.
    inverts typ1; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards* h1: epre_nlam ep.
    inverts H1. inverts H5.
    forwards*: Principle_inf H.
    rewrite H5 in *.
    subst*.
    eapply ep_annol; eauto.
    rewrite <- H6 in *; eauto.
    exfalso; apply H0; auto.
    +
    inverts* H.
    +
    inverts* H.
    +
    inverts val1.
    rewrite x in *. inverts H2. 
Qed.


Lemma epre_abs_aux: forall v e t1 t2 l1 b1 ll1 bb1,
  walue v ->
  principal_type v = (t_arrow t1 t2) ->
  epre nil nil v (e_anno (e_abs e ll1 bb1) l1 b1 t_dyn) ->
  epre nil nil v (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t_dyn t_dyn)).
Proof.
  introv val ty ep. gen t1 t2.
  inductions ep; intros;try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep]; 
  try solve[forwards*: flike_int]; simpl in *;eauto; subst.
  -
    inverts H1. inverts* H2.
  -
  inductions ep; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep]; 
  try solve[forwards*: flike_int]; eauto.
  +
  inverts H. inverts H0.
  inverts H14; try solve[forwards*: abs_nlam].
  inverts H1.
  forwards*: IHep.
  inverts* val. 
  eapply ep_annol; eauto.
  inverts val. simpl in *; inverts H13.
  +
  inverts H0. 
  inverts val; try solve[forwards*: abs_epre_true2 ep];
  try solve[forwards*: absr_epre_true2 ep]; 
  try solve[forwards*: flike_int];
  try solve[forwards*: abs_nlam]; simpl in *; subst.
  inverts H. inverts H5.
  inverts H14; try solve[forwards*: abs_nlam]; simpl in *; subst.
  apply ep_annol with (B1 := (t_arrow C D)) 
  (B2:= (t_arrow t_dyn t_dyn)); eauto.
Qed.



Lemma epre_abs: forall v e t1 t2 l1 b1 l2 b2 ll1 bb1,
  walue v ->
  principal_type v = (t_arrow t1 t2) ->
  epre nil nil v (e_anno (e_abs e ll1 bb1) l1 b1 t_dyn) ->
  epre nil nil v (e_anno (e_abs e ll1 bb1) l2 b2 (t_arrow t_dyn t_dyn)).
Proof.
  introv val ty ep.
  forwards*: epre_abs_aux ep.
  forwards*: epre_ignore_label H. 
Qed.



Lemma Flike_add: 
 FLike (principal_type e_add).
Proof.
  unfold FLike;
  splits; try solve[
  unfold not; intros nt; inverts* nt].
  simpl.
  eauto.
Qed.


Lemma Flike_addl: forall i, 
 FLike (principal_type (e_addl i)).
Proof.
  introv.
  unfold FLike;simpl;
  splits; try solve[
  unfold not; intros nt; inverts nt]. 
  auto.
Qed.

Lemma Flike_lit: forall i,
 FLike (principal_type (e_lit i)) ->
 False.
Proof.
  introv fl.
  unfold FLike in *.
  inverts fl. inverts H0. inverts H2.
Qed.

Hint Resolve Flike_add Flike_addl : core.



Lemma epre_wal: forall v1 v2,
 epre nil nil v1 v2 ->
 walue v1 ->
 value v2 ->
 walue v2.
Proof.
  introv ep wal val.
  inductions ep; try solve[inverts* wal;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]];
  try solve[inverts* val].
  -
  inverts* val. inverts* wal;
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  (* inductions ep; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];eauto;
    try solve[forwards*: abs_nlam].
  inductions ep; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];eauto;
    try solve[forwards*: abs_nlam].
  inverts H.  *)
  inverts* wal; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
Qed. 



Lemma epre_walr: forall v1 v2,
 epre nil nil v1 v2 ->
 walue v2 ->
 value v1 ->
 walue v1.
Proof.
  introv ep wal val.
  inductions ep; try solve[inverts* wal;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]];
  try solve[inverts* val].
  -
  inverts* val. inverts* wal;
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  inverts* wal.
  inductions ep; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];eauto;
    try solve[forwards*: abs_nlam].
  inductions ep; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];eauto;
    try solve[forwards*: abs_nlam].
Qed. 




Lemma tdynamic_guarantee: forall e1 e2 e1' A B A1 B1 l1 b1 l2 b2,
 epre nil nil e1 e2 ->  
 tpre A B ->
 walue e1 ->
 walue e2 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 l1 b1 A (e_exp e1') ->
 exists e2', TypedReduce e2 l2 b2 B (e_exp e2') /\ epre nil nil e1' e2'.
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen e1' A B A1 B1.
  inductions ep; intros; 
  try solve[inverts* val1];
  try solve[inverts* val2];
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]; eauto.
  - 
    inverts red; try solve[inverts* H7];
    try solve[inverts* tp].
    +
    inverts* tp.
    exists. splits*.
    +
    inverts* tp.
    exists. splits*.
    +
    forwards*: Flike_lit.
  -
    inductions red; eauto;
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts* tp;inverts* H]; simpl in *; subst.
    +
    inverts H.
    *
    inverts val1; try solve[forwards*: abs_nlam]. 
    inverts val2;
    try solve[forwards*: absr_epre_true2 ep].
    forwards*: tpre_principle ep. rewrite <- H7 in *.
    inverts H6; try solve[inverts* H;inverts* H4]; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    --
      inverts typ2. inverts H5. 
      inverts H15. inverts H5. inverts H17;
      try solve[forwards*: abs_nlam]; simpl in *.
      inverts typ1. inverts H5.
      inverts tp.
      exists. splits.
      apply TReduce_dd; eauto.
      eapply ep_annol; eauto.
      inverts H20; try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int]; simpl in *.
      **
      forwards* h1: principle_inf H5.
      rewrite h1 in *. subst. inverts H4.
      destruct(eq_type C1). destruct(eq_type D1). subst.
      ++
      exists. splits.
      apply TReduce_vany; eauto.
      eapply ep_annol; eauto.
      ++
      exists. splits.
      apply TReduce_dyna; simpl; eauto.
      apply ep_anno;eauto.
      ++
      exists. splits.
      apply TReduce_dyna; simpl; eauto.
      apply ep_anno;eauto.
    --
    inverts H4.
    forwards*: walue_lc H1.
    inverts typ1. inverts typ2. inverts H6. inverts H10.
    inverts H18. inverts H6.
    inverts H19; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    forwards*: Principle_inf H6. rewrite <- H7 in *. subst. 
    inverts* tp.
    exists(e_anno (e_anno v l1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
    destruct(eq_type C2). destruct(eq_type D2). subst.
    assert(TypedReduce (e_anno (e_anno v l1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn)
    l2 b2 
    (principal_type (e_anno v l1 b1 (t_arrow t_dyn t_dyn))) (e_exp (e_anno v l1 b1 (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    exists((e_anno v l1 b1 (t_arrow t_dyn t_dyn))). splits*.
    eapply ep_annol; eauto. 
    exists(e_anno (e_anno v l1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow C2 D2)). splits*.
    apply TReduce_dyna; simpl;eauto.
    apply ep_anno; eauto.
    exists(e_anno (e_anno v l1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow C2 D2)). splits*.
    apply TReduce_dyna; simpl;eauto.
    apply ep_anno; eauto.
    *
    inverts typ1. inverts H.
    inverts typ2. inverts H. 
    inverts val1. inverts val2.
    forwards*: abs_nlam. forwards*: abs_nlam.
    inverts val2; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    inverts H15; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. 
    **
    inverts H12; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    forwards*: Principle_inf H.  rewrite <- H17 in *. subst.
    forwards*: Principle_inf H13. rewrite <- H14 in *. subst.
    inverts tp.
    --
    destruct(eq_type C0). destruct(eq_type D0). subst.
    ++
    exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    ++
    exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
    apply Typ_anno; eauto.
    ++
    exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
    apply Typ_anno; eauto.
    --
    forwards*: epre_sim (t_arrow C0 D0) (t_arrow C3 D3) H2.
    exists(e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow C3 D3)).
    splits*.
    +
    inverts tp.
    inverts val1; try solve[forwards*: abs_nlam]; try solve[inverts H1].
    inverts H1.
    inverts typ1. inverts H1. inverts typ2. inverts H1. inverts* val2; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep].
    inverts H. inverts H11. inverts H16. 
    exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    forwards*: walue_lc H13.
    exists(e_anno e2 l3 b3 t_dyn). splits*.
    +
    inverts tp. inverts* H.
    forwards*: epre_lc ep.
    +
    inverts typ1. inverts H2. inverts typ2. inverts H2.
    inverts tp.
    forwards*: flike_tpre H H1.
    lets(t1&t2&eq1&eq2): H2. subst.
    inverts eq2.
    *
    forwards*: epre_nlam ep.
    inverts val2; try solve[forwards*: abs_nlam]. 
    inverts val1; try solve[forwards*: abs_nlam].
    forwards*: tpre_principle ep.
    rewrite <- H18 in *.
    inverts H13; inverts* H8;inverts* H10; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    *** 
      exists. splits*.
      eapply ep_annol; eauto.
    ***
    inverts H14. inverts H8.
    forwards*: walue_lc H9.
    exists(e_anno (e_anno v l1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
    apply ep_anno; eauto.
    eapply ep_annol; eauto.
    inverts H11; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: Principle_inf H14. rewrite <- H18 in *. subst.
    eapply ep_annol ; eauto.
    *
    lets(t3&t4&eq2): H7. subst.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply ep_anno; eauto. 
    eapply ep_annol; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    +
    inductions ep; try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int];
      try solve[forwards*: abs_nlam].
    +
    inductions ep; try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int];
      try solve[forwards*: abs_nlam].
    +
    inverts H.
    inverts typ1. inverts H. inverts typ2. inverts H. 
    inverts val1;try solve[forwards*: abs_nlam].
    forwards*: epre_nlam ep. 
    inverts val2;try solve[forwards*: abs_nlam].
    forwards* h1: flike_tpre tp H3.
    lets(t1&t2&eq1&eq2): h1. subst.
    forwards*: tpre_principle ep.
    assert(value e1). eauto.
    assert(value e2). eauto.
    inverts H10; inverts H9;inverts* H2; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]; simpl in *;
    try solve[exfalso; apply H1; eauto];
    try solve[forwards*: abs_nlam].
    inverts H8. rewrite <- H10 in H13. inverts H13.
    inverts H12. inverts H2.
    assert(value e2). eauto.
    assert(value v). eauto.
    inverts H2; inverts H10;inverts* H13; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    inverts eq2; subst.
    *
    forwards*: value_lc H23.
    exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
    *
    lets(t3&t4&eq3): H2. subst.
    inverts H15. inverts H10.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    assert(TypedReduce (e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn) l2 b2
    (principal_type (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn))) (e_exp (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    exists((e_anno v0 p1 b1 (t_arrow t_dyn t_dyn))). splits*.
    --
    exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow t3 t4)).
    splits*.
    apply TReduce_dyna; simpl; eauto.
    --
    exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow t3 t4)).
    splits*.
    apply TReduce_dyna; simpl; eauto.
    +
    inverts H. 
    forwards*: epre_nlam ep.
    assert(value (e_anno e2 l3 b3 t_dyn)). auto.
    assert(value (e_anno e1' l0 b0 t_dyn)). auto.
    inverts H2; try solve[forwards*: abs_nlam].
    inverts H3; try solve[forwards*: abs_nlam].
    forwards*: tpre_principle ep.
    inverts H9; simpl in *;try solve[inverts* H5].
    *
    inverts H8; try solve[inverts* H6; inverts* H2]. 
    inverts tp.
    assert(t_int = (principal_type (e_lit i0))). simpl; auto.
    rewrite H3.
    exists((e_lit i0)). splits*.
    exists(e_anno (e_lit i0) l3 b3 t_dyn). splits*.
    *
    inverts H8; simpl in *;try solve[inverts* H;inverts* H2];
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[exfalso; apply H0; eauto].
    *
    inverts tp.
    forwards*: value_lc H3.
    inverts typ1. inverts H9. 
    inverts typ2. inverts H9.
    inverts H18. inverts H9.
    inverts H21; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    inverts H5.
    forwards*: Principle_inf H9. rewrite H5 in *.
    exists(e_anno e2 l3 b3 t_dyn). splits*.
    
    inverts typ1. inverts H7. inverts H19. 
    inverts H8; simpl in *;try solve[inverts* H2;inverts* H6];
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    inverts* H5. inverts* H6. inverts H10. inverts H12. 
    assert((t_arrow t_dyn t_dyn) = (principal_type (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)))). simpl; auto.
    assert(TypedReduce (e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn)
    l2 b2 (principal_type (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)))
    (e_exp (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    exists((e_anno v0 p1 b1 (t_arrow t_dyn t_dyn))).
    splits*.
  -
    forwards* h1: dmatch_tpre2 H3.
    inverts h1.
    inverts H1.
    +
    inverts H3. inverts H2.
    *
    destruct(A0).
    --
    inverts* red; try solve[forwards*: flike_int H10];
    try solve[forwards*: abs_nlam].
    --
    inverts* red; simpl in *; subst*.
    inverts H10.
    inverts tp.
    ++
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    inverts typ1. inverts H1.
    inverts typ2. inverts H1.
    exists. splits.
    apply TReduce_dd; eauto.
    eapply ep_annol;eauto.
    ++
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    inverts typ1. inverts H1.
    inverts typ2. inverts H1.
    inverts H19; try solve[forwards*: abs_nlam].
    destruct(eq_type C0). destruct(eq_type D0). subst.
    ---
    pick fresh x.
    exists. splits.
    apply TReduce_absd;eauto.
    eapply ep_annol with (B2:= (t_arrow t_dyn t_dyn)); auto.
    eapply Typ_anno; eauto.
    forwards*: H x.
    ---
    exists. splits.
    eapply TReduce_adyn;eauto.
    apply ep_anno; eauto.
    ---
    exists. splits.
    eapply TReduce_adyn;eauto.
    apply ep_anno; eauto.
    --
    inverts* tp.
    inverts* val2; try solve[inverts H5].
    inverts* red; simpl in *;try solve[inverts H8];
    try solve[inverts H8;exfalso; apply H1; auto];
    try solve[inverts H11;exfalso; apply H1; auto].
    ++
    inverts H6.
    inverts typ1. inverts H1. inverts H13; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H1. inverts H16; try solve[forwards*: abs_nlam].
    exists. splits.
    apply TReduce_dd; eauto.
    eapply ep_annol;eauto.
    ++
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    inverts typ1. inverts H1.
    inverts typ2. inverts H1.
    exists. splits.
    apply TReduce_dd; eauto.
    eapply ep_annol;eauto.
    *
    inverts H2.
    inverts red; simpl in *;subst*;try solve[forwards*: abs_nlam].
    ++ 
    inverts H11.
    inverts tp.
    --
    inverts typ1. inverts H1. inverts H15; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H1. inverts H18; try solve[forwards*: abs_nlam].
    destruct(eq_type B1). destruct(eq_type B2). subst.
    ---
    exists.
    splits*.
    ---
    exists.
    splits.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor;eauto.
    ---
    exists.
    splits.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor;eauto.
    --
    assert(tpre (t_arrow C D) (t_arrow B1 B2)); auto.
    assert(tpre (t_arrow A B) (t_arrow C0 D0)); auto.
    forwards*: epre_sim H2 H1 H3. 
    exists. splits*.
    ++
    inverts tp. inverts H10. inverts H7. inverts H9.
    exists. splits.
    eapply TReduce_v; eauto.
    eapply ep_anno; eauto.
    ++
    inverts typ1. inverts H1. inverts H15; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H1. inverts H18; try solve[forwards*: abs_nlam].
    inverts tp.
    destruct(eq_type B1). destruct(eq_type B2). subst.
    ---
    exists.
    splits*.
    eapply ep_anno; eauto.
    eapply ep_annol; eauto.
    ---
    exists.
    splits.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ---
    exists.
    splits.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    +
    inverts H2. inverts H3.
    destruct(A0).
    *
    inverts* red; try solve[forwards*: flike_int H12];
    try solve[forwards*: abs_nlam].
    *
    inverts* red; try solve[forwards*: flike_int H12];
    try solve[forwards*: abs_nlam]; try solve[simpl; inverts H11].
    ++
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    inverts typ1. inverts H1. inverts H15; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H1. inverts H18; try solve[forwards*: abs_nlam].
    inverts tp.
    exists. splits.
    apply TReduce_dd; eauto.
    eapply ep_annol;eauto.
    destruct(eq_type C ). destruct(eq_type D). subst.
    ---
    exists.
    splits*.
    eapply ep_annol; eauto.
    ---
    exists.
    splits.
    apply TReduce_adyn; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ---
    exists.
    splits.
    apply TReduce_adyn; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ++
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    inverts typ1. inverts H1. inverts H14; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H1. inverts H17; try solve[forwards*: abs_nlam].
    inverts tp.
    exists. splits.
    apply TReduce_dd; eauto.
    eapply ep_absn;eauto.
    inverts H13. inverts H15.
    exists.
    splits*.
    *
    inverts* tp.
    inverts* val2; try solve[inverts H6].
    inverts* red; simpl in *;try solve[inverts H8];
    try solve[inverts H8;exfalso; apply H1; auto];
    try solve[inverts H13;exfalso; apply H1; auto].
    inverts H14.
  -
    inverts typ2. inverts H4. 
    assert(value (e_anno e2 l b A2)); auto.
    inverts H4.
    +
    inverts H1.
    assert(value e1); auto. 
    inverts H1; try solve[inverts H]; 
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    inverts H.
    inverts* red.
    * simpl in *. inverts H18.
    inverts tp.
    --
    destruct(eq_type A). destruct(eq_type B3). subst.
    ++
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    ++
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor; eauto.
    eapply ep_anno; eauto.
    ++
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_annor; eauto.
    --
    forwards*: Principle_inf H0.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: Principle_inf H8.
    rewrite H in *. inverts H13. 
    forwards*: epre_sim (t_arrow A B3) (t_arrow C2 D2) H1.
    exists(e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow C2 D2)).
    splits*.
    apply ep_anno; eauto.
    *
    inverts H17.
    inverts tp. inverts H10. inverts* H11.
    exists((e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
    splits*.
    *
    inverts tp; simpl in *.
    destruct(eq_type A). destruct(eq_type B3). subst.
    -- 
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    --
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_anno; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_anno; eauto.
    *
    inverts red; try solve[inverts H15].
    --
    inverts H.
    inverts tp; simpl in *.
    ++
    destruct(eq_type A). destruct(eq_type B3). subst.
    --- 
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    ---
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. inverts H16.
    forwards*: inference_unique H0 H7. inverts H13.
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_anno; eauto.
    ---
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. inverts H16.
    forwards*: inference_unique H0 H1. inverts H13.
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_anno; eauto.
    ++
    inverts H16.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[simpl; inverts* H15]. 
    forwards*: inference_unique H0 H. subst.
    assert(tpre (t_arrow A3 B1) (t_arrow C1 D1) ); auto.
    forwards*: epre_sim ((t_arrow A B3)) H4 H13.
    exists. splits.
    eapply TReduce_abs; eauto.
    eapply ep_anno; eauto.
    --
    inverts tp.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: inference_unique H0 H1. subst.
    destruct(eq_type A). destruct(eq_type B3). subst.
    --- 
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    ---
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ---
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    *
    inverts red; try solve[inverts H15].
    --
    inverts H.
    inverts tp; simpl in *.
    ++
    destruct(eq_type A). destruct(eq_type B3). subst.
    --- 
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    ---
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. inverts H16.
    forwards*: inference_unique H0 H7. inverts H13.
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_anno; eauto.
    ---
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. inverts H16.
    forwards*: inference_unique H0 H1. inverts H13.
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_anno; eauto.
    ++
    inverts H16.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]. 
    forwards*: inference_unique H0 H. subst.
    assert(tpre (t_arrow A3 B1) (t_arrow C1 D1) ); auto.
    forwards*: epre_sim ((t_arrow A B3)) H4 H13.
    exists. splits.
    eapply TReduce_abs; eauto.
    eapply ep_anno; eauto.
    --
    inverts tp.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: inference_unique H0 H1. subst.
    destruct(eq_type A). destruct(eq_type B3). subst.
    --- 
    exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    ---
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ---
    exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    +
    forwards*: epre_wal ep.
    forwards*: IHep red tp.
    lets(v2'&rred&eep): H7.
    forwards*: Tred_value red.
    inverts typ1; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    forwards*: TypedReduce_sim red.
    inverts H13;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    forwards*: TypedReduce_sim red.
    forwards*: TypedReduce_sim rred.
    forwards*: TypedReduce_preservation red.
    forwards*: TypedReduce_preservation rred.
    forwards*: tred_dyn_same eep rred.
  -   
    inverts typ1. inverts H4.
    inductions red;simpl in *;subst;
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    +
    assert(value (e_anno e1 l b (t_arrow C D))); auto.
    inverts H4.
    inverts tp.
    *
    forwards*: epre_value_arrow ep.
    forwards*: epre_nlamr ep. 
    inverts H4.
    lets(vv2&ll1&bb1&eq1&eq2): H8. subst.
    assert(value (e_anno vv2 ll1 bb1 t_dyn)); auto.
    inverts H4.
    forwards*: value_lc H16.
    inverts H0.
    exists(e_anno vv2 ll1 bb1 t_dyn). splits*.
    eapply ep_annol; eauto.
    lets(t3&t4&eq3): H8. subst.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e2) l2 b2 t_dyn). splits*.
    eapply TReduce_v; eauto.
    rewrite eq3; eauto.
    --
    exists(e_anno (e_anno (e2) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    rewrite eq3; eauto.
    eapply ep_anno; eauto.
    --
    exists(e_anno (e_anno (e2) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    rewrite eq3; eauto.
    eapply ep_anno; eauto.
    *
    forwards*: epre_value_arrow ep.
    forwards*: epre_nlamr ep. 
    inverts H4.
    lets(vv2&ll&bb&eq1&eq2): H8. subst.
    ++
    assert(value (e_anno vv2 ll bb t_dyn)); auto.
    inverts H4.
    inverts typ2. inverts H4.
    inverts H24; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    forwards: value_group H10.
    forwards*: principle_inf H.
    rewrite H19 in *. inverts H15.
    inverts H17; try solve[inverts H15; inverts H17;inverts H15;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int] ].
    forwards*: epre_abs ll bb ll bb ep.
    destruct(eq_type C1). destruct(eq_type D1). subst.
    --
    exists. splits*.
    eapply ep_annol; eauto.
    eapply ep_annol; eauto.
    --
    exists. splits*.
    eapply ep_anno; eauto.
    eapply ep_annol; eauto.
    --
    exists. splits*.
    eapply ep_anno; eauto.
    eapply ep_annol; eauto.
    ***
    inverts H13; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: remove_left_dyn ep.
    forwards*: Principle_inf H20.
    forwards*: Principle_inf H4.
    rewrite eq2 in *. subst.
    rewrite <- H15 in *.
    destruct(eq_type C1). destruct(eq_type D1). subst.
    --
    exists(vv2). splits*.
    rewrite <- eq2.
    apply TReduce_vany; eauto.
    eapply ep_annol; eauto.
    inverts* H13.
    lets(var1&var2&var3&hh1):H23.
    inverts hh1; try solve[inverts H19].
    --
    exists(e_anno (vv2 ) l2 b2 (t_arrow C1 D1)). splits*.
    apply TReduce_dyna; simpl; eauto.
    rewrite eq2; auto.
    apply ep_anno; eauto.
    inverts* H13; try solve[inverts H25; inverts H19].
    lets(var1&var2&var3&hh1):H25.
    inverts hh1.
    inverts H19.
    --
    exists(e_anno (vv2 ) l2 b2 (t_arrow C1 D1)). splits*.
    apply TReduce_dyna; simpl; eauto.
    rewrite eq2; auto.
    apply ep_anno; eauto.
    inverts* H13; try solve[lets(var1&var2&var3&hh1):H24;inverts hh1; try solve[forwards*: abs_nlam]].
    ++
    lets(t3&t4&eq3): H8. subst.
    forwards*: epre_sim (t_arrow C1 D1) H5 H1.
    forwards*: principle_inf H0.
    rewrite eq3 in *. subst.
    exists(e_anno (e2) l2 b2 (t_arrow C1 D1)).
    splits*.
    +
    assert(value (e_anno e1 l b A2));auto.
    inverts tp. inverts H4;inverts H7.
    forwards*: Principle_inf H. 
    rewrite <- H14 in *. subst.
    inverts H9; inverts H; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    *
    inverts H1.
    --
    assert(value e2); auto.
    inverts H; inverts H0.
    forwards*: value_lc H4.
    exists(e_anno v0 p1 b3 t_dyn). splits*.
    eapply ep_annol; eauto.
    --
    inverts H13. inverts H.
    inverts H9. inverts H12.
    forwards*: Principle_inf H0.
    exists(e_anno e2 l2 b2 t_dyn). splits*.
    apply  TReduce_v; eauto.
    rewrite H; auto.
    *
    inverts H1.
    assert(value e2); auto.
    inverts H; inverts* H0.
    exists. splits*.
    eapply ep_annol; eauto.
    inverts H7. inverts H10.
    forwards*: principle_inf H0.
    exists. splits.
    eapply TReduce_v; eauto.
    rewrite H; eauto.
    eapply ep_annol; eauto.
    *
    inverts H1.
    assert(value e2); auto.
    inverts H; inverts* H0.
    exists. splits*.
    eapply ep_annol; eauto.
    inverts H9. inverts H7.
    forwards*: principle_inf H0.
    exists. splits.
    eapply TReduce_v; eauto.
    rewrite H; eauto.
    eapply ep_annol; eauto.
    +
    inverts H1. inverts tp.
    assert(value (e_anno e1 l b t_dyn)).
    auto.
    assert(value e2).
    auto.
    inverts H1.
    inverts H7; inverts H0.
    forwards*: value_lc H8.
    exists. splits*.
    +
    inverts tp.
    forwards*: flike_tpre H1 H4.
    lets(t1&t2&eq1&eq2): H7. subst.
    inverts H1.
    * 
    assert(value e2).
    auto.
    inverts H1; inverts H0.
    forwards*: value_lc H9.
    exists(e_anno v p0 b1 t_dyn). splits*.
    eapply ep_annol; eauto.
    eapply ep_annol; eauto.
    *
    inverts eq2; try solve[inverts H1].
    lets(t3&t4&eq3): H1. inverts eq3.
    assert(value e2).
    auto.
    inverts H8; inverts H0; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply ep_anno; eauto. 
    eapply ep_annol; eauto.
    --
    exists(e_anno (e_anno (e_anno v p0 b1 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_anno; eauto.
    apply ep_anno; eauto.  
    --
    exists(e_anno (e_anno (e_anno v p0 b1 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_anno; eauto.
    apply ep_anno; eauto.
    --
    exists. splits.
    eapply TReduce_anyd; eauto.
    eapply ep_anno; eauto.
    eapply ep_anno; eauto.
    --
    exists. splits.
    eapply TReduce_anyd; eauto.
    eapply ep_anno; eauto.
    eapply ep_anno; eauto.
    +
    assert(value (e_anno e1 l b t_dyn)); auto.
    assert(value e2); auto.
    inverts H9. inverts H1.
    inverts H10; inverts H0.
    forwards*: flike_tpre tp H6.
    lets(t1&t2&eq1&eq2): H0. 
    inverts eq2; subst.
    *
    forwards*: value_lc H9.
    exists(e_anno v p0 b1 t_dyn). splits*.
    *
    lets(t3&t4&eq3): H10. inverts eq3.
    inverts H16; inverts H5; inverts H14;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    forwards*: tpre_v_dyn_fun ep.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    inverts H12; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    inverts H.
    forwards*: epre_abs p0 b1  p0 b1 ep.
    forwards*: value_group H11.
    inverts* H. 
    lets(var1&var2&var3&hh1):H12. inverts hh1. inverts* H9.
    exists. splits*.
    eapply ep_annol; eauto.
    ***
    forwards*: Principle_inf H14.
    rewrite H5 in *. subst.
    assert(TypedReduce (e_anno v p0 b1 t_dyn) l2 b2 (principal_type (v)) (e_exp v)).
    apply TReduce_vany; eauto.
    rewrite H5 in *.
    forwards*: remove_left_dyn ep.
    inverts H. inverts* H18.
    exists v. splits*.
    lets(var1&var2&var3&hh1):H. inverts hh1.
    inverts H17.
    --
    inverts H13. inverts H17.
    inverts typ2. inverts H13.
    inverts H30; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    inverts H27.
    forwards*: epre_abs p0 b1 p0 b1 ep.
    exists. splits*.
    forwards*: epre_abs p0 b1 p0 b1 ep.
    forwards*: value_group H11.
    inverts* H26. 
    lets(var1&var2&var3&hh1):H27. inverts* hh1.
    exists. splits*.
    ***
    forwards*: remove_left_dyn ep.
    inverts* H25.
    exists(e_anno v l2 b2 (t_arrow t3 t4)). splits.
    apply TReduce_dyna; eauto.
    rewrite H5; eauto.
    eapply ep_anno; eauto.
    lets(var1&var2&var3&hh1):H26. inverts hh1.
     inverts H24.
    --
    inverts H13. inverts H16.
    inverts typ2. inverts H13.
    inverts H29; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    inverts H26.
    forwards*: epre_abs p0 b1 p0 b1 ep.
    exists. splits*.
    forwards*: epre_abs p0 b1 p0 b1 ep.
    forwards*: value_group H11.
    inverts* H25.
    lets(var1&var2&var3&hh1):H26. inverts* hh1.
    exists. splits*.
    ***
    forwards*: remove_left_dyn ep.
    exists(e_anno v l2 b2 (t_arrow t3 t4)). splits.
    apply TReduce_dyna; eauto.
    rewrite H5; eauto.
    eapply ep_anno; eauto.
    inverts* H24.
    lets(var1&var2&var3&hh1):H25. inverts* hh1.
    inverts H23.
    +
    assert(value (e_anno e1' l b t_dyn)); auto.
    assert(value e2); auto.
    inverts H7. inverts H1.
    inverts H8; inverts H0.
    inverts H14; inverts H11; simpl in *;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    *
    forwards*: tpre_v_dyn_int ep.
    *
    forwards*: tpre_v_dyn_fun ep.
    inverts tp.
    forwards*: value_lc H7.
    inverts H13. inverts H11.
    inverts H10; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    ***
    inverts H14.
    inverts H16.
    forwards*: epre_abs p0 b1 p0 b1 ep.
    forwards*: value_group H0.
    inverts* H10. 
    lets(var1&var2&var3&hh1):H13. inverts* hh1.
    ***
    assert(TypedReduce (e_anno v p0 b1 t_dyn) l2 b2 (principal_type v) (e_exp v)).
    apply TReduce_vany; eauto.
    inverts H14. inverts H16. 
    rewrite H9 in H10; auto.
    forwards*: remove_left_dyn ep.
    inverts* H14.
    lets(var1&var2&var3&hh1):H16. inverts hh1.
    inverts H17.
  -
    inverts red; try solve[inverts* H4]; simpl in *.
    +
    simpl in *. inverts H7.
    inverts tp.
    exists. splits.
    apply TReduce_anyd; eauto.
    eapply ep_annor; eauto.
    assert(tpre (t_arrow t_int (t_arrow t_int t_int)) (t_arrow t_int (t_arrow t_int t_int))); auto.
    assert(tpre (t_arrow A0 B0)  (t_arrow C D)); auto.
    forwards*: epre_sim H2 H1 H3.
    exists. splits.
    eapply TReduce_abs; eauto.
    eapply ep_anno;eauto. 
    +
    simpl in *.
    inverts tp.
    exists. splits.
    apply TReduce_anyd;eauto.
    eapply ep_annol; eauto.
    apply Typ_anno;eauto.
    eapply Typ_sim;eauto.
    eapply ep_annor;eauto.
    eapply ep_annor;eauto.
    +
    simpl in *.
    inverts tp.
    exists. splits.
    apply TReduce_anyd;eauto.
    eapply ep_annol; eauto.
    apply Typ_anno;eauto.
    eapply Typ_sim;eauto.
    eapply ep_annor;eauto.
  -
    inverts red; try solve[inverts* H4].
    +
    simpl in *. inverts H7.
    inverts tp.
    exists. splits.
    apply TReduce_anyd; eauto.
    eapply ep_annor; eauto.
    assert(tpre ((t_arrow t_int t_int)) ((t_arrow t_int t_int))); auto.
    assert(tpre (t_arrow A0 B0)  (t_arrow C D)); auto.
    forwards*: epre_sim H2 H1 H3.
    exists. splits.
    eapply TReduce_abs;eauto.
    eapply ep_anno;eauto.
    +
    inverts tp.
    exists. splits.
    apply TReduce_anyd; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor;eauto.
    +
    inverts tp.
    exists. splits.
    apply TReduce_anyd; eauto.
    eapply ep_anno; eauto.
Qed.



Lemma tdynamic_guaranteer: forall e1 e2 e2' A B l1 b1 l2 b2 ,
 epre nil nil e1 e2 ->  
 tpre A B ->
 walue e1 ->
 walue e2 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B -> 
 TypedReduce e2 l1 b1 B (e_exp e2') ->
 (exists e1', TypedReduce e1 l2 b2 A (e_exp e1') /\ epre nil nil e1' e2') \/
 TypedReduce e1 l2 b2 A (e_blame l2 b2).
Proof.
  introv ep tp val1 val2 typ1 typ2 red. 
  forwards*: TypedReduce_progress typ1.
  inverts H. destruct x; eauto.
  forwards*: tdynamic_guarantee ep tp H0.
  lets(ee2&tred&epp):H.
  forwards*: TypedReduce_unique red tred.
  inverts* H1.
  inverts* H0.
Qed.


Lemma epre_lit_false: forall v1 t1 t2 i l b,
 value v1 ->
 principal_type v1 = (t_arrow t1 t2) ->
 epre nil nil (v1 ) (e_anno (e_lit i) l b t_dyn) ->
 False.
Proof.
  introv val ty ep. gen t1 t2.
  inductions ep; intros; simpl in *;eauto.
  -
  subst.
  inverts val.
  forwards*: tpre_principle ep; simpl in *.
  rewrite <- H7 in *.
  inverts H1.
  -
  forwards*: tpre_principle ep; simpl in *.
  rewrite ty in *.
  inverts H4.
  -
  subst.
  inverts val.
  forwards*: IHep.
Qed.



Lemma tred_right: forall v1 v2 t1 t l b,
 Typing nil v1 Inf t1 ->
 Typing nil v2 Chk t ->
 value v1 ->
 walue v2 ->
 epre nil nil v1 v2 ->
 tpre t1 t ->
 exists v2', TypedReduce v2 l b t (e_exp v2') /\
 epre nil nil v1 v2'.
Proof.
  introv typ1 typ2 val1 val2 ep tp.
  destruct t.
  -
    inverts ep; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1].
    +
    inverts typ2. inverts H5.
    inverts val2; try solve[inverts H0];
    try solve[inverts H6];
    try solve[forwards*: abs_nlam];
    try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1].
    inverts tp.
    inverts val1; inverts typ1.
    forwards*: tpre_principle H1; simpl in *.
    inverts H12; simpl in *; inverts* H5;inverts H9.
    exists(e_lit i0). splits*.
    apply TReduce_vany; eauto.
  -
     lets ep': ep.
    inverts ep; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1];
    try solve[inverts val2].
    +
    inverts tp. inverts typ1. inverts val1.
    inverts val2.
    *
      inverts typ2. inverts H2.
      inverts H17; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
      try solve[forwards*: abs_nlam].
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      exists.
      splits*.
      ---
      exists.
      splits*.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
      ---
      exists.
      splits*.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    *
      inverts typ2. inverts H2.
      exists. splits.
      eapply TReduce_abs; eauto.
      eapply ep_annor; eauto.
    *
    inverts typ2. inverts H2.
    exists(e_anno (e_anno e2 l2 b2 (t_arrow A B1) ) l b (t_arrow t2 t3)).
    splits*.
    *
    forwards*: tpre_principle H0.
    rewrite <- H11 in *.
    inverts H12; simpl in *; inverts H2; inverts H7;
    try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    +++
    inverts typ2. inverts H2. inverts H19. 
    inverts H10; try solve[forwards*: abs_epre_true2 H0];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    inverts H2.
    forwards*: principle_inf H14.
    rewrite H2 in *. inverts H11.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists.
    splits.
    eapply TReduce_vany; eauto.
    eapply ep_annol; eauto.
    ---
    exists.
    splits.
    eapply TReduce_dyna; simpl; eauto.
    eapply ep_annor; eauto.
    ---
    exists.
    splits.
    eapply TReduce_dyna; simpl; eauto.
    eapply ep_annor; eauto.
    +++
    inverts typ2. inverts H2. inverts H20.
    inverts H2.
    inverts H10; try solve[forwards*: abs_epre_true2 H0];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int]; simpl in *.
    forwards* h1: Principle_inf H2.
    rewrite h1 in *. inverts H11.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists( (e_anno v l3 b0 (t_arrow t_dyn t_dyn))).
    splits*.
    apply  TReduce_vany;eauto.
    ---
    exists.
    splits.
    apply TReduce_dyna; simpl;eauto.
    eapply ep_anno; eauto.
    ---
    exists.
    splits.
    apply TReduce_dyna; simpl;eauto.
    eapply ep_anno; eauto.
    +
    inverts tp.
    inverts typ1. inverts H0.
    inverts H1.
    --
    inverts typ2. inverts H0.
    exists. splits*.
    --
    inverts H11; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H0. 
    inverts H13; try solve[forwards*: abs_nlam].
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists.
    splits*.
    ---
    exists.
    splits.
    apply TReduce_adyn; simpl;eauto.
    eapply ep_annor; eauto.
    ---
    exists.
    splits.
    apply TReduce_adyn; simpl;eauto.
    eapply ep_annor; eauto.
    +
    inverts tp. inverts typ2. inverts H5.
    inverts val2; try solve[inverts H0];
    try solve[inverts H4];
    try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1].
    *
    inverts H16.
    forwards*: epre_nlam H1.
    inverts H5.
    forwards*: Principle_inf H0.
    rewrite <- H14 in *.
    subst*.
    forwards*: Principle_inf H.
    forwards*: Principle_inf typ1.
    rewrite H13 in H15. 
    forwards*: Principle_inf H5.
    rewrite <- H16 in *. subst.
    rewrite H15 in *.
    exists((e_anno (e_anno e2 l1 b0 (t_arrow A B0)) l b (t_arrow t2 t3))).
    splits.
    apply TReduce_abs with (C:= A) (D := B0).
    auto. simpl. reflexivity.
    apply ep_annor with (B1:= (t_arrow A0 B))
    (B2:=(t_arrow A B0) ).
    apply H.
    apply Typ_anno.
    rewrite <- H14 in *.
    apply Typ_sim with (A:= (t_arrow C D)).
    apply H5.
    auto.
    auto.
    auto.
    auto.
    auto.
    auto.
    *
    forwards*: tpre_principle H1.
    forwards*: Principle_inf typ1.
    rewrite H10 in *.
    inverts H14; simpl in *; 
    inverts H5; inverts H11; try solve[].
    ***
    forwards*: principle_inf H.
    rewrite H5 in *. subst.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists.
    splits*.
    apply  TReduce_vany;eauto.
    ---
    exists. splits.
    eapply TReduce_dyna; simpl;eauto.
    eapply ep_annor; eauto.
    ---
    exists. splits.
    eapply TReduce_dyna; simpl;eauto.
    eapply ep_annor; eauto.
    ***
    forwards*: Principle_inf H.
    rewrite H5 in H10. rewrite H10 in H.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    inverts H0. 
    exists( (e_anno v l2 b1 (t_arrow t_dyn t_dyn)) ).
    splits*.
    apply  TReduce_vany;eauto.
    ---
    inverts H0.
    exists(e_anno (e_anno v l2 b1 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    ---
    inverts H0.
    exists(e_anno (e_anno v l2 b1 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    +
    inverts tp. inverts typ1.
    inverts typ2; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts val2].
    inverts val1.
    forwards*: tpre_principle H1.
    rewrite <- H17 in *.
    inverts H13; try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
    ***
    forwards*: Principle_inf H11.
    rewrite H13 in *. subst*.
    inverts val2; simpl in *;inverts H10; try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    *
    forwards*: epre_abs l2 b1 l2 b1 H1.
    forwards*: value_group H12.
    inverts* H10.
    lets(var1&var2&var3&hh1):H17. inverts* hh1.
    try solve[inverts H15].
    forwards*: principle_inf H.
    rewrite H17 in *. subst.
    inverts H5. inverts H23; try solve[forwards*: abs_nlam].
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists.
    splits*.
    eapply ep_annol; eauto.
    ---
    exists. splits.
    eapply  TReduce_adyn; simpl;eauto.
    eapply ep_annor; eauto.
    eapply ep_annol; eauto.
    ---
    exists. splits.
    eapply  TReduce_adyn; simpl;eauto.
    eapply ep_annor; eauto.
    eapply ep_annol; eauto.
    *
    inverts H5.  
    forwards*: principle_inf H.
    rewrite H5 in *. subst.
    exists. splits*.
    *
    inverts H5.
    exists(e_anno (e_anno v l2 b1 (t_arrow A1 B0)) l b (t_arrow t2 t3)).
    splits*.
    *
    inverts H12; simpl in *; inverts H13; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H];
    try solve[forwards*: abs_nlam].
    ++ 
    inverts H17; inverts H16;try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
    --
    forwards*: epre_lit_false H1.
    --
    inverts H. inverts H0. inverts H21. inverts H.
    inverts H24; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H];
    try solve[forwards*: abs_nlam].
    forwards*: remove_left_dyn H1.
    inverts H;try solve[lets(var1&var2&var3&hh1):H16; inverts hh1;inverts H].
    inverts H5. inverts H25. inverts H.
    inverts H27; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H];
    try solve[forwards*: abs_nlam].
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists.
    splits.
    eapply  TReduce_vany ; eauto.
    eapply ep_annol; eauto.
    ---
    exists. splits.
    eapply  TReduce_dyna; simpl;eauto.
    eapply ep_anno; eauto.
    ---
    exists. splits.
    eapply  TReduce_dyna; simpl;eauto.
    eapply ep_anno; eauto.
    --
    forwards*: remove_left_dyn H1. 
    inverts H16; try solve[lets(var1&var2&var3&hh1):H17; inverts* hh1;inverts H16].
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    inverts H0. inverts H24. inverts H0.
    forwards*: Principle_inf H; simpl in *.
    rewrite <- H0 in *. inverts H.
    inverts H5. inverts H27. inverts H.
    exists( (e_anno v1 l3 b3 (t_arrow t_dyn t_dyn)) ).
    splits*.
    apply  TReduce_vany;eauto.
    ---
    exists(e_anno (e_anno v1 l3 b3 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    ---
    exists(e_anno (e_anno v1 l3 b3 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    ++
      inverts H5. inverts H0.
      inverts H21; try solve[inverts H17].
      inverts H17;inverts H16.
      --
      forwards*: epre_lit_false H1.
      --
      inverts H. inverts H0. inverts H22; try solve[inverts H];
      try solve[forwards*: abs_nlam].
      forwards*: remove_left_dyn H1.
      inverts H;try solve[lets(var1&var2&var3&hh1):H0; inverts hh1;inverts H].
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      exists.
      splits.
      eapply  TReduce_vany ; eauto.
      eapply ep_annol; eauto.
      ---
      exists. splits.
      eapply  TReduce_dyna; simpl;eauto.
      eapply ep_anno; eauto.
      ---
      exists. splits.
      eapply  TReduce_dyna; simpl;eauto.
      eapply ep_anno; eauto.
      --
      forwards*: remove_left_dyn H1. 
      inverts H16; try solve[lets(var1&var2&var3&hh1):H17; inverts hh1;inverts H16].
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      inverts H0. 
      exists( (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) ).
      splits*.
      apply  TReduce_vany;eauto.
      ---
      exists(e_anno (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
      splits*.
      apply TReduce_dyna; simpl;eauto.
      ---
      exists(e_anno (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
      splits*.
      apply TReduce_dyna; simpl;eauto.
    ++
      inverts H5. inverts H0.
      inverts H21; try solve[inverts H17].
      inverts H17;inverts H16.
      --
      forwards*: epre_lit_false H1.
      --
      inverts H. inverts H0. inverts H22; try solve[inverts H];
      try solve[forwards*: abs_nlam].
      forwards*: remove_left_dyn H1.
      inverts H;try solve[lets(var1&var2&var3&hh1):H0; inverts hh1;inverts H].
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      exists.
      splits.
      eapply  TReduce_vany ; eauto.
      eapply ep_annol; eauto.
      ---
      exists. splits.
      eapply  TReduce_dyna; simpl;eauto.
      eapply ep_anno; eauto.
      ---
      exists. splits.
      eapply  TReduce_dyna; simpl;eauto.
      eapply ep_anno; eauto.
      --
      forwards*: remove_left_dyn H1. 
      inverts H16; try solve[lets(var1&var2&var3&hh1):H17; inverts hh1;inverts H16].
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      inverts H0. 
      exists( (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) ).
      splits*.
      apply  TReduce_vany;eauto.
      ---
      exists(e_anno (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
      splits*.
      apply TReduce_dyna; simpl;eauto.
      ---
      exists(e_anno (e_anno v0 l3 b2 (t_arrow t_dyn t_dyn)) l b (t_arrow t2 t3)).
      splits*.
      apply TReduce_dyna; simpl;eauto.
    *
    inverts H5.
    exists. splits.
    eapply TReduce_abs; eauto. 
    eapply ep_annor; eauto.
    *
    inverts H5.
    exists. splits.
    eapply TReduce_abs; eauto. 
    eapply ep_annor; eauto.
    +
    inverts typ2. inverts H1.
    inverts typ1.
    exists. splits.
    eapply TReduce_abs; eauto. 
    eapply ep_annor; eauto.
    +
    inverts typ2. inverts H1.
    inverts typ1.
    exists. splits.
    eapply TReduce_abs; eauto. 
    eapply ep_annor; eauto.
  -
    inverts ep; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1];
    try solve[inverts val2].
    +
     exists(e_anno (e_lit i) l b t_dyn).
     splits*.
    +
     inverts val2.
     *
     forwards*: Typing_regular_1 typ2.
     *
     inverts H. inverts val1. inverts typ2.
     inverts H. inverts typ1. 
     destruct(eq_type t0).
     destruct(eq_type t2).
     subst.
     --
     exists. splits*.
     eapply ep_annor; eauto.
     --
     exists. splits.
     eapply  TReduce_anyd; simpl; eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     exists. splits.
     eapply  TReduce_anyd; simpl; eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     *
     inverts H. inverts val1. inverts typ2.
     inverts H. inverts typ1. 
     destruct(eq_type A0).
     destruct(eq_type B0).
     subst.
     --
     exists. splits*.
     eapply ep_annor; eauto.
     --
     exists. splits.
     eapply  TReduce_anyd; simpl; eauto.
     eapply ep_annor; eauto.
    eapply ep_annor; eauto.
     --
     exists. splits.
     eapply  TReduce_anyd; simpl; eauto.
     eapply ep_annor; eauto.
    eapply ep_annor; eauto.
     *
     exists(e_anno e2 l2 b2 t_dyn). splits*.
    +
    inverts typ1. inverts typ2. inverts H3.
    inverts H1. 
    --
    inverts H2. inverts H0.
    inverts H9; try solve[forwards*: abs_nlam].
    inverts H13; try solve[forwards*: abs_nlam].
    destruct(eq_type B1).
    destruct(eq_type B2).
    subst.
    ---
    exists. splits*.
    eapply ep_annor; eauto.
    ---
    exists. splits.
    eapply  TReduce_anyd; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_annor; eauto.
    ---
    exists. splits.
    eapply  TReduce_anyd; simpl; eauto.
    eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
    eapply Typ_anno; eauto.
    eapply ep_annor; eauto.
    --
    inverts H0.
    ++
    forwards* lc: Typing_regular_1 H13. 
    ++
    forwards* lc: Typing_regular_1 H13. 
    +
      inverts val2; try solve[inverts H0];
      try solve[forwards*: abs_nlam];
      try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1].
     *
     forwards*: tpre_principle H1.
     rewrite <- H10 in *. 
     inverts val1; inverts H5; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H];
    try solve[forwards*: abs_nlam].
     ++ 
     destruct(eq_type A0).
     destruct(eq_type B).
     subst.
     --
     inverts typ2. inverts H5.
     exists(e_anno (e_anno e2 l1 b0 (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     --
     inverts typ2.  inverts H11.
     inverts typ1. inverts H. 
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     inverts typ2.  inverts H9.
     inverts typ1. inverts H. 
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
     eapply ep_annor; eauto.
     ++
     inverts typ1.
     inverts H.
     inverts typ2. inverts H.
     destruct(eq_type A0).
     destruct(eq_type B).
     subst.
     --
     exists(e_anno (e_anno e2 l1 b0 (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     eapply ep_annor; eauto.
     --
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     ++
     inverts typ1.
     inverts H.
     inverts typ2. inverts H.
     destruct(eq_type A0).
     destruct(eq_type B).
     subst.
     --
     exists(e_anno (e_anno e2 l1 b0 (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     eapply ep_annor; eauto.
     --
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     *
     exists(e_anno e2 l1 b0 t_dyn). splits*. 
    +
     inverts val1.
     *
     inverts typ1. 
     inverts H2.
     --
     forwards*: tpre_principle H1.
     rewrite <- H10 in *.
     inverts val2; try solve[inverts H0]; simpl in *.
     ***
     inverts H13; try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int].
     forwards*: principle_inf H.
     ***
     exists(e_anno v l2 b1 t_dyn). splits*.
     --
     inverts val2; inverts H0; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
     ***
     inverts H13; try solve[forwards*: abs_epre_true2 H1];
    try solve[forwards*: absr_epre_true2 H1]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
     forwards*: principle_inf H0.
     rewrite <- H12 in *; subst.
     forwards*: principle_inf H.
     rewrite <- H10 in *; subst.
     inverts typ2. inverts H12.
     destruct(eq_type C0).
     destruct(eq_type D0).
     subst.
     ---
     exists.
     splits*.
     ---
     exists.
     splits.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_anno; eauto.
     ---
     exists.
     splits.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_anno; eauto.
     ***
     inverts typ2. inverts H0.
     forwards*:Principle_inf H. rewrite <- H10 in *.
     subst*.
     forwards*: epre_nlamr H1.
     destruct(eq_type C0).
     destruct(eq_type D0).
     subst.
     ---
     exists(e_anno (e_anno v l2 b1 (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     ---
     exists(e_anno (e_anno (e_anno v l2 b1 (t_arrow C0 D0)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     ---
     exists(e_anno (e_anno (e_anno v l2 b1 (t_arrow C0 D0)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     ***
     exists. splits.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_anno;eauto.
     forwards*: epre_nlamr H1.
     ***
     exists. splits.
     apply TReduce_anyd;eauto.
     eapply ep_annor; eauto.
     eapply ep_anno;eauto.
     forwards*: epre_nlamr H1.
     *
     inverts typ1.
     inverts H2.
     inverts val2; inverts H0.
     ***
     forwards*: principle_inf H.
     exists. splits*.
     ***
     forwards*: walue_lc H5.
     exists(e_anno v l2 b1 t_dyn). splits*.
     +
     inverts typ1. inverts typ2. inverts H2.
     exists. splits.
     apply TReduce_anyd;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     +
     inverts typ1. inverts typ2. inverts H1.
     exists. splits.
     apply TReduce_anyd;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
Qed.



Lemma value_tred_keep0: forall v v' A l b,
 Typing nil v Chk A ->
 value (e_anno v l b A) ->
 TypedReduce v l b A (e_exp v') ->
 v' = (e_anno v l b A).
Proof.
  introv typ val red.
  inverts* val; simpl in *.
  -
  inverts* typ; simpl in *; subst.
  inverts* H1.
  inverts* red.
  forwards*: Principle_inf H.
  rewrite <- H3 in *.
  subst*.
  rewrite <- H4 in *.
  inverts* red; try solve[simpl in *; inverts* H4].
  -
  inverts* red; simpl in *; inverts* H1.
  rewrite <- H0 in *. inverts* H5. inverts* H1.
  inverts* H3.
  rewrite <- H0 in *. inverts* H5. 
Qed.


Lemma val_nlam_wal: forall v,
 value v ->
 nlam v ->
 walue v.
Proof.
  introv val nl.
  inductions val; try solve[inverts* nl].
  -
  inductions val;eauto.
  -
  inductions val;eauto.
Qed. 


Lemma epre_val: forall v1 v2 t1 t2,
 Typing nil v1 Chk t1 ->
 Typing nil v2 Chk t2 ->
 epre nil nil v1 v2 ->
 value v1 ->
 exists v2', steps v2 (e_exp v2') /\ value v2' /\ epre nil nil v1 v2'.
Proof.
  introv typ1 typ2 ep val. gen t1 t2.
  inductions ep; intros;try solve[inverts* val];
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  -
  forwards*: Typing_regular_1 typ2. 
  exists.
  splits*.
  -
  inverts typ2. inverts H1.
  inverts typ1. inverts H1.
  forwards*: IHep H10.
  inverts* val.
  lets(v2'&red&val2&epr): H1.
  inverts val.
  +
  inverts H.
  *
  forwards*: preservation_multi_step red.
  inverts H13; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  ***
  inverts H; try solve[forwards*: abs_epre_true2 epr];
    try solve[forwards*: absr_epre_true2 epr]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  ****
  forwards*: epre_value_arrow epr. inverts H.
  lets(v21&ll&bb&eq&eq2): H15. substs.
  exists((e_anno v21 ll bb t_dyn)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  forwards*: value_lc val2. inverts H.
  apply Step_annov; eauto.
  unfold not; intros nt; inverts* nt. inverts H18.
  inverts H11.
  eapply ep_annol; eauto.
  lets(t3&t4&eq): H15. substs.
  destruct(eq_type t3).
  destruct(eq_type t4); subst.
  exists((e_anno (v2') l2 b2 t_dyn)).
  splits*.
  apply multi_rred_anno. apply red.
  eapply value_dyn; eauto.
  rewrite eq; eauto.
  exists((e_anno (e_anno (v2') l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
  splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply TReduce_anyd; simpl; eauto.
  rewrite eq; eauto.
  unfold not; intros nt; inverts* nt. 
  rewrite eq in H18; inverts* H18.
  apply value_dyn; eauto.
  forwards*: principle_inf H11.
  rewrite eq in *. subst.
  eapply ep_annor; eauto.
  exists((e_anno (e_anno (v2') l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
  splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply TReduce_anyd; simpl; eauto.
  rewrite eq; eauto.
  unfold not; intros nt; inverts* nt. 
  rewrite eq in H18; inverts* H18.
  apply value_dyn; eauto.
  forwards*: principle_inf H11.
  rewrite eq in *. subst.
  eapply ep_annor; eauto.
  *
  forwards*: preservation_multi_step red.
  inverts H13; try solve[forwards*: abs_epre_true2 epr];
    try solve[forwards*: absr_epre_true2 epr]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  ***
  inverts H; try solve[forwards*: abs_epre_true2 epr];
    try solve[forwards*: absr_epre_true2 epr]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  ****
  forwards*: epre_value_arrow epr. inverts H.
  lets(v21&ll1&bb1&eq1&eq2): H17. substs.
  inverts val2; try solve[forwards*: abs_epre_true2 epr];
    try solve[forwards*: absr_epre_true2 epr]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  forwards*: Principle_inf H6.
  rewrite <- H12 in *. substs.
  inverts* H13; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[forwards*: abs_nlam].
  inverts* H25; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  --
  forwards*: epre_abs ll1 bb1 ll1 bb1 epr.
  forwards*: value_group H8.
  inverts* H13. 
  lets(var1&var2&var3&hh1):H18; inverts hh1. inverts H11.
  destruct(eq_type C0).
  destruct(eq_type D0); subst.
  ++
  exists.
  splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  unfold not; intros nt; inverts* nt. inverts H26.
  eapply value_fanno; eauto. 
  eapply ep_annol; eauto.
  ++
  exists. splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  unfold not; intros nt; inverts* nt. inverts H27.
  eapply value_fanno; eauto. 
  eapply ep_anno; eauto.
  ++
  exists. splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  unfold not; intros nt; inverts* nt. inverts H27.
  eapply value_fanno; eauto. 
  eapply ep_anno; eauto.
  --
  forwards*: Principle_inf H.
  rewrite eq2 in H20. substs.
  forwards*: epre_dyn epr.
  forwards*: value_group H21.
  inverts* H20. 
  lets(var1&var2&var3&hh1):H22; inverts hh1. inverts H18.
  destruct(eq_type C0).
  destruct(eq_type D0); subst.
  exists v21.
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  rewrite <- eq2.
  apply TReduce_vany; eauto.
  unfold not; intros nt; inverts* nt. inverts H28.
  exists(e_anno v21 l2 b2 (t_arrow t_dyn D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply  TReduce_dyna; eauto.
  rewrite eq2; auto.
  unfold not; intros nt; inverts* nt; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H29].
  exists(e_anno v21 l2 b2 (t_arrow C0 D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply  TReduce_dyna; eauto.
  rewrite eq2; auto.
  unfold not; intros nt; inverts* nt. inverts H29.
  --
  lets(t3&t4&eq): H17. substs.
  exists(e_anno (v2') l2 b2 (t_arrow C0 D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply step_refl.
  +
  inverts H.
  forwards*: preservation_multi_step red.
  assert(TypedReduce e1 l1 b1 t_dyn (e_exp (e_anno e1 l1 b1 t_dyn))); eauto.
  forwards*: val_nlam_wal H12.
  forwards*: epre_nlam ep.
  forwards* h1: steps_not_nlam red.
  forwards*: val_nlam_wal val2 h1.
  forwards*: tdynamic_guarantee l2 b2 epr H6.
  lets(e2'&tred&epp): H14.
  forwards*: value_lc val2.
  destruct(value_decidable (e_anno v2' l2 b2 t_dyn)); eauto.
  exists (e_anno v2' l2 b2 t_dyn).
  splits*.
  apply multi_rred_anno. apply red.
  forwards*: Tred_value tred.
  exists e2'.
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  -
  forwards* lc1: Typing_regular_1 typ2. inverts lc1.
  inverts H2.
  +
  exists. splits*.
  +
  exists. splits*.
  -
  inverts typ2. inverts H4.
  forwards*: IHep.
  inverts H4. inverts H7. inverts H8.
  forwards*: preservation_multi_step H13 H4.
  forwards*: tred_right l b H8 H1.
  forwards* ha: value_group H7.
  inverts* ha.
  lets(var1&var2&var3&hh1):H10; inverts hh1.
  forwards*: epre_nlam H9.
  inverts H11.
  lets(v2'& rred& epp):H10.
  exists v2'. splits*.
  eapply stars_trans.
  apply multi_rred_anno; eauto.
  forwards*: value_lc H7.
  destruct(value_decidable (e_anno x l b A0)); auto.
  forwards*:value_tred_keep rred. inverts* H14.
  forwards*: Tred_value rred.
  -
  inverts typ1. inverts H4.
  forwards*: IHep.
  inverts* val.
  inverts H4. inverts H7. inverts H8.  
  forwards*: epre_nlamr ep.
  forwards*: epre_nlam H9.
  forwards*: preservation_multi_step H0 H4.
Qed.


Lemma tp_not_int: forall A B,
 tpre A B ->
 not(A = t_int) ->
 not(B = t_int).
Proof.
  introv tp nin.
  inductions tp; try solve[exfalso; apply nin; eauto];
  try solve[unfold not; intros nt; inverts* nt].
Qed.



Lemma value_tred_keep: forall v r A l b,
Typing nil v Chk A ->
value (e_anno v l b A) ->
TypedReduce v l b A r ->
r = (e_exp (e_anno v l b A)).
Proof.
 introv typ val red.
 inverts* val; simpl in *.
 -
 inverts* typ; simpl in *; subst.
 inverts* H1.
 inverts* red.
 forwards*: principle_inf H.
 rewrite <- H3 in *.
 subst*.
 rewrite <- H4 in *.
 inverts* red; try solve[simpl in *; inverts* H4].
 -
 inverts* red; simpl in *; inverts* H1.
 rewrite <- H2 in *. inverts* H. inverts* H1.
 inverts* H3.
 rewrite <- H2 in *. inverts* H. 
Qed.


Lemma epre_valr: forall v1 v2 t1 t2,
 Typing nil v1 Chk t1 ->
 Typing nil v2 Chk t2 ->
 epre nil nil v1 v2 ->
 value v2 ->
 ((exists v1' , steps v1 (e_exp v1') /\ value v1' /\ epre nil nil v1' v2)
 \/ exists l b, steps v1 (e_blame l b)).
Proof.
  introv typ1 typ2 ep val. gen t1 t2.
  inductions ep; intros;try solve[inverts* val];
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  -
    forwards*: Typing_regular_1 typ1. 
    left.
    exists.
    splits*.
  -
    inverts typ1. inverts H1.
    inverts typ2. inverts H1.
    forwards*: IHep H10 H13.
    inverts* val.
    inverts* H1.
    lets(vv&rred&vval&epp): H6.
    +
    forwards*: preservation_multi_step rred.
    forwards*: TypedReduce_progress l1 b1 H1.
    inverts H7. destruct x; eauto.
    *
    forwards*: steps_not_nlam rred.
    destruct(value_decidable (e_anno vv l1 b1 A0)); auto.
    forwards*: value_tred_keep H8. inverts* H11.
    --
    left. exists. splits.
    apply multi_rred_anno; eauto.
    auto.
    eapply ep_anno; eauto.
    --
    forwards* h1: epre_nlam ep.
    forwards* h2: steps_not_nlam rred.
    forwards* h3: val_nlam_wal h2.
    forwards*: tdynamic_guarantee l1 b1 epp H.
    forwards* h4: val_nlam_wal h1.
    inverts* val.
    lets(vv1&rred1&epp1):H11.
    forwards*: value_tred_keep rred1.
    inverts* H12.
    left. exists. splits.
    eapply stars_trans.
    apply multi_rred_anno; eauto.
    apply stars_one.
    eapply Step_annov; eauto.
    forwards*: Tred_value H8.
    auto.
    *
    destruct(value_decidable (e_anno vv l1 b1 A0)); auto.
    forwards*: value_tred_keep H8. inverts* H9.
    inverts H8.
    right.
    exists.
    eapply stars_transb.
    apply multi_rred_anno; eauto.
    apply step_b; eauto.
    +
    inverts H6. inverts H1.
    forwards*: multi_bblame_anno H6.
  -
    forwards* lc1: Typing_regular_1 typ1. inverts lc1.
    inverts* H1.
    +
    left.
    exists*.
    +
    left.
    exists*.
  -
    inverts typ2. inverts H4.
    forwards*: IHep.
    inverts* val.
    inverts* H4.
    lets(vv&rred&vval&epp): H7.
    forwards: preservation_multi_step H rred.
    forwards*: epre_nlam ep.
    forwards*: epre_nlamr epp.
  -
    inverts typ1. inverts H4.
    forwards*: IHep.
    inverts H4.
    +
    lets(vv&rred&vval&epp): H7.
    forwards*: preservation_multi_step H rred.
    forwards*: preservation_multi_step H rred.
    destruct(value_decidable (e_anno vv l b A0)); eauto.
    left.
    exists. splits.
    apply multi_rred_anno.
    apply rred.
    auto. eauto.
    forwards: preservation_multi_step H13 rred.
    forwards*: TypedReduce_progress l b H10.
    inverts H11. destruct x.
    forwards*: tred_left epp H12.
    forwards*: epre_nlamr epp.
    left. exists. splits.
    eapply stars_trans.
    apply multi_rred_anno.
    apply rred.
    apply stars_one.
    apply Step_annov; eauto.
    forwards*: Tred_value H12.
    auto.
    right. exists. 
    eapply stars_transb.
    apply multi_rred_anno.
    apply rred.
    apply step_b.
    apply Step_annov; eauto.
    +
    inverts H7. inverts H4.
    forwards*: multi_bblame_anno H7.
Qed.



Lemma unwrap_epre: forall v1 v2 v3 v4 t3 t4 l2 b2 tt1 tt2 c d,
 Typing nil (e_appv (e_anno (v1) l2 b2 (t_arrow t3 t4)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 walue v1 ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre nil nil (e_anno v1 l2 b2 (t_arrow t3 t4)) v3 ->
 epre nil nil v2 v4 ->
 principal_type v1 = (t_arrow c d) ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ (epre nil nil (e_anno (e_appv v1  (e_anno v2 l2 (negb b2) c)) l2 b2 t4) e2').
Proof.
  introv typ1 typ2 val1 wal1 val2 val3 val4 ep1 ep2 ty. 
  gen tt1 tt2 v2 v4 c d.
  inductions ep1; intros.
  -
    inverts typ1. inverts H1.
    inverts H6. 
    inverts typ2. inverts H1. inverts H11.  
    inverts val3.
    forwards*: epre_wal ep1.
    inverts H.
    forwards* h1: tpre_principle ep1.
    rewrite ty in *.
    rewrite <- H16 in *.
    inverts h1.
    exists. splits.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply ep_anno; eauto.
  -
    inverts wal1.
  -
    inverts typ1. inverts H4. inverts H9.
    inverts typ2. inverts H4. inverts H14.
    inverts H. 
    inverts val3. 
    forwards*: epre_wal ep1. inverts val1. 
    forwards*: tpre_principle ep1; simpl in *.
    inverts H20; try solve[inverts H].
    forwards*: principle_inf H13.
    rewrite <- H18 in *. inverts H20. 
    inverts H15. inverts H4. 
    forwards* h1: tred_right ep2.
    lets (vv1&rred1&epp1): h1.
    forwards*: TypedReduce_preservation rred1.
    forwards*: TypedReduce_walue rred1.
    forwards* h2: IHep1 v1 epp1.
    lets (vv&rred&epp): h2.
    assert(Typing nil (e_appv e2 vv1) Inf D); eauto.
    forwards*: preservation_multi_step rred.
    inverts H1.
    inverts H8; try solve[inverts wal1].
    forwards*: principle_inf H1.
    rewrite H8 in *. subst.  inverts H26. 
    destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
    +
    forwards h6: rred1. 
    forwards* h7: value_tred_keep2 h6. inverts h7.
    inverts H23. 
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply multi_rred_anno.
    apply rred.
    eapply ep_annor;eauto.
    eapply Typ_anno;eauto.
    +
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno.
    rewrite fill_appvr.
    apply do_step; auto.
    apply do_step; auto.
    eapply Step_annov; simpl; eauto.
    unfold fill.
    apply multi_rred_anno.
    apply rred.
    eapply ep_annor; eauto.
    eapply Typ_anno;eauto.
  -
    inverts typ1. inverts H4. inverts H9.
    inverts typ2. inverts H4. 
    forwards*: principle_inf H14.
    forwards*: principle_inf H0.
    rewrite H4 in *. inverts H10.
    inverts val1.
    forwards*: tpre_principle ep1; simpl in *.
    rewrite H4 in *. rewrite <- H21 in *.
    inverts H10. inverts ty.
    inverts H8; try solve[inverts wal1].
    forwards*: principle_inf H10.
    rewrite <- H21 in *. subst.
    inverts H13.
    inverts H1.
    exists. splits.
    apply step_refl.
    eapply ep_annol; eauto.
Qed.


Lemma unwrap_eprer: forall v1 v2 v3 v4 t3 t4 tt1 tt2 l2 b2 ttt1 ttt2,
 Typing nil (e_appv (e_anno v1 l2 b2 (t_arrow t3 t4)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 walue v1 ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre  nil nil v3 (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 epre nil nil v4 v2 ->
 principal_type v1 = (t_arrow ttt1 ttt2) ->
 (exists e2', steps (e_appv v3 v4) (e_exp e2') /\ (epre  nil nil e2' (e_anno (e_appv v1 (e_anno v2 l2 (negb b2) ttt1)) l2 b2 t4)))
 \/ exists l b, steps (e_appv v3 v4) (e_blame l b).
Proof.
  introv typ1 typ2 val1 wal1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4 ttt1 ttt2.
  inductions ep1; intros.
  -
  inverts H. inverts val3. inverts val1.
  forwards*: tpre_principle ep1; simpl in *.
  rewrite <- H11 in *.
  forwards*: epre_walr ep1.
  inverts H.
  rewrite <- H7 in *.
  inverts H1.
  left. exists.
  splits.
  apply stars_one.
  eapply Step_abeta; eauto.
  apply ep_anno; eauto.
  -
  inverts wal1.
  -
  inverts H1.
  inverts typ1. inverts H1. inverts H11.
  inverts typ2. inverts H1.
  forwards* h1: principle_inf H16. 
  forwards* h2: principle_inf H. 
  rewrite h1 in *. inverts h2.
  forwards* h3: epre_walr ep1.
  inverts H10; try solve[inverts wal1].
  forwards* h4: principle_inf H16.
  forwards* h5: principle_inf H0.
  forwards* h6: principle_inf H1.
  rewrite h5 in *. subst.
  inverts H2. inverts H12.
  left. exists. splits*.
  eapply ep_annor; eauto.
  -
  inverts H0. inverts H2. inverts H1.
  inverts val3. 
  inverts typ1. inverts H0. inverts H14.
  inverts typ2. inverts H0. inverts H19.
  inverts val1.
  forwards* h1: epre_walr ep1.
  inverts H18; try solve[ inverts h1]. 
  forwards* h2: principle_inf H0.
  forwards* h3: principle_inf H.
  rewrite h3 in *. subst. inverts H15.
  rewrite <- H25 in *. inverts H4.
  forwards*: TypedReduce_progress v4 A0.
  inverts H4. destruct x; eauto.
  +
  forwards* h4: tred_left ep2 H15. 
  forwards* h5: TypedReduce_walue H15.
  forwards*: TypedReduce_preservation H15.
  forwards*: IHep1 v1 h4.
  inverts H12; try solve[inverts wal1].
  forwards*: principle_inf H23.
  rewrite H12 in *. subst.
  inverts H24.
  inverts H18.
  *
  lets(vv1&rred1&epp1): H24.
  assert(Typing nil (e_appv e1 e) Inf B).
  eauto.
  forwards*: preservation_multi_step rred1.
  destruct(value_decidable (e_anno v4 l (negb b) A0)); auto.
  --
  forwards* h2: value_tred_keep2 H15.
  inverts h2.
  left. exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  apply multi_rred_anno.
  apply rred1.
  eapply ep_annol; eauto.
  eapply Typ_anno;eauto.
  --
  left. exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  eapply stars_trans.
  apply stars_one.
  rewrite fill_anno.
  apply do_step; eauto.
  rewrite fill_appvr.
  eapply do_step;eauto.
  unfold fill.
  apply multi_rred_anno.
  apply rred1.
  eapply ep_annol; eauto.
  eapply Typ_anno;eauto.
  *
  destruct(value_decidable (e_anno v4 l (negb b) A0)); auto.
  --
  forwards* h2: value_tred_keep2 H18.
  inverts h2.
  lets(ll3&bb3&rred3):H24.
  right.
  exists.
  eapply stars_transb.
  apply stars_one.
  eapply Step_abeta; eauto.
  apply multi_bblame_anno; eauto.
  --
  lets(ll3&bb3&rred3):H24.
  right.
  exists.
  eapply stars_transb.
  apply stars_one.
  eapply Step_abeta; eauto.
  eapply stars_transb.
  apply stars_one.
  rewrite fill_anno.
  apply do_step; eauto.
  rewrite fill_appvr.
  eapply do_step;eauto.
  unfold fill.
  apply multi_bblame_anno; eauto.
  +
  inverts* H15.
  right. 
  exists.
  eapply stars_transb.
  apply stars_one.
  eapply Step_abeta; eauto.
  apply multi_bblame_anno.
  apply step_b; eauto.
  rewrite fill_appvr.
  apply blame_step; eauto.
  eapply Step_annov; eauto.
  unfold not;intros nt;inverts* nt. inverts H27.
Qed.


Lemma add: forall i v3 v4 tt1 tt2,
 Typing nil (e_appv e_add (e_lit i)) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 epre nil nil e_add v3 ->
 epre nil nil (e_lit i) v4 ->
 value v3 ->
 walue v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_addl i) e2'.
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. 
  gen i tt1 tt2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
  -
    inverts typ2. inverts H4. inverts H9.
    inverts typ1. inverts H4. inverts H13.
    inverts H. inverts H15; try solve[inverts ep1].
    inverts val3.
    forwards*: principle_inf H. 
    forwards*: tpre_principle ep1; simpl in *.
    rewrite <- H22 in *. subst. inverts H9. inverts H15.
    forwards*: tred_right l (negb b) ep2.
    lets (vv1&rred1&epp1): H9.
    forwards*: TypedReduce_walue rred1.
    forwards*: TypedReduce_preservation rred1. 
    forwards*: IHep1 epp1.
    lets (vv2&rred2&epp2): H19.
    forwards*: epre_wal ep1.
    forwards*: preservation_multi_step D rred2.
    inverts H1.
    destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
    --
    forwards* h1: value_tred_keep2 rred1.
    inverts h1.
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_rred_anno. apply rred2.
    eapply ep_annor; eauto.
    --
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    rewrite fill_anno.
    rewrite fill_appvr.
    eapply stars_trans.
    apply stars_one.
    apply do_step; auto.
    apply do_step; auto.
    eapply Step_annov;eauto.
    unfold fill.
    apply multi_rred_anno. apply rred2.
    eapply ep_annor; eauto.
  -
    inverts typ2. inverts H1.
    forwards*: tpre_principle ep2; simpl in *.
    inverts typ1. inverts H4. inverts H12.
    inverts H6. inverts val4;inverts H8.
    exists. splits.
    eapply stars_one.
    eapply Step_add; eauto.
    inverts* ep2.
Qed.



Lemma addl: forall i1 i2 v3 v4 tt1 tt2,
 Typing nil (e_appv (e_addl i1) (e_lit i2)) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 epre nil nil (e_addl i1) v3 ->
 epre nil nil (e_lit i2) v4 ->
 value v3 ->
 walue v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_lit (i1+i2)) e2'.
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. 
  gen i2 tt1 tt2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
  -
    inverts typ2. inverts H4. inverts H9.
    inverts typ1. inverts H4. inverts H13.
    inverts H. inverts H15; try solve[inverts ep1].
    inverts val3.
    forwards*: principle_inf H. 
    forwards*: tpre_principle ep1; simpl in *.
    rewrite <- H22 in *. subst. inverts H14. inverts H4.
    forwards*: tred_right l (negb b) ep2.
    lets (vv1&rred1&epp1): H4.
    forwards*: TypedReduce_walue rred1.
    forwards*: TypedReduce_preservation rred1. 
    forwards*: IHep1 epp1.
    lets (vv2&rred2&epp2): H19.
    forwards*: epre_wal ep1.
    forwards*: preservation_multi_step D rred2.
    inverts H1.
    destruct(value_decidable (e_anno v4 l (negb b) C));eauto.
    --
    forwards* h2:value_tred_keep2 rred1.
    inverts h2.
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_rred_anno. apply rred2.
    eapply ep_annor; eauto.
    --
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    rewrite fill_anno.
    eapply stars_trans.
    rewrite fill_appvr.
    apply stars_one.
    apply do_step; auto.
    apply do_step; auto.
    eapply Step_annov;simpl; eauto.
    apply multi_rred_anno.
    unfold fill. apply rred2.
    eapply ep_annor; eauto.
  -
    inverts typ2. inverts H1.
    forwards*: tpre_principle ep2; simpl in *.
    inverts typ1. inverts H4. inverts H12.
    inverts H6. inverts val4;inverts H8.
    exists. splits.
    eapply stars_one.
    eapply Step_addl; eauto.
    inverts* ep2.
Qed.


Lemma addr: forall v3 v4 tt1 tt2 i,
 Typing nil (e_appv e_add (e_lit i)) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 epre nil nil v3 e_add ->
 epre nil nil v4 (e_lit i) ->
 value v3 ->
 walue v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_addl i).
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. gen v4 i tt1 tt2.
  inductions ep1;intros.
  -
  inverts typ2. inverts H4. inverts H9. inverts H0.
  inverts val3.
  forwards*: value_group H8. 
  inverts H0.
  +
  forwards*: tpre_principle ep2; simpl in *.
  inverts val4; inverts H0. inverts H11.
  forwards*: tpre_principle ep1; simpl in *.
  inverts H0. inverts H17.
  inverts H15; try solve[forwards*: abs_nlam].
  forwards*: principle_inf H0.
  rewrite <- H9 in *. subst.
  inverts H16. inverts H18. inverts H19.
  forwards*: IHep1 ep2.
  lets(vv1&rred1&epp1):H15.
  inverts H1.
  forwards*: preservation_multi_step (t_arrow t_int t_int) rred1.

  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  eapply stars_trans.
  apply stars_one.
  rewrite fill_anno. apply do_step; auto.
  rewrite fill_appvr. apply do_step; auto.
  eapply Step_annov; eauto.
  unfold not;intros nt;inverts* nt. 
  unfold fill.
  apply multi_rred_anno; eauto.
  eapply ep_annol; eauto.
  +
  lets(var1&var2&var3&hh1):H7; inverts hh1.
  inverts H7; inverts* ep1.
  -
  inverts typ2. inverts H1.
  forwards*:tpre_principle ep2; simpl in *.
  inverts H6.
  inverts val4; inverts H8.
  exists. splits.
  eapply stars_one.
  eapply Step_add; eauto.
  inverts* ep2. 
Qed. 



Lemma addlr: forall v3 v4 tt1 tt2 i1 i2,
 Typing nil (e_appv (e_addl i1) (e_lit i2)) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 epre nil nil v3 (e_addl i1) ->
 epre nil nil v4 (e_lit i2) ->
 value v3 ->
 walue v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_lit (i1+i2)).
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4.
  gen v4 i2 tt1 tt2.
  inductions ep1;intros.
  -
  inverts typ2. inverts H4. inverts H9. inverts H0.
  inverts val3.
  forwards*: value_group H7. 
  inverts H0.
  +
  forwards*: tpre_principle ep2; simpl in *.
  inverts val4; inverts H0. inverts H11.
  forwards*: tpre_principle ep1; simpl in *.
  inverts H0. inverts H16. inverts H17.
  inverts H15; try solve[inverts H4].
  forwards*: principle_inf H0.
  rewrite <- H9 in *. subst.
  forwards*: IHep1 ep2.
  lets(vv1&rred1&epp1):H15.
  inverts H1.
  forwards*: preservation_multi_step rred1.
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  eapply stars_trans.
  apply stars_one.
  rewrite fill_anno. apply do_step; auto.
  rewrite fill_appvr. apply do_step; auto.
  eapply Step_annov; eauto.
  unfold not;intros nt;inverts* nt. 
  unfold fill.
  apply multi_rred_anno; eauto.
  eapply ep_annol; eauto.
  +
  lets(var1&var2&var3&hh1):H4; inverts hh1.
  inverts H4; inverts ep1.
  -
  inverts typ2. inverts H1.
  forwards*:tpre_principle ep2; simpl in *.
  inverts H6.
  inverts val4; inverts H8.
  exists. splits.
  eapply stars_one.
  eapply Step_addl; eauto.
  inverts* ep2. 
Qed. 


Lemma beta_epre: forall e v2 v3 v4 t1 t2 tt1 tt2 l1 b1 ll1 bb1,
 Typing nil (e_appv (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre nil nil (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) v3 ->
 epre nil nil v2 v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_anno (e ^^ v2) l1 b1 t2) e2'.
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H];
    try solve[forwards*: epre_nlamr ep1; try solve[forwards*: abs_nlam]].
  -
    inverts typ1. inverts H4. inverts H9. 
    inverts H8;try solve[forwards*: abs_nlam].
    inverts typ2. inverts H4. inverts H14. 
    inverts H20; try solve[forwards*: abs_nlam].
    forwards*: walue_lc val4.
    forwards*: walue_lc val2.
    inverts H1.
    inverts val3.
    inverts H2. 
    exists. splits.
    apply stars_one.
    apply Step_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    assert((e2 ^^ v4) = [y ~> v4] (e2 ^^ e_var_f y)).
    rewrite (subst_exp_intro y); eauto.
    rewrite H1.
    forwards*: H y.
    forwards*: epre_open H2 ep2.
  -
  inverts typ1. inverts H4. inverts H9. 
  inverts typ2. inverts H4. inverts H14. 
  inverts val3.  inverts H.
  forwards*: principle_inf H0. rewrite H in *. inverts H19.
  inverts H13; simpl in *;inverts H;try solve[forwards*: abs_epre_true2 ep1];
    try solve[forwards*: absr_epre_true2 ep1]; 
    try solve[forwards*: flike_int];
    try solve[inverts H0].
  +
  inverts H20. inverts H. inverts H13.
  forwards*: tpre_principle ep1; simpl in *.
  inverts H.
  forwards*: tred_right l (negb b) ep2.
  lets (vv1&rred1&epp1): H.
  forwards*: TypedReduce_walue rred1.
  forwards*: TypedReduce_preservation rred1. 
  forwards*: IHep1 epp1.
  lets (vv2&rred2&epp2): H18.
  inverts H1. 
  inverts H0.
  assert(Typing nil (e_appv (e_anno v p b0 (t_arrow C D)) vv1) Inf D); eauto.
  forwards*: preservation_multi_step rred2.
  inverts H26; try solve[inverts H14].
  ++
  destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
  +++
  forwards* h1: value_tred_keep2 rred1. inverts h1.
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  eapply multi_rred_anno; eauto.
  eapply ep_annor; eauto.
  apply Typ_anno; eauto.
  inverts H22; try solve[forwards*: abs_nlam].
  pick fresh y .
  forwards*: H32 y.
  rewrite (subst_exp_intro y); eauto.
  eapply typing_c_subst_simpl; eauto.
  +++
  inverts H22; try solve[forwards*: abs_nlam].
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  rewrite fill_anno.
  rewrite fill_appvr.
  eapply stars_trans.
  apply stars_one.
  apply do_step; auto.
  apply do_step; auto.
  eapply Step_annov;eauto.
  unfold fill.
  apply multi_rred_anno. apply rred2.
  eapply ep_annor; eauto.
  apply Typ_anno; eauto.
  pick fresh y .
  forwards*: H32 y.
  rewrite (subst_exp_intro y); eauto.
  eapply typing_c_subst_simpl; eauto.
  ++
  forwards* h1: value_group H4.
  inverts h1; try solve[ lets(var1&var2&var3&hh1):H26; inverts hh1;inverts H29].
  destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
  +++
  inverts H8; try solve[forwards*: abs_nlam].
  forwards* h2: value_tred_keep2 rred1. inverts h2.
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  apply multi_rred_anno. apply rred2.
  eapply ep_annor; eauto.
  apply Typ_anno; eauto.
  pick fresh y .
  forwards*: H34 y.
  rewrite (subst_exp_intro y); eauto.
  eapply typing_c_subst_simpl; eauto.
  +++
  inverts H8; try solve[forwards*: abs_nlam].
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  eapply Step_abeta; eauto.
  rewrite fill_anno.
  rewrite fill_appvr.
  eapply stars_trans.
  apply stars_one.
  apply do_step; auto.
  apply do_step; eauto.
  unfold fill.
  apply multi_rred_anno. apply rred2.
  eapply ep_annor; eauto.
  apply Typ_anno; eauto.
  pick fresh y .
  forwards*: H34 y.
  rewrite (subst_exp_intro y); eauto.
  eapply typing_c_subst_simpl; eauto.
  +
  inductions ep1; try solve[inverts ep1].
  +
  inductions ep1; try solve[inverts ep1].
Qed.


Lemma beta_eprer: forall e v2 v3 v4 t1 t2 tt1 tt2 l1 b1 ll1 bb1,
 Typing nil (e_appv (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre nil nil v3 (e_anno (e_abs e ll1 bb1) l1 b1 (t_arrow t1 t2)) ->
 epre nil nil v4 v2 ->
 (exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_anno (e ^^ v2) l1 b1 t2)) \/
 exists l b, steps (e_appv v3 v4) (e_blame l b ).
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep1];
    try solve[forwards*: absr_epre_true2 ep1]; 
    try solve[forwards*: flike_int];
    try solve[inverts H0].
  -
    inverts typ2. inverts H4. inverts H9. inverts H1. inverts H2.
    inverts val3.
    inverts typ1. inverts H1.
    inverts H13.
    left. exists. splits.
    apply stars_one.
    eapply Step_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    assert((e ^^ v2) = [y ~> v2] (e ^^ e_var_f y)).
    rewrite (subst_exp_intro y); eauto.
    rewrite H1.
    forwards*: H y.
    forwards*: epre_open H8 ep2.
  -
    inverts H0. inverts H1. inverts H2.
    inverts typ1. inverts H0. inverts H11. 
    inverts typ2. inverts H0. inverts H16. 
    inverts H15; try solve[forwards*: abs_epre_true2 ep1];
    try solve[forwards*: absr_epre_true2 ep1]. 
    inverts val3.
    forwards*: principle_inf H0.
    forwards*: principle_inf H.
    rewrite <- H24 in *. subst. inverts H12. 
    inverts H20; inverts* H0; try solve[forwards*: abs_nlam].
    ++
    forwards*: TypedReduce_progress v4 C.
    inverts H0. destruct x.
    +
    forwards*: tpre_principle ep1; simpl in *.
    inverts H17. inverts H0.
    forwards*: tred_left ep2 H20.
    forwards*: TypedReduce_walue H20.
    forwards*: TypedReduce_preservation H20. 
    forwards*: IHep1 H0.
    inverts H25.
    *
    lets(vv1&rred1&epp1): H28.
    assert(Typing nil ( e_appv (e_anno v p b0 (t_arrow A B0)) e0) Inf B0).
    eauto.
    forwards*: preservation_multi_step H25 rred1.
    inverts H.
    forwards*: value_group H12. inverts H.
    --
    destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
    ---
    inverts H10; try solve[forwards*: abs_nlam].
    forwards* h1: value_tred_keep2 H20. inverts h1.
    left. exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
    inverts* H3; try solve[inverts H].
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    forwards*: H35 y.
    apply Typ_anno; eauto.
    eapply typing_c_subst_simpl; eauto.
    ---
    left. exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno;eauto. apply do_step; auto.
    rewrite fill_appvr;eauto. apply do_step; eauto.
    unfold fill.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
    inverts* H9; try solve[forwards*: abs_nlam].
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    forwards*: H35 y.
    apply Typ_anno; eauto.
    eapply typing_c_subst_simpl; eauto.
    --
    inverts H31. 
    destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
    ---
    inverts H10; try solve[forwards*: abs_nlam].
    forwards* h1: value_tred_keep2 H20. inverts h1.
    lets(var2&var3&hh1):H; inverts hh1.
    left. exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
    inverts* H3; try solve[inverts H].
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    forwards*: H35 y.
    apply Typ_anno; eauto.
    eapply typing_c_subst_simpl; eauto.
    ---
    lets(var2&var3&hh1):H; inverts hh1.
    left. exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno;eauto. apply do_step; auto.
    rewrite fill_appvr;eauto. apply do_step; eauto.
    unfold fill.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
    inverts* H9; try solve[forwards*: abs_nlam].
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    forwards*: H35 y.
    apply Typ_anno; eauto.
    eapply typing_c_subst_simpl; eauto.
    *
    inverts H28. inverts H25.
    forwards*: value_group H12. inverts H25.
    --
    destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
    ---
    inverts H9; try solve[forwards*: abs_nlam].
    forwards* h1: value_tred_keep2 H20. inverts h1.
    right. exists. 
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_bblame_anno; eauto.
    ---
    right. exists. 
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_transb.
    apply stars_one.
    rewrite fill_anno;eauto. apply do_step; auto.
    rewrite fill_appvr;eauto. apply do_step; eauto.
    unfold fill.
    apply multi_bblame_anno; eauto.
    --
    inverts H30. 
    destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
    ---
    inverts H9; try solve[forwards*: abs_nlam].
    forwards* h1: value_tred_keep2 H20. inverts h1.
    lets(var2&var3&hh1):H25; inverts hh1.
    right. exists. 
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply multi_bblame_anno; eauto.
    ---
    lets(var2&var3&hh1):H25; inverts hh1.
    right. exists. 
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_transb.
    apply stars_one.
    rewrite fill_anno;eauto. apply do_step; auto.
    rewrite fill_appvr;eauto. apply do_step; eauto.
    unfold fill.
    apply multi_bblame_anno; eauto.
    +
    lets red': H20.
    inverts* H20.
    forwards*: value_group H12. inverts H0.
    --
    inverts H.
    right. exists.
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply step_b.
    rewrite fill_anno; eauto.
    rewrite fill_appvr.
    apply blame_step;eauto.
    apply blame_step;eauto.
    eapply Step_annov;eauto.
    unfold not;intros nt. inverts* nt. inverts H30.
    --
    inverts H20.
    inverts H.
    lets(var2&var3&hh1):H0; inverts hh1.
    right. exists.
    eapply stars_transb.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply step_b.
    rewrite fill_anno; eauto.
    rewrite fill_appvr.
    apply blame_step;eauto.
    apply blame_step;eauto.
    eapply Step_annov;eauto.
    unfold not;intros nt. inverts* nt. inverts H30.
    ++
    inductions ep1;  try solve[inverts ep1].
    ++
    inductions ep1;  try solve[inverts ep1].
Qed.


(* Lemma val_nlam_wal: forall v,
 value v ->
 nlam v ->
 walue v.
Proof.
  introv val nl.
  forwards* h1: value_group val.
  inverts* h1.
  inverts* H; inverts nl.
Qed. *)


Lemma add_right_dynf: forall v l b,
 epre nil nil e_add (e_anno v l b t_dyn) ->
 value (e_anno v l b t_dyn) ->
 (exists v' l1 b1, v = (e_anno v' l1 b1 (t_arrow t_dyn t_dyn))) /\
 epre nil nil e_add v.
Proof.
  introv ep val.
  inverts val.
  inverts H3; inverts H1; try solve[inductions ep; eauto].
  inductions ep; eauto; try solve[inductions ep; eauto].
  inductions ep; eauto; try solve[inductions ep; eauto].
Qed.


Lemma addl_right_dynf: forall i v l b,
 epre nil nil (e_addl i) (e_anno v l b t_dyn) ->
 value (e_anno v l b t_dyn) ->
 (exists v' l1 b1, v = (e_anno v' l1 b1 (t_arrow t_dyn t_dyn))) /\
 epre nil nil (e_addl i)  v.
Proof.
  introv ep val.
  inverts val.
  inverts H3; inverts H1; try solve[inductions ep; eauto].
  inductions ep; eauto; try solve[inductions ep; eauto].
  inductions ep; eauto; try solve[inductions ep; eauto].
Qed.



Lemma nlam_open3: forall e y,
  nlam e ->
  nlam (e ^^ e_var_f y).
Proof.
  introv nl.
  inverts nl; unfold open_exp_wrt_exp;simpl; eauto.
  destruct(lt_eq_lt_dec nat 0).
  inverts* s.
  eauto.
Qed.




Lemma dynamic_guarantee_chk_less: forall e1 e2 e2' T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 -> 
 step e2 (e_exp e2') ->
 (exists e1', steps e1 (e_exp e1') /\ epre nil nil e1' e2' ) \/ (exists l b, steps e1 (e_blame l b)) .
Proof.
  introv ep typ1 typ2 red. gen e2' T1 T2.
  inductions ep; intros;
  try solve[inverts* red;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* red;destruct E; unfold fill in H1; inverts* H1];
  try solve[forwards*: step_not_value red ];
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  -
    inverts* red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    + destruct E; unfold fill in H0; inverts* H0.
      *
      inverts typ1. inverts typ2.
      inverts H0. inverts H5.
      forwards* h1: Typing_chk H15. inverts h1.
      forwards* h2: Typing_chk H17. inverts h2.
      forwards*: IHep1 H3. inverts H2. 
      inverts H8. inverts H2.
      inverts H8.
      forwards*: epre_lc2 ep2.
      left.
      exists. split. apply multi_rred_app2.
       auto.  apply H2.
      unfold fill; auto. 
      right.
      lets(ll1&bb1&rred1): H2.
      exists.
      apply multi_bblame_app2; auto.
      inverts H2.
      forwards*: epre_lc2 ep2.
      apply rred1.
      *
      inverts typ1. inverts typ2. inverts H0. inverts H5. 
      forwards* h1: Typing_chk H15. inverts h1.
      forwards* h2: Typing_chk H17. inverts h2.
      forwards*: epre_valr ep1. inverts* H2.
      inverts H8.
      ++
      inverts H9. inverts H8. inverts H10.
      forwards*: IHep2 H16. inverts H10.
      ---
      inverts H14. inverts H10.
      forwards*: Typing_regular_1 H16.
      inverts H2.
      forwards*: preservation_multi_step H15 H9.
      forwards*: tpre_principle H13.
      rewrite H22 in *.
      forwards*: principle_inf H2.
      inverts H20.
      rewrite <- H23 in *. subst.
      inverts H12.
      left.
      exists(e_app x1 l1 b1 x2). split. 
      apply stars_trans with (b:=e_app x1 l1 b1 e2).
      apply multi_rred_app2;auto.  
      eapply multi_rred_app;auto.
      rewrite <- H23. reflexivity.
      unfold fill. 
      forwards*: steps_not_nlam H14.
      ---
      lets(ll1&bb1&rred1): H14.
      inverts H2.
      forwards*: tpre_principle H13.
      rewrite H20 in *. 
      inverts H2.
      forwards*: preservation_multi_step H15 H9.
      forwards*: tpre_principle H13.
      forwards*: principle_inf H2.
      rewrite <- H10 in *. subst. inverts H12.
      forwards*: Typing_regular_1 H16.
      right. exists.
      eapply stars_transb.
      apply multi_rred_app2.
      auto. apply H9.
      eapply multi_bblame_app; auto.
      rewrite <- H10. reflexivity.
      apply rred1. 
      ++
      lets(ll1&bb1&rred1): H9.
      forwards*: Typing_regular_1 H16.
      right.
      exists.
      apply multi_bblame_app2; eauto.
    +
      inverts typ1. inverts H0. 
      inverts typ2. inverts H0.
      forwards*: Typing_chk H14. inverts H0.
      forwards*: Typing_chk H19. inverts H0.
      forwards*: epre_valr ep1.
      inverts H0.
      *
      lets(vv1&rred1&vval1&epp1): H12.
      forwards*: epre_valr ep2.
      inverts H0.
      --
      lets(vv2&rred2&vval2&epp2): H13.
      forwards*: epre_lc2 ep2.
      forwards*: tpre_principle epp1.
      rewrite H7 in *. inverts H17.
      forwards*: preservation_multi_step H14 rred1.
      forwards*: preservation_multi_step H15 rred2.
      forwards*: principle_inf H17.
      rewrite <- H18 in *. subst. inverts H11.
      forwards*: principle_inf H19.
      rewrite H11 in *. subst.
      inverts H16.
      forwards* h1: steps_not_nlam rred2.
      forwards* h2: val_nlam_wal h1.
      forwards* h3: epre_wal epp2.
      forwards* h4: tdynamic_guaranteer l1 b1 epp2 H8.
      inverts h4. 
      **
      lets(vv3&rred3&epp3): H7.
      left. exists.
      splits.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply rred1.
      eapply stars_trans.
      eapply multi_rred_app. rewrite <- H18. auto.
      auto.
      apply rred2.
      apply stars_one.
      eapply Step_equal; eauto.
      apply ep_appv; eauto.
      **
      right. exists. 
      eapply stars_transb.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply rred1.
      eapply stars_trans.
      eapply multi_rred_app. rewrite <- H18.
      auto. auto.
      apply rred2.
      apply step_refl.
      apply step_b.
      eapply Step_betap; eauto.
      --
      forwards* h1: principle_inf H19.
      rewrite h1 in *. subst. inverts H16.
      forwards* h2: tpre_principle epp1.
      rewrite h1 in *.
      inverts h2.
      forwards* h3: preservation_multi_step H14 rred1.
      forwards* h4: principle_inf h3.
      rewrite h4 in *. subst.
      forwards*: epre_lc2 ep2.
      lets(ll1&bb1&rred2): H13.
      right. exists.
      eapply stars_transb.
      apply multi_rred_app2. auto.
      apply rred1.
      eapply multi_bblame_app; eauto.
      *
      forwards*: epre_lc2 ep2.
      lets(ll1&bb1&rred1): H12.
      right. exists.
      apply multi_bblame_app2; eauto.
    +
      inverts typ1. inverts H0.
      inverts typ2. inverts H0. 
      inverts H17. inverts H14.
      inverts H9.
      --
      forwards*: epre_nlamr ep1.
      left. exists. splits.
      apply step_refl.
      eapply ep_app; eauto.
      --
      forwards* h1: Typing_chk H12. inverts h1.
      forwards*: epre_valr ep1.
      inverts H7.
      ++
      lets(vv1&rred1&vval1&epp1): H8.
      forwards* h2: preservation_multi_step H12 rred1.
      forwards*: Typing_regular_1 H13.
      inverts vval1;inverts h2.
      left. exists. splits.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply rred1.
      apply stars_one.
      apply Step_betad. auto. auto.
      apply ep_app; eauto.
      ++
      forwards*: Typing_regular_1 H13.
      lets(ll1&bb11&rred1): H8.
      right. exists.
      apply multi_bblame_app2; eauto.
  -
    inverts typ1. inverts H1. inverts typ2. inverts H1.
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H1.
    forwards*: IHep H8.
    inverts H1.
    lets(e2'&red&epp): H6.
    forwards*: steps_not_nlam red.
    forwards*: multi_rred_anno A0 red.
    lets(ll1&bb1&rred1): H6.
    right. exists. 
    apply multi_bblame_anno; eauto.
    +
    forwards*: value_lc H11.
    forwards*: epre_lc2 ep.
    forwards*: epre_valr ep.
    inverts H7.
    *
    lets(v2&red&vval&epp1): H8.
    forwards*: preservation_multi_step red.
    forwards*: steps_not_nlam red.
    forwards* hh1:epre_nlam ep.
    forwards*: val_nlam_wal vval.
    forwards*: val_nlam_wal hh1.
    forwards*: tdynamic_guaranteer epp1 H H12.
    inverts H17.
    **
    lets(v2'&tred&epp2):H18.
    forwards*: multi_rred_anno A0 red.
    forwards* h1: Tred_value H12.
    forwards*: value_lc h1.
    forwards*: epre_lc2 epp1.
    destruct(value_decidable (e_anno v2 l1 b1 A0)); eauto.
    ***
    forwards*: TypedReduce_preservation H11.
    forwards* h2: value_tred_keep tred. inverts* h2.
    ***
    left.
    exists v2'. splits*.
    **
    destruct(value_decidable (e_anno v2 l1 b1 A0)); eauto.
    ***
    forwards* h1: value_tred_keep H18. inverts* h1.
    ***
    lets red': H18.
    inverts* red'.
    right. exists.
    eapply stars_transb.
    forwards h2: multi_rred_anno A0 red.
    apply h2.
    apply step_b; auto.
    *
    lets(ll1&bb1&rred1): H8.
    right. exists.
    apply multi_bblame_anno; auto.
    apply rred1.
  -
    inverts typ2. inverts H4.
    inverts red.
    +
    destruct E; unfold fill in *; inverts H4.
    forwards* hh2: Typing_regular_1 H13.
    forwards*: step_not_value H9.
    +
    inverts H11.
    inverts* H2; try solve[exfalso; apply H14; eauto].
  -
    inverts typ2. inverts H4.
    inverts red.
    +
    destruct E; unfold fill in *; inverts H4.
    forwards*: IHep H13.
    inverts H4.
    *
    lets(ee2'&rred&epp): H7.
    forwards* h1: preservation_multi_step H rred.
    forwards*: Typing_regular_1 h1.
    forwards*: preservation H0 H9.
    forwards*: steps_not_nlam rred.
    *
    right*.
    +
    forwards* h1: epre_valr ep.
    inverts* h1.
    lets(vv1& rred1 & vval1 & epp1): H4.
    forwards*: epre_nlam ep.
    forwards*: preservation_multi_step H rred1.
    forwards*: tred_right epp1.
    forwards* h2: value_group H11.
    inverts* h2. lets(var2&var3&hh1):H9; inverts hh1; try solve[forwards*: abs_nlam].
    lets(vv2& rred2 & epp2): H9.
    forwards* h3: TypedReduce_unique H12 rred2.
    inverts h3.
    left.
    exists. splits.
    apply rred1. auto.
  -
    inverts typ1. inverts H4.
    forwards*: IHep.
    inverts* H4.
    +
    lets(vv1& rred1 & epp1): H7.
    forwards*: preservation_multi_step H rred1.
    forwards*: epre_nlamr ep.
    forwards*: step_not_nlam red.
    left. exists. splits.
    apply multi_rred_anno.
    apply rred1.
    forwards*: preservation H0 red.
    +
    lets(ll1&bb1&rred1): H7.
    right. exists.
    apply multi_bblame_anno; auto.
    apply rred1.
  -
    inverts red; 
    try solve[destruct E; unfold fill in H; inverts* H];try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    +
      destruct E; unfold fill in H; inverts* H.
      *
      inverts typ1. inverts typ2.
      inverts H. inverts H4.
      forwards* h1: Typing_chk H9. inverts h1.
      forwards* h2: Typing_chk H8. inverts h2.
      forwards*: IHep1 H2. inverts H1. 
      inverts H7. inverts H1.
      inverts H7.
      forwards*: epre_lc2 ep2.
      left.
      exists. split. apply multi_rred_appv2.
       auto.  apply H1.
      unfold fill; auto. 
      right.
      lets(ll1&bb1&rred1): H1.
      exists.
      apply multi_bblame_appv2; auto.
      inverts H1.
      forwards*: epre_lc2 ep2.
      apply rred1.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards* h1: Typing_chk H9. inverts h1.
      forwards* h2: Typing_chk H8. inverts h2.
      forwards*: epre_valr ep1. inverts* H1.
      forwards*: Typing_regular_1 H11.
      inverts H7.
      ++
      lets(vv1& rred1 & vval1 & epp1): H15.
      forwards*: IHep2 H2. inverts H7.
      ---
      lets(vv2&rred2&epp2): H16.
      left. exists. splits.
      eapply stars_trans.
      apply multi_rred_appv2. auto.
      apply rred1.
      apply multi_rred_appv. auto.
      apply rred2.
      unfold fill;eauto.
      ---
      lets(ll3&bb3&rred3): H16.
      right. exists. 
      eapply stars_transb.
      apply multi_rred_appv2. auto.
      apply rred1.
      apply multi_bblame_appv. auto.
      apply rred3.
      ++
      lets(ll1&bb11&rred1): H15.
      right. exists.
      apply multi_bblame_appv2; eauto.
    +
    lets typ1': typ1.
    lets typ2': typ2.
    inverts typ2. inverts H. inverts H6.
    inverts typ1. inverts H.
    forwards*: Typing_chk H11. inverts H.
    forwards*: Typing_chk H13. inverts H.
    forwards* h1: epre_valr ep1.
    inverts h1.
    *
    lets(vv1&rred1&vval1&epp1): H.
    forwards* h2: epre_valr ep2.
    inverts h2.
    --
    lets(vv2&rred2&vval2&epp2): H12.
    forwards*: epre_lc2 ep2.
    forwards*: preservation_multi_step H11 rred1.
    forwards*: preservation_multi_step H13 rred2.
    forwards* h1: steps_not_nlam rred2.
    forwards* h2: val_nlam_wal vval2 h1.
    assert(e_appv e1 e2 ->** e_exp (e_appv vv1 vv2)).
    eapply stars_trans.
    apply multi_rred_appv2.
    auto.
    apply rred1.
    apply multi_rred_appv.
    auto.
    apply rred2.
    forwards* h3: beta_eprer epp1 epp2.
    inverts* h3.
    lets(vv3&rred3&epp3):H19.
    left.
    exists. splits.
    eapply stars_trans.
    apply H18.
    apply rred3.
    auto.
    lets(ll3&bb3&rred3):H19.
    right. exists.
    eapply stars_transb.
    apply H18.
    apply rred3.
    --
    lets(ll3&bb3&rred3):H12.
    forwards*: epre_lc2 ep2.
    right. exists.
    eapply stars_transb.
    apply multi_rred_appv2; eauto.
    apply multi_bblame_appv;eauto.
    *
    lets(ll3&bb3&rred3):H.
    forwards*: epre_lc2 ep2.
    right. exists.
    apply multi_bblame_appv2;eauto.
    +
    lets typ1': typ1.
    lets typ2': typ2.
    inverts typ2. inverts H. inverts H8.
    inverts typ1. inverts H.
    forwards*: Typing_chk H13. inverts H.
    forwards*: Typing_chk H10. inverts H.
    forwards* h1: epre_valr ep1.
    inverts h1.
    *
    lets(vv1&rred1&vval1&epp1): H.
    forwards* h2: epre_valr ep2.
    inverts h2.
    --
    lets(vv2&rred2&vval2&epp2): H14.
    forwards*: epre_lc2 ep2.
    forwards*: preservation_multi_step H13 rred1.
    forwards*: preservation_multi_step H15 rred2.
    forwards* h1: steps_not_nlam rred2.
    forwards* h2: val_nlam_wal vval2 h1.
    assert(e_appv e1 e2 ->** e_exp (e_appv vv1 vv2)).
    eapply stars_trans.
    apply multi_rred_appv2.
    auto.
    apply rred1.
    apply multi_rred_appv.
    auto.
    apply rred2.
    forwards* h3: unwrap_eprer epp1 epp2.
    inverts* h3.
    lets(vv3&rred3&epp3):H21.
    left.
    exists. splits.
    eapply stars_trans.
    apply H20.
    apply rred3.
    auto.
    lets(ll3&bb3&rred3):H21.
    right. exists.
    eapply stars_transb.
    apply H20.
    apply rred3.
    --
    lets(ll3&bb3&rred3):H14.
    forwards*: epre_lc2 ep2.
    right. exists.
    eapply stars_transb.
    apply multi_rred_appv2; eauto.
    apply multi_bblame_appv;eauto.
    *
    lets(ll3&bb3&rred3):H.
    forwards*: epre_lc2 ep2.
    right. exists.
    apply multi_bblame_appv2;eauto.
    +
    lets typ1': typ1.
    lets typ2': typ2.
    inverts typ2. inverts H. inverts H4.
    inverts typ1. inverts H.
    forwards*: Typing_chk H9. inverts H.
    forwards*: Typing_chk H11. inverts H.
    forwards* h1: epre_valr ep1.
    inverts h1.
    *
    lets(vv1&rred1&vval1&epp1): H.
    forwards* h2: epre_valr ep2.
    inverts h2.
    --
    lets(vv2&rred2&vval2&epp2): H10.
    forwards*: epre_lc2 ep2.
    forwards*: preservation_multi_step H9 rred1.
    forwards*: preservation_multi_step H11 rred2.
    forwards* h1: steps_not_nlam rred2.
    forwards* h2: val_nlam_wal vval2 h1.
    assert(e_appv e1 e2 ->** e_exp (e_appv vv1 vv2)).
    eapply stars_trans.
    apply multi_rred_appv2.
    auto.
    apply rred1.
    apply multi_rred_appv.
    auto.
    apply rred2.
    forwards* h3: addr epp1 epp2.
    inverts* h3.
    --
    lets(ll3&bb3&rred3):H10.
    forwards*: epre_lc2 ep2.
    right. exists.
    eapply stars_transb.
    apply multi_rred_appv2; eauto.
    apply multi_bblame_appv;eauto.
    *
    lets(ll3&bb3&rred3):H.
    forwards*: epre_lc2 ep2.
    right. exists.
    apply multi_bblame_appv2;eauto.
    +
    lets typ1': typ1.
    lets typ2': typ2.
    inverts typ2. inverts H. inverts H4.
    inverts typ1. inverts H.
    forwards*: Typing_chk H9. inverts H.
    forwards*: Typing_chk H11. inverts H.
    forwards* h1: epre_valr ep1.
    inverts h1.
    *
    lets(vv1&rred1&vval1&epp1): H.
    forwards* h2: epre_valr ep2.
    inverts h2.
    --
    lets(vv2&rred2&vval2&epp2): H10.
    forwards*: epre_lc2 ep2.
    forwards*: preservation_multi_step H9 rred1.
    forwards*: preservation_multi_step H11 rred2.
    forwards* h1: steps_not_nlam rred2.
    forwards* h2: val_nlam_wal vval2 h1.
    assert(e_appv e1 e2 ->** e_exp (e_appv vv1 vv2)).
    eapply stars_trans.
    apply multi_rred_appv2.
    auto.
    apply rred1.
    apply multi_rred_appv.
    auto.
    apply rred2.
    forwards* h3: addlr epp1 epp2.
    inverts* h3.
    --
    lets(ll3&bb3&rred3):H10.
    forwards*: epre_lc2 ep2.
    right. exists.
    eapply stars_transb.
    apply multi_rred_appv2; eauto.
    apply multi_bblame_appv;eauto.
    *
    lets(ll3&bb3&rred3):H.
    forwards*: epre_lc2 ep2.
    right. exists.
    apply multi_bblame_appv2;eauto.
    +
    inverts ep1; try solve[forwards*: abs_nlam].
    inverts typ2. inverts H. inverts H7.
    inverts typ1. inverts H.
    forwards*: Typing_chk H14. inverts H.
    forwards* h1: epre_valr ep2.
    inverts h1.
    *
    lets(vv1&rred1&vval1&epp1): H.
    forwards*: steps_not_nlam rred1.
    forwards* h3: val_nlam_wal vval1.
    forwards*: Typing_regular_1 H12.
    inverts H12.
    forwards*: preservation_multi_step H14 rred1.
    forwards* hh1: steps_not_nlam rred1.
    left.
    exists. splits.
    eapply stars_trans.
    apply multi_rred_appv; eauto.
    apply stars_one.
    apply Step_nbeta;eauto.
    pick fresh y.
    rewrite (subst_exp_intro y);eauto.
    assert((e ^^ e2') = [y ~> e2'] (e ^^ e_var_f y)).
    rewrite (subst_exp_intro y);eauto.
    rewrite H16.
    forwards* h6:H5.
    forwards*: epre_open h6 epp1 hh1.
    *
    forwards*: Typing_regular_1 H12.
    lets(ll3&bb3&rred3):H.
    forwards*: epre_lc2 ep2.
    right. exists.
    eapply stars_transb.
    apply multi_rred_appv2; eauto.
    apply multi_bblame_appv;eauto.
  -
    inverts* red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    + destruct E; unfold fill in *; inverts* H3.
      *
      inverts typ1. inverts typ2.
      inverts H3. inverts H8.
      forwards* h1: Typing_chk H18. inverts h1.
      forwards* h2: Typing_chk H20. inverts h2.
      forwards*: IHep1 H3. inverts H11.
      --
      inverts H12. inverts H11.
      inverts H5.
      forwards* lc: epre_lc2 ep2. inverts lc.
      forwards* h1: preservation_multi_step H18 H12.
      forwards* h2: preservation H20 H6 .
      forwards* h3: inference_unique H H18. subst.
      forwards* h4: inference_unique H0 H20. subst.
      forwards* h5: pattern_uniq H1 H15. inverts h5.
      forwards* h6: pattern_uniq H2 H14. inverts h6.
      left.
      exists. split. apply multi_rred_app2.
       auto.  apply H12.
       eapply ep_appa;eauto.
      --
      right.
      lets(lll1&bbb1&rred1): H12.
      exists.
      apply multi_bblame_app2; auto.
      inverts H5.
      forwards* lc: epre_lc2 ep2. inverts* lc.
      apply rred1.
      *
      forwards* lc: Typing_regular_1 typ2. inverts lc.
      forwards*: step_not_value H6.
    +
      inverts typ1. inverts H3. 
      inverts typ2. inverts H3.
      forwards* h1: Typing_chk H17. inverts h1.
      forwards* h2: Typing_chk H22. inverts h2.
      forwards* h3: epre_valr ep1.
      inverts h3.
      *
      lets(vv1&rred1&vval1&epp1): H13.
      forwards*: preservation_multi_step H17 rred1.
      forwards* h1: tpre_principle epp1.
      rewrite H10 in *. inverts h1.
      forwards* h2: principle_inf H15.
      rewrite h2 in *. subst. inverts H14.
      forwards* h3: inference_unique H H17. subst. inverts H1.
      forwards* h4: principle_inf H22. rewrite  h4 in *. subst.
      inverts H19.
      forwards* h5: inference_unique H0 H22. subst.
      inverts H2.
      forwards* lc: Typing_regular_1 H18.
      forwards* h6: TypedReduce_progress l1 b1 H18.
      inverts h6.
      assert(value (e_anno (e_abs e2 ll1 bb1) l1 b1 A1)).
      inverts* H18; try solve[forwards*: abs_nlam].
      forwards* h7: value_tred_keep H1. inverts h7.
      assert(value (e_anno (e_abs e2' ll2 bb2) l2 b2 B1)).
      inverts* H23; try solve[forwards*: abs_nlam].
      forwards* h8: value_tred_keep H11. inverts* h8.
      left.
      exists. splits.
      eapply stars_trans.
      apply multi_rred_app2.
      auto. apply rred1.
      apply stars_one.
      eapply Step_equal;eauto.
      eapply ep_appv; eauto.
      *
      forwards* lc: epre_lc2 ep2. inverts lc.
      lets(lll1&bbb1&rred1): H13.
      right. exists.
      apply multi_bblame_app2; eauto.
    +
      inverts typ1. inverts H0.
      inverts typ2. inverts H0. 
      inverts H18. inverts H15.
      inverts H3.
      forwards* h1:inference_unique H H18. subst.
      forwards* h1: Typing_chk H18. inverts h1.
      inverts H1.
      --
      inverts H13. inverts H2.
      left.
      exists. splits.
      apply step_refl.
      eapply ep_appa; eauto.
      eapply ep_annor;eauto.
      forwards* h1: epre_nlamr ep1.
      --
      forwards*: epre_valr ep1.
      inverts H1.
      lets(vv1&rred1&vval1&epp1): H3.
      forwards* h2: preservation_multi_step H18 rred1.
      forwards*: Typing_regular_1 H20.
      inverts vval1;inverts h2.
      left. exists. splits.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply rred1.
      apply stars_one.
      apply Step_betad. auto. auto.
      eapply ep_appa; eauto.
      inverts* H2.
      forwards*: Typing_regular_1 H20.
      lets(lll1&bbb11&rred1): H3.
      right. exists.
      apply multi_bblame_app2; eauto.
Qed.



Lemma dynamic_guarantee_chk: forall e1 e2 e1' T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 -> 
 step e1 (e_exp e1') ->
 exists e2', steps e2 (e_exp e2') /\ epre nil nil e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' T1 T2.
  inductions ep; intros;
  try solve[inverts* red;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* red;destruct E; unfold fill in H1; inverts* H1];
  try solve[forwards*: step_not_value red ];
  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
  - 
    inverts* red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    + 
      destruct E; unfold fill in H0; inverts* H0.
      *
      inverts typ1. inverts typ2.
      inverts H0. inverts H5.
      forwards* h1: Typing_chk H15. inverts h1.
      forwards* h2: Typing_chk H17. inverts h2.
      forwards*: IHep1 H3. inverts H2. inverts H8.
      exists. split. inverts H2. apply multi_rred_app2.
      forwards*: epre_lc ep2. apply H8.
      inverts H2.
      forwards* h3: step_not_nlam H3.
      unfold fill. eauto.
      *
      inverts typ1. inverts typ2. inverts H0. inverts H5. 
      forwards* h1: IHep2 H16. inverts h1. inverts H0.
      inverts H2. 
      forwards* h2: Typing_chk H15. inverts h2.
      forwards* h3: Typing_chk H17. inverts h3.
      forwards*: epre_val ep1. 
      inverts H9. inverts H13. inverts H19.
      forwards*: Typing_regular_1 H16.
      forwards*: epre_lc ep2.
      forwards*: preservation_multi_step H17 H9.
      forwards*: principle_inf H22.
      inverts H11.
      --
      exists(e_app x2 l2 b2 x). split. 
      apply stars_trans with (b:=e_app x2 l2 b2 e2').
      apply multi_rred_app2;auto.
      eapply multi_rred_app;auto.
      rewrite TEMP. auto.
      unfold fill. 
      forwards* h4: epre_nlam ep2.
      forwards* h5: step_not_nlam H3.
      --
      inverts H13;simpl in *; inverts TEMP.
      inverts H23; try solve[simpl in *;inverts H11]; simpl in *.
      forwards*: epre_lit_false H20.
      +++
      inverts H2; try solve[forwards*: abs_epre_true2 H19];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int];
      try solve[inverts H17].
      forwards*: epre_abs p b p b H20.
      forwards*: value_group H14.
      inverts* H2; inverts H26;
      try solve[forwards*: abs_epre_true2 H20];
      try solve[forwards*: absr_epre_true2 ep].
      lets (var2&var3&hh1): H2; inverts hh1.
      forwards*: abs_epre_true2 H20.
      exists. splits.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply H9.
      eapply stars_trans.
      apply stars_one.
      eapply Step_betad; eauto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app; eauto.
      apply do_step; eauto.
      eapply Step_annov; eauto.
      unfold not;intros nt; inverts* nt. inverts H32.
      simpl in *.
      eapply multi_rred_app; simpl. auto.
      eapply value_fanno; eauto. simpl; reflexivity.
      apply H5.
      eapply ep_app; eauto.
      forwards* h1: epre_nlam ep2.
      forwards* h2: steps_not_nlam H5.
      forwards* h3: epre_nlamr H8.
      +++
      inverts H11.
      forwards*: remove_left_dyn H20.
      inverts H11; try solve[inverts H23; inverts H11].
      inverts H22.
      exists. splits.
      eapply stars_trans.
      apply multi_rred_app2. auto.
      apply H9.
      eapply stars_trans.
      apply stars_one.
      eapply Step_betad; eauto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app; eauto.
      apply do_step; eauto.
      eapply Step_annov; eauto.
      eapply TReduce_vany; eauto.
      unfold not;intros nt; inverts* nt. inverts H30.
      simpl in *.
      eapply multi_rred_app; simpl. auto.
      eapply value_fanno; eauto.
      apply H5.
      eapply ep_app; eauto.
      forwards*: step_not_nlam H3.
      lets (var1&var2&var3&hh1): H23; inverts hh1.
    +
      inverts typ1. inverts H0. 
      inverts typ2. inverts H0.
      forwards* h1: Typing_chk H14. inverts h1.
      forwards* h2: Typing_chk H19. inverts h2.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H10.
      forwards*: epre_val ep2.
      lets(vv2&red2&val2&epp2):H12.
      forwards*: principle_inf H14.
      forwards*: tpre_principle epp1; simpl in *.
      rewrite H13 in *. subst*.
      inverts H11.
      forwards*: preservation_multi_step H19 red1.
      forwards*: preservation_multi_step H20 red2.
      inverts val1; simpl in *; inverts H17; try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int];
      try solve[inverts H6].
      *
      inverts epp1; try solve[forwards*: abs_nlam]; simpl in *; subst.
      inverts H13.
      forwards* h1: epre_nlam ep2.
      forwards* h2: steps_not_nlam red2.
      forwards* h3: val_nlam_wal h2.
      forwards* h4: val_nlam_wal H6.
      forwards* h5: tdynamic_guarantee l2 b2 epp2 H8.
      lets(vv3&ttred&epp3):h5.
      forwards*: value_lc H5.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 H17 red1.
      forwards*: multi_rred_app (e_abs e l0 b) l2 b2 red2.
      exists. splits.
      eapply stars_trans.
      apply H21. 
      eapply stars_trans.
      apply H22.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      apply ep_appv; eauto.
      *
      inverts H7. inverts H16.
      forwards* h1:val_nlam_wal H.
      forwards* h2: epre_nlam ep2.
      forwards* h3: steps_not_nlam red2.
      forwards* h4: val_nlam_wal h3.
      forwards*: tdynamic_guarantee l2 b2 epp2 H25 H8.
      lets(vv3&ttred&epp3):H7.
      forwards*: value_lc H5.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 H17 red1.
      forwards*: multi_rred_app (e_anno v p b (t_arrow A4 A2)) red2.
      exists. splits.
      eapply stars_trans.
      apply H22. 
      eapply stars_trans.
      apply H23.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      apply ep_appv; eauto.
      *
      inverts H21; inverts H18; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
      forwards*: epre_lit_false epp1.
      --
      inverts H7. inverts H16.
      forwards* h1: val_nlam_wal H.
      forwards* h2: epre_nlam ep2.
      forwards* h3: steps_not_nlam red2.
      forwards* h4: val_nlam_wal val2.
      forwards*: tdynamic_guarantee epp2 H8.
      lets(vv&ttred&epp):H7.
      forwards*: value_lc H6.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 e2' red1.
      forwards*: multi_rred_app (e_anno (e_abs e l0 b0) p b (t_arrow t_dyn t_dyn)) red2.
      exists. splits.
      eapply stars_trans.
      apply H21.
      eapply stars_trans.
      eapply stars_one.
      apply Step_betad; eauto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app; eauto.
      apply do_step; eauto.
      eapply Step_annov; eauto.
      unfold not;intros nt;inverts nt. inverts H30.
      simpl.
      eapply stars_trans.
      apply H22.
      apply stars_one.
      eapply Step_equal; simpl; eauto.
      forwards*: epre_abs epp1.
      forwards*: epre_nlamr epp1.
      forwards* h5: value_group H5.
      inverts* h5.
      lets (var2&var3&hh1): H24; inverts hh1; try solve[inverts H23].
      --
      forwards*: remove_left_dyn epp1.
      inverts H18; try solve[lets (var1&var2&var3&hh1): H21; inverts hh1].
      inverts H7. inverts H16. 
      inverts H28. inverts H7.
      forwards*: value_lc H5.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 l2 b2 H23 red1.
      forwards*: multi_rred_app (e_anno v0 p0 b0 (t_arrow t_dyn t_dyn)) l2 b2 red2.
      forwards*: value_lc val2.
      forwards* hhh1: value_group H6. 
      forwards* hhh2: value_group val2. 
      inverts hhh1; try solve[lets (var1&var2&var3&hh1): H27; inverts* hh1; try solve[inverts H]].
      inverts hhh2;
      try solve[lets (var1&var2&var3&hh1): H28; inverts* hh1; try solve[inverts H]].
      forwards* hh3: tdynamic_guarantee l2 b2 epp2 H8.
      lets(vv3&ttred&epp3):hh3.
      exists. splits.
      eapply stars_trans.
      apply H24.
      eapply stars_trans.
      apply stars_one.
      apply Step_betad.
      eapply value_dyn; simpl.
      auto.
      eapply value_fanno; auto. apply H22.
      auto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app.
      apply do_step.
      auto.
      apply Step_annov.
      eapply value_dyn; simpl.
      auto.
      eapply value_fanno; auto. apply H22.
      apply TReduce_vany.
      auto.
      unfold not; intros nt; inverts* nt. inverts H36.
      unfold fill.
      eapply stars_trans.
      apply H25.
      apply stars_one.
      eapply Step_equal; simpl .
      eapply value_fanno.
      auto.
      apply H22.
      auto.
      reflexivity.
      apply ttred.
      apply ep_appv.
      auto. auto.
      forwards* hh4: epre_wal epp2.
      lets (var1&var2&var3&hh1): H28; inverts* hh1. inverts hh4.
      (* inverts hhh2. 
      forwards* hh5: epre_walr epp2.
      inverts H27. inverts hh5.
      inverts H27. inverts H28.
      assert(value (e_anno ((e_abs x2 ll1 bb1)) l2 b2 t_dyn)); auto.
      forwards* hh5: TypedReduce_progress l2 b2 H11.
      inverts hh5. 
      forwards* hh6: value_tred_keep H28. inverts hh6.
      exists. splits.
      eapply stars_trans.
      apply H24.
      eapply stars_trans.
      apply stars_one.
      apply Step_betad.
      eapply value_dyn;simpl.
      auto.
      eapply value_fanno.
      auto.
      apply H22.
      auto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app.
      apply do_step.
      auto.
      apply Step_annov.
      eapply value_dyn;simpl.
      auto.
      eapply value_fanno.
      auto.
      apply H22.
      apply TReduce_vany.
      auto.
      unfold not; intros nt; inverts* nt. inverts H36.
      unfold fill.
      eapply stars_trans.
      apply H25.
      apply stars_one.
      eapply Step_equal; simpl ;auto.
      eapply value_fanno.
      auto.
      apply H22.
      inverts H. *)
      *
      inverts H7. inverts H16.
      forwards*: tdynamic_guarantee epp2 H23 H8.
      forwards* h1:val_nlam_wal H6.
      forwards* h2: epre_nlam ep2.
      forwards* h3: steps_not_nlam red2.
      forwards* h4: val_nlam_wal h3.
      lets(vv&ttred&epp):H7.
      forwards*: value_lc H5.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 e2' red1.
      forwards*: multi_rred_app e_add red2.
      exists. splits.
      eapply stars_trans.
      apply H21.
      eapply stars_trans.
      eapply H22.
      eapply stars_one.
      eapply Step_equal; simpl;eauto.
      eapply ep_appv; eauto.
      *
      inverts H7. inverts H16.
      forwards* hhh1: value_group H5. 
      forwards* hhh2: value_group val2. 
      inverts hhh1. inverts hhh2. 
      forwards* hhh3: tdynamic_guarantee epp2 H23 H8.
      forwards*: val_nlam_wal H.
      lets(vv&ttred&epp):hhh3.
      forwards*: value_lc H5.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 e2' red1.
      forwards*: multi_rred_app (e_addl i5) red2.
      exists. splits.
      eapply stars_trans.
      apply H22.
      eapply stars_trans.
      eapply H24.
      eapply stars_one.
      eapply Step_equal; simpl;eauto.
      eapply ep_appv; eauto.
      forwards* hhh4: epre_wal epp2.
      forwards*: epre_nlam epp2.
      lets (var1&var2&var3&hh1): H16; inverts* hh1. inverts H17.
      lets (var1&var2&var3&hh1): H16; inverts* hh1. inverts hhh4.
      forwards* hhh5: epre_walr epp1.
      lets (var1&var2&var3&hh1): H7; inverts* hh1. inverts hhh5.
      +
      inverts typ1. inverts H0. 
      inverts typ2. inverts H0.
      forwards* h1: Typing_chk H12. inverts h1.
      forwards* h2: Typing_chk H17. inverts h2.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H8.
      forwards*: tpre_principle epp1; simpl in *.
      inverts val1; simpl in *; inverts H10.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 l2 b2 H10 red1.
      exists. splits.
      eapply stars_trans.
      apply H16.
      apply stars_one.
      apply Step_betad; eauto.
      apply ep_app; eauto.
  -
    inverts typ1. inverts H1. inverts typ2. inverts H1.
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H1.
    forwards*: IHep H8.
    lets(e2'&red&epp): H1.
    forwards*: epre_nlam ep.
    forwards*: steps_not_nlam red.
    forwards*: epre_nlamr epp.
    forwards*: multi_rred_anno A red.
    +
    forwards*: value_lc H11.
    forwards*: epre_lc ep.
    forwards* h1: epre_val ep.
    lets(v2&red&vval&epp1): h1.
    forwards*: preservation_multi_step red.
    forwards* h2: tdynamic_guarantee epp1 H H12.
    forwards*: val_nlam_wal H11.
    forwards*: epre_nlam ep.
    forwards*: steps_not_nlam red.
    forwards*: val_nlam_wal vval.
    lets(v2'&tred&epp2):h2.
    forwards*: multi_rred_anno A red.
    forwards*: Tred_value H12.
    forwards*: value_lc H9.
    forwards*: epre_lc epp1.
    destruct(value_decidable (e_anno v2 l2 b2 A)); eauto.
    *
    forwards*: TypedReduce_preservation H12.
    forwards*: value_tred_keep tred. inverts* H19.
    *
    exists v2'. splits*.
  -
    inverts typ1. inverts H4.
    forwards*: Typing_regular_1 H13.
    forwards*: step_not_value red.
    inverts* H1.
  -
    inverts typ2. inverts H4.
    forwards*: IHep red.
    lets(ee2'&rred&epp): H4.
    forwards*: preservation_multi_step H0 rred.
    forwards*: Typing_regular_1 H7.
    forwards*: preservation H red.
    forwards*: step_not_nlam red.
    exists(e_anno ee2' l b A0).
    splits*.
    apply multi_rred_anno; auto.
  -
    inverts typ1. inverts H4.
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H4.
    forwards* h1: IHep H9.
    lets(e2'&red&epp): h1.
    forwards*: preservation_multi_step H0 red.
    forwards*: preservation H H9.
    forwards*: steps_not_nlam red.
    +
    forwards* h1: epre_val ep.
    lets(v2&red&vval&epp): h1.
    forwards*: preservation_multi_step H0 red.
    forwards*: tred_left epp H1.
    forwards*: epre_nlamr ep.
  -
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    inverts red;  try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    +
      destruct E; unfold fill in H; inverts* H.
      *
      forwards* h1: Typing_chk H4. inverts h1.
      forwards* h2: Typing_chk H9. inverts h2.
      forwards*: IHep1 H10. inverts H1. 
      inverts H13. inverts H1.
      inverts H8.
      forwards*: epre_lc ep2.
      exists. split. apply multi_rred_appv2.
       auto.  apply H13.
      unfold fill; auto. 
      *
      forwards*: Typing_chk H4. inverts H.
      forwards*: Typing_chk H9. inverts H. inverts H8.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H.
      forwards*: Typing_regular_1 H11.
      forwards* h1: IHep2 H10.
      lets(vv3&rred3&epp3): h1.
      exists. split. 
      eapply stars_trans. 
      apply multi_rred_appv2.
      auto. apply red1.
      apply multi_rred_appv.
       auto.  apply rred3.
      unfold fill; auto. 
    +
   forwards* hh1: Typing_chk H9. inverts hh1.
   forwards* h1: epre_val ep1.
   lets(vv1&rred1&vval1&epp1): h1.
   forwards* h2: epre_val ep2.
   lets(vv2&rred2&vval2&epp2): h2.
   inverts H4.
   forwards*: preservation_multi_step H9 rred1.
   forwards*: preservation_multi_step H11 rred2.
   forwards*: epre_wal epp2.
   forwards* h3:  beta_epre epp1 epp2.
   lets(vv4&rred4&epp4): h3.
    forwards*: Typing_regular_1 H11.
    exists. splits.
    eapply stars_trans.
    eapply multi_rred_appv2.
    auto.
    apply rred1.
    eapply stars_trans.
    eapply multi_rred_appv.
    auto.
    apply rred2.
    eapply rred4.
    auto.
    +
    forwards* hh1: Typing_chk H9. inverts hh1.
    forwards* h1: epre_val ep1.
    lets(vv1&rred1&vval1&epp1): h1.
    forwards* h2: epre_val ep2.
    lets(vv2&rred2&vval2&epp2): h2.
    inverts H4.
    forwards*: preservation_multi_step H9 rred1.
    forwards*: preservation_multi_step H11 rred2.
    forwards*: epre_wal epp2.
    forwards* h3: unwrap_epre epp1 epp2.
    lets(vv4&rred4&epp4): h3.
    forwards*: Typing_regular_1 H11.
    exists. splits.
    eapply stars_trans.
    eapply multi_rred_appv2.
    auto.
    apply rred1.
    eapply stars_trans.
    eapply multi_rred_appv.
    auto.
    apply rred2.
    eapply rred4.
    auto.
    +
    forwards* hh1: Typing_chk H9. inverts hh1.
    forwards* h1: epre_val ep1.
    lets(vv1&rred1&vval1&epp1): h1.
    forwards* h2: epre_val ep2.
    lets(vv2&rred2&vval2&epp2): h2.
    inverts H4.
    forwards*: preservation_multi_step H9 rred1.
    forwards*: preservation_multi_step H11 rred2.
    forwards*: epre_wal epp2.
    forwards* h3: add epp1 epp2.
    lets(vv4&rred4&epp4): h3.
    forwards*: Typing_regular_1 H11.
    exists. splits.
    eapply stars_trans.
    eapply multi_rred_appv2.
    auto.
    apply rred1.
    eapply stars_trans.
    eapply multi_rred_appv.
    auto.
    apply rred2.
    eapply rred4.
    auto.
    +
    forwards* hh1: Typing_chk H9. inverts hh1.
    forwards* h1: epre_val ep1.
    lets(vv1&rred1&vval1&epp1): h1.
    forwards* h2: epre_val ep2.
    lets(vv2&rred2&vval2&epp2): h2.
    inverts H4.
    forwards*: preservation_multi_step H9 rred1.
    forwards*: preservation_multi_step H11 rred2.
    forwards*: epre_wal epp2.
    forwards* h3: addl epp1 epp2.
    lets(vv4&rred4&epp4): h3.
    forwards*: Typing_regular_1 H11.
    exists. splits.
    eapply stars_trans.
    eapply multi_rred_appv2.
    auto.
    apply rred1.
    eapply stars_trans.
    eapply multi_rred_appv.
    auto.
    apply rred2.
    eapply rred4.
    auto.
    +
    inverts ep1; try solve[forwards*: abs_epre_true2 ep1];
    try solve[forwards*: absr_epre_true2 ep1];
    try solve[forwards*: abs_nlam].
    forwards* hh1: Typing_chk H11. inverts hh1.
    forwards* h2: epre_val ep2.
    lets(vv2&rred2&vval2&epp2): h2.
    inverts H4.
    forwards*: preservation_multi_step H11 rred2.
    forwards*: epre_wal epp2.
    forwards*: Typing_regular_1 H9.
    inverts H9.
    exists. splits.
    eapply stars_trans.
    eapply multi_rred_appv.
    auto.
    apply rred2.
    eapply stars_one.
    eapply Step_nbeta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y);eauto.
    assert((e0 ^^ vv2) = [y ~> vv2] (e0 ^^ e_var_f y)).
    rewrite (subst_exp_intro y);eauto.
    rewrite H9.
    forwards* h6:H17.
    forwards*: epre_open h6 epp2.
  -
     inverts* red; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int].
    + 
      destruct E; unfold fill in *; inverts* H3.
      *
      inverts typ1. inverts typ2.
      inverts H3. inverts H8.
      forwards* h1: Typing_chk H18. inverts h1.
      forwards* h2: Typing_chk H20. inverts h2.
      forwards*: IHep1 H6. inverts H11. inverts H12.
      exists. split. inverts H5. apply multi_rred_app2.
      forwards*: epre_lc ep2. 
      inverts* H5. apply H11.
      forwards*: preservation_multi_step H20 H11.
      forwards*: preservation H18 H6.
      eapply ep_appa; eauto.
      forwards* h3: inference_unique H H18.
      forwards* h4: inference_unique H0 H20.
      subst.
      forwards* h5: pattern_uniq H1 H15. inverts h5.
      forwards* h6: pattern_uniq H2 H14. inverts h6.
      auto.
      *
      forwards* lc: Typing_regular_1 typ1. inverts lc.
      forwards*: step_not_value H6.
    +
       forwards* lc: Typing_regular_1 typ2. inverts lc.
       inverts typ1. inverts H3. 
       inverts typ2. inverts H3.
       forwards* h1: Typing_chk H19. inverts h1.
       forwards* h2: Typing_chk H24. inverts h2.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H15.
      forwards* h3: principle_inf H19.
      forwards* h4: principle_inf H.
      forwards*: tpre_principle epp1; simpl in *.
      rewrite h3 in *. subst*.
      inverts H16. inverts H1.
      forwards*: preservation_multi_step H24 red1.
      forwards* h5: principle_inf H1.
      inverts H17.
      rewrite <- H18 in *.  subst.
      *
        inverts H21.
        inverts val1;inverts H1.
        assert(value (e_anno (e_abs e2 ll1 bb1) l1 b1 A1)).
        inverts* H20; try solve[forwards*: abs_nlam].
        assert(value (e_anno (e_abs e2' ll2 bb2) l2 b2 t_dyn)).
        inverts* H25; try solve[forwards*: abs_nlam].
        forwards* h1: TypedReduce_progress l2 b2 H25. inverts h1.
        forwards* h2: value_tred_keep H21. inverts h2.
        forwards* h4: value_tred_keep H11. inverts h4.
        assert((principal_type v) = (t_arrow t_dyn t_dyn)).
        inverts H16; inverts H10; simpl; auto.
        forwards*: epre_lit_false epp1.
        inverts H16; simpl in *;inverts H23.
        ++
        forwards*: epre_abs p b p b epp1.
        forwards* h1: value_group H8.
        inverts* h1;
        try solve[ lets (var1&var2&var3&hh1): H16; inverts* hh1; try solve[
          forwards*: abs_epre_true2 epp1
        ]].
        forwards* h6: inference_unique H0 H24.
        subst. inverts H2.
        exists. splits.
        eapply stars_trans.
        apply multi_rred_app2.
        auto.
        apply red1.
        eapply stars_trans.
        eapply stars_one.
        apply Step_betad; auto.
        eapply stars_trans.
        rewrite fill_app.
        apply stars_one.
        eapply do_step; auto.
        apply Step_annov; eauto.
        unfold not;intros nt;inverts nt. inverts H31.
        unfold fill.
        apply stars_one.
        eapply Step_equal;simpl;eauto.
        eapply ep_appv; eauto.
        ++
        forwards* h6: inference_unique H0 H24.
        subst. inverts H2.
        forwards* h7: remove_left_dyn epp1.
        inverts h7; try solve[inverts* H2;inverts H16].
        exists. splits.
        eapply stars_trans.
        apply multi_rred_app2.
        auto.
        apply red1.
        eapply stars_trans.
        eapply stars_one.
        apply Step_betad; auto.
        apply value_dyn;eauto.
        eapply stars_trans.
        rewrite fill_app.
        apply stars_one.
        eapply do_step; auto.
        apply Step_annov; eauto.
        apply TReduce_vany; eauto.
        unfold not;intros nt;inverts nt. inverts H32.
        unfold fill.
        apply stars_one.
        eapply Step_equal;simpl;eauto.
        eapply ep_appv; eauto.
        lets (var1&var2&var3&hh1): H2; inverts* hh1.
      *
        forwards* h1: principle_inf H1.
        rewrite h1 in *. subst.
        forwards* h2: preservation_multi_step H0 red1.
        forwards* h4: principle_inf h2.
        rewrite h4 in *. subst.
        inverts H21. inverts H2.
        assert(value (e_anno (e_abs e2 ll1 bb1) l1 b1 A1)). 
        inverts* H20; try solve[forwards*: abs_nlam].
        assert(value (e_anno (e_abs e2' ll2 bb2) l2 b2 B1)). 
        inverts* H25; try solve[forwards*: abs_nlam].
        forwards* h6: value_tred_keep H11. inverts h6.
        forwards* h8: TypedReduce_progress l2 b2 H25.
        inverts h8.
        forwards* h9: value_tred_keep H16. inverts h9.
        exists. splits.
        eapply stars_trans.
        apply multi_rred_app2.
        auto.
        apply red1.
        eapply stars_one.
        eapply Step_equal; eauto.
        eapply ep_appv;eauto.
    +
       forwards* lc: Typing_regular_1 typ2. inverts lc.
       inverts typ1. inverts H3. 
       inverts typ2. inverts H3.
       inverts H17. inverts H14.
       inverts H. inverts H1.
       forwards* h2: Typing_chk H22. inverts h2.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H1.
      forwards*: tpre_principle epp1; simpl in *.
      inverts H3. 
      forwards*: preservation_multi_step H22 red1.
      forwards* h5: principle_inf H3.
      rewrite h5 in *.
      inverts H14. inverts H19.
      inverts val1;inverts H3.
      forwards* h6: inference_unique H0 H22.
      subst.
      inverts H2.
      exists. splits.
      eapply stars_trans.
      apply multi_rred_app2.
      auto.
      apply red1.
      apply stars_one.
      apply Step_betad; eauto.
      eapply ep_appa;eauto.
Qed.



Lemma dynamic_guarantee_dir: forall e1 e2 e1' dir T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e1 (e_exp e1') ->
 exists e2', steps e2 (e_exp e2') /\ epre nil nil e1' e2'.
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  - forwards*: Typing_chk typ1. inverts H. 
    forwards*: Typing_chk typ2. inverts H.
    forwards*: dynamic_guarantee_chk H0 H1.
  - forwards*: dynamic_guarantee_chk typ1 typ2.
Qed.



Lemma dynamic_guarantee_less: forall e1 e2 e2' dir T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e2 (e_exp e2') ->
 (exists e1', steps e1 (e_exp e1') /\ epre nil nil e1' e2') \/ exists l b, steps e1 (e_blame l b).
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  - forwards*: Typing_chk typ1. inverts H. 
    forwards*: Typing_chk typ2. inverts H.
    forwards*: dynamic_guarantee_chk_less H0 H1.
  - forwards*: dynamic_guarantee_chk_less typ1 typ2.
Qed.


Lemma dynamic_guarantees_less: forall e1 e2 dir m2 T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value m2 ->
 steps e2 (e_exp m2) ->
 (exists m1, value m1 /\ steps e1 (e_exp m1) /\ epre nil nil m1 m2) \/ exists l b, steps e1 (e_blame l b).
Proof.
  introv ep typ1 typ2 val red. gen e1 T1 dir T2 . 
  inductions red; intros.
  - 
    destruct dir; try solve[inverts typ1].
    forwards*: Typing_chk typ2. inverts H.
    forwards*: Typing_chk typ1. inverts H.
    forwards*: epre_valr ep.
    inverts H. inverts H2. inverts* H.
    right*.
    forwards*: epre_valr ep.
    inverts H. inverts H0. inverts* H.
    right*.
  - 
    forwards*: dynamic_guarantee_less ep typ1 typ2 H.
    inverts* H0. inverts H1. inverts* H0.
    forwards*: preservation H.
    forwards*: preservation_multi_step H1.
    forwards*: IHred val H2.
    inverts* H4. inverts H5. inverts H4.
    inverts* H6. inverts H5. inverts H4.
    right. exists.
    eapply stars_transb.
    apply H1. apply H5.
Qed.



Lemma dynamic_guarantees: forall e1 e2 dir m1 T1 T2,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value m1 ->
 steps e1 (e_exp m1) ->
 exists m2, value m2 /\ steps e2 (e_exp m2) /\ epre nil nil m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  - 
    destruct dir; try solve[inverts typ1].
    forwards*: Typing_chk typ2. inverts H.
    forwards*: Typing_chk typ1. inverts H.
    forwards*: epre_val ep.
    inverts H. inverts H2. inverts* H3.
    forwards*: epre_val ep.
    inverts H. inverts H0. inverts* H1.
  - forwards*: dynamic_guarantee_dir ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: preservation H.
    forwards*: preservation_multi_step H0.
    forwards*: IHred val H2 H1 H3.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    apply stars_trans with (b := x).
    apply H0.
    apply H5. auto.
Qed.




Lemma tdynamic_guarantee_blame: forall e1 e2 A B B1 l1 b1 l2 b2,
 epre nil nil e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e2 l1 b1 B (e_blame l1 b1) ->
 TypedReduce e1 l2 b2 A (e_blame l2 b2).
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen A B B1 l1 b1 l2 b2.
  inductions ep; intros; 
  try solve[inverts* val1];
  try solve[inverts* val2];
  try solve[inverts * red].
  -
    inverts red.
    destruct(sim_decidable (principal_type e1) A0).
    +
    inverts val2.
    forwards*: tpre_principle ep.
    inverts* val1.
    forwards*: epre_sim H1 H2 tp.
    exfalso; apply H8.
    apply BA_AB; auto.
    +
    inverts typ1. inverts H2.
    inverts val2. 
    forwards*: tpre_principle ep.
    inverts* val1.
    inverts H9; simpl in * ; inverts H6.
    inverts val1.
    inverts H7; simpl in *;inverts H11; inverts* H2.
    apply TReduce_blame; eauto.
    unfold not;intros nt.
    apply H1. apply BA_AB; auto.
    *
    lets ep': ep.
    inverts ep;try solve[forwards*: absr_epre_true2 ep']; simpl in *.
    *
    inverts H2.
    inverts typ2. inverts H2. inverts H20.
    inverts H12;try solve[forwards*: abs_epre_true2 ep]; simpl in *.
    forwards*: principle_inf H16.
    inverts* val1.
    rewrite H12 in *. subst*.
    destruct A0; try solve[exfalso; apply H1; auto].
    inverts H3; try solve[inverts* H17].
    apply TReduce_blame; eauto.
    unfold not;intros nt.
    rewrite H12 in *. inverts nt.
    inverts tp; try solve[exfalso; apply H8; eauto]. 
  -
    inverts red; simpl in *.
    inverts H1.
    destruct B0; try solve[exfalso; apply H11; eauto]. 
    inverts tp. inverts typ1. inverts H1. inverts H4.
    destruct B0; try solve[exfalso; apply H11; eauto]. 
    inverts tp. inverts typ1. inverts H1. 
    eapply TReduce_blame; simpl.
    unfold not; intros nt. inverts nt.
  -
    inverts red.
    inverts val2.
    forwards*: principle_inf H0.
    forwards*: tpre_principle ep.
    inverts H6.
    rewrite <- H9 in *.
    inverts H4.
    destruct B; try solve[exfalso; apply H11; auto].
    inverts tp.
    inverts val1; simpl in *; inverts H5.
    inverts typ1. inverts H4. inverts H5.
    rewrite <- H9 in *.
    destruct B; try solve[exfalso; apply H11; auto].
    inverts H5.
    inverts tp.
    inverts typ1.
    inverts val1; simpl in *; inverts* H6; inverts* H5;inverts* H7.
  -
    inverts typ1. inverts H4.
    inverts red. 
    destruct(sim_decidable (principal_type e1) A0).
    +
    inverts H13; try solve[forwards*: 
    abs_epre_true2 ep].
    forwards*: principle_inf H8.
    inverts* val1.
    rewrite H11 in *.
    forwards*: IHep tp l b l2 b2.
    inverts* val1.
    inverts H12. 
    inverts* val1. inverts* H18.
    inverts* H15.
    + 
    inverts H13; try solve[forwards*: 
    abs_epre_true2 ep].
    inverts val2.
    assert(A1 = t_dyn).
    inverts* val1.
    forwards*: principle_inf H8.
    rewrite H11 in *. subst*.
    inverts H15; simpl in *; inverts H13.
    forwards*: epre_lit_false ep.
    destruct B; try solve[exfalso; apply H4; eauto].
    inverts* H5; inverts tp.
    destruct B; try solve[exfalso; apply H4; eauto].
    inverts* H5; inverts tp.
    subst*.
    apply TReduce_blame; eauto.
    unfold not;intros nt.
    apply H7. apply BA_AB; auto.
Qed. 



Lemma dynamic_guarantees_blame_chk: forall e1 e2 T1 T2 l1 b1,
 epre nil nil e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 ->
 step e2 (e_blame l1 b1) ->
 exists l2 b2, steps e1 (e_blame l2 b2).
Proof.
  introv ep typ1 typ2 red. gen T1 T2 l1 b1.
  inductions ep;intros; try solve[inverts* red].
  -
    inverts red; destruct E; unfold fill in *; inverts* H1.
  -
    inverts red.
    +
    destruct E; unfold fill in *; inverts H0.
    *
    inverts typ1. inverts H0.
    inverts typ2. inverts H0.
    forwards* h1: Typing_chk H17. inverts h1.
    forwards* h2: Typing_chk H12. inverts h2.
    forwards* h3: IHep1 H4.
    lets(ll1&bb1&rred1): h3. 
    forwards*: Typing_regular_1 H13.
    exists.
    apply multi_bblame_app2; eauto.
    *
    inverts typ2. inverts H0. inverts typ1. inverts H0.
    inverts H3.
    forwards* h1: Typing_chk H12.  forwards* h2: Typing_chk H17.
    inverts h1. inverts h2.   
    forwards*: epre_valr ep1.
    forwards*: Typing_regular_1 H18.
    inverts H7.
    --
    forwards h3: principle_inf H12. auto.
    rewrite h3 in *. subst. inverts H9.
    lets(vv1&rred1&vval1&epp1): H15.
    forwards*: tpre_principle epp1.
    rewrite h3 in *.
    forwards*: preservation_multi_step H17 rred1.
    forwards* h4: principle_inf H8.
    inverts H7.
    rewrite <- H9 in *. subst*. inverts H14.
    forwards* h5: IHep2 H4.
    lets(ll2&bb2&rred2): h5.
    exists. 
    eapply stars_transb.
    apply multi_rred_app2.
    auto. apply rred1.
    eapply multi_bblame_app; eauto.
    --
    lets(ll1&bb1&rred1): H15.
    exists. 
    apply multi_bblame_app2; eauto.
    +
    inverts typ1. inverts H0.
    inverts typ2. inverts H0.
    forwards* h1: Typing_chk H14.  forwards* h2: Typing_chk H19.
    inverts h1. inverts h2.
    forwards*: epre_valr ep1.
    inverts H10.
    *
    lets(vv1&rred1&vval1&epp1): H12.
    forwards*: preservation_multi_step H14 rred1.
    forwards*: tpre_principle epp1.
    rewrite H8 in *. inverts H13.
    forwards* h1: preservation_multi_step H14 rred1.
    forwards* h2: principle_inf h1.
    rewrite h2 in *. inverts H17. inverts H11.
    forwards*: principle_inf H19.
    forwards* h3: epre_valr ep2.
    inverts h3.
    lets(vv2&rred2&vval2&epp2): H13.
    forwards*: preservation_multi_step H15 rred2.
    forwards*: tdynamic_guarantee_blame A1 l1 b1 epp2 H9.
    forwards*: Typing_regular_1 H15.
    exists.
    eapply stars_transb.
    apply multi_rred_app2.
    auto. apply rred1.
    eapply stars_transb.
    eapply multi_rred_app. apply h2. 
    auto. 
    apply rred2.
    eapply step_b.
    eapply Step_betap; eauto.
    lets(ll3&bb3&rred3): H13.
    exists.
    eapply stars_transb.
    apply multi_rred_app2.
    forwards*: Typing_regular_1 H15.
    apply rred1.
    eapply multi_bblame_app; eauto.
    *
    lets(ll3&bb3&rred3): H12.
    exists.
    apply multi_bblame_app2; eauto.
    forwards*: Typing_regular_1 H15.
  -
    inverts red.
    +
    destruct E; unfold fill in *; inverts H1.
    inverts typ1. inverts H1.
    inverts typ2. inverts H1.
    forwards*: IHep.
    lets(ll3&bb3&rred3): H1.
    exists.
    apply multi_bblame_anno; auto.
    apply rred3.
    +
    inverts typ1. inverts H1. inverts typ2. inverts H1.
    forwards*: epre_valr ep.
    inverts H1.
    lets(vv1&rred1&vval1&epp1): H9.
    forwards*: preservation_multi_step H13 rred1.
    lets red1: H7. inverts red1.
    forwards*: tdynamic_guarantee_blame A0 epp1  H7.
    exists.
    eapply stars_transb.
    apply multi_rred_anno.
    apply rred1.
    forwards*: epre_lc2 epp1.
    destruct(value_decidable (e_anno vv1 l1 b1 A0)); auto.
    forwards*: value_tred_keep H10.
    inverts H14.
    apply step_b.
    eapply Step_annov; eauto.
    lets(ll3&bb3&rred3): H9.
    exists.
    apply multi_bblame_anno; auto.
    apply rred3.
  -
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    forwards*: step_not_value red.
    inverts* H2.
  -
    inverts red.
    +
    inverts typ2. inverts H5.
    destruct E; unfold fill in *; inverts* H4.
    +
    lets H9': H10.
    inverts H10. inverts H0.
    inductions ep; clear IHep.
    *
      inverts H.
      inverts H9.
      inverts H15; try solve[forwards*: abs_nlam].
      lets ep': ep.
      forwards*: epre_lc2 ep'.
      forwards*: epre_nlam ep.
      inverts* H13; simpl in *; try solve[forwards*: abs_nlam].
      forwards*: precise_type H H14.
      forwards*: epre_sim H5 H13 H2.
      forwards*: principle_inf H14.
      rewrite H18 in *.
      apply BA_AB in H17.
      exfalso; apply H12; eauto.
    *
      inverts H. 
      destruct(A); simpl in *; try solve[exfalso; apply H12; auto].
      inverts H5. inverts H18. inverts H8.
    * 
      forwards*: precise_type H4 H0.
      inverts H9.
      forwards*: principle_inf H0.
      rewrite H9 in *.
      forwards*:inference_unique H4 H.
      subst*.
      assert(sim B1 B1 ).
      apply sim_refl.
      forwards*: epre_sim H9 H2 H5.
      apply BA_AB in H10.
      exfalso; apply H12; eauto.
    *
      inverts H.
      forwards*: epre_valr ep.
      inverts H.
      lets(vv1&rred1&vval1&epp1): H8.
      forwards*: preservation_multi_step H18 rred1.
      forwards*: tdynamic_guarantee_blame B1 epp1  H9'.
      exists.
      eapply stars_transb.
      apply multi_rred_anno.
      apply rred1.
      forwards*: epre_lc2 epp1.
      destruct(value_decidable (e_anno vv1 l b B1)); auto.
      forwards*: value_tred_keep H10.
      inverts H16.
      apply step_b.
      apply Step_annov; eauto.
      lets(ll3&bb3&rred3): H8.
      exists.
      apply multi_bblame_anno; auto.
      apply rred3.
  -
    inverts typ1. inverts H4.
    forwards*: IHep H13.
    lets(ll3&bb3&rred3): H4.
    exists.
    apply multi_bblame_anno; auto.
    apply rred3.
  -
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    inverts* red.
    destruct E; unfold fill in *; inverts* H.
    +
    inverts H10.
    forwards* h1: Typing_chk H4.
    forwards* h2: Typing_chk H9.
    inverts h1. inverts h2.
    forwards* h3: Typing_regular_1 H6.
    forwards* h4: IHep1 H13.
    lets(ll3&bb3&rred3): h4.
    exists.
    eapply multi_bblame_appv2; eauto.
    +
    inverts H10.
    forwards* h1: Typing_chk H6.
    forwards* h2: Typing_chk H11.
    inverts h1. inverts h2.
    forwards* h4: IHep2 H13.
    lets(ll3&bb3&rred3): h4.
    forwards* h5: Typing_chk H4.
    forwards* h6: Typing_chk H9.
    inverts h5. inverts h6.
    forwards*: epre_valr ep1.
    inverts H15.
    *
    lets(vv1&rred1&vval1&epp1): H16.
    forwards*: preservation_multi_step H4 rred1.
    forwards* h3: Typing_regular_1 H6.
    exists.
    eapply stars_transb.
    eapply multi_rred_appv2.
    auto. apply rred1.
    eapply multi_bblame_appv; 
    eauto.
    *
    forwards* h3: Typing_regular_1 H.
    lets(ll4&bb4&rred4): H16.
    exists. eapply multi_bblame_appv2; eauto.
  -
    inverts red.
    +
    destruct E; unfold fill in *; inverts H3.
    *
    inverts typ1. inverts H3.
    inverts typ2. inverts H3.
    forwards* h1: Typing_chk H20. inverts h1.
    forwards* h2: Typing_chk H15. inverts h2.
    forwards* h3: IHep1 H7.
    lets(lll1&bbb1&rred1): h3. 
    forwards*: Typing_regular_1 H16.
    exists.
    apply multi_bblame_app2; eauto.
    *
    forwards* lc: Typing_regular_1 typ2. inverts lc.
    forwards*: step_not_value H7.
    +
    inverts* H12.
Qed.



Lemma dynamic_guarantees_blame: forall dir e1 e2 T1 T2 l1 b1 ,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 step e2 (e_blame l1 b1) ->
 exists l2 b2, steps e1 (e_blame l2 b2).
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  -
  forwards*: Typing_chk typ1.
  forwards*: Typing_chk typ2.
  inverts H. inverts H0.
  forwards*: dynamic_guarantees_blame_chk red.
  -
  forwards*: dynamic_guarantees_blame_chk red.
Qed.

