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




Lemma flike_int: 
 FLike t_int ->
 False.
Proof.
  introv fl.
  inverts* fl.
  inverts* H0.
  inverts* H2.
Qed.

Hint Resolve  flike_int: falseHd.

Ltac solve_false := try intro; try solve [false; eauto with falseHd].



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
epre E1 E2 e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
  introv ep cp Typ1 Typ2.
  gen T T'.
  inductions ep; intros;
  try solve[inverts* Typ1; inverts* Typ2].
  - inverts Typ1. inverts Typ2.
    forwards*: binds_tpre H4 H6.
  - 
    inverts* Typ1.
    inverts* Typ2.
    forwards*: IHep1 H6 H9.
    forwards*: dmatch_tpre2 H3 H4.
    inverts* H0.
  -
    inverts Typ2; eauto.
    inverts H9.
    forwards*: IHep Typ1 H0.
    forwards* h1: inference_unique H0 H3.
    inverts h1.
    forwards* h2: inference_unique H Typ1.
    inverts h2.
    auto.
  - 
    inverts Typ1; eauto.
    inverts H9.
    forwards* h1: inference_unique H0 Typ2.
    inverts* h1.
  -
    inverts* Typ1.
    inverts* Typ2.
    forwards* h: IHep1 H2 H4.
    inverts* h.
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



(* 
Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 epre E1 E2 e1 e2 ->
 Typing E1 e1 Chk t ->
 tpre t t2 ->
 Typing E2 e2 Chk t2.
Proof.
  introv cp ep typ tp. gen t t2.
  inductions ep; intros.
  - inverts typ.
    inverts H1.
    forwards*: env_less_precise_binds H6. inverts H1. inverts H3.
    forwards*: cpre_uniq cp.
    forwards*: epre_sim H2 H5 tp.
  - inverts typ. inverts H1.
    forwards*: cpre_uniq cp.
    assert(tpre t_int t_int);eauto.
    forwards*: epre_sim H2 H3 tp.
  - 
    inverts* typ. inverts H2.
    forwards*: epre_sim H3 H1 tp.
    inverts H1.
    eapply Typ_sim with (A:= (t_arrow A2 B2));auto.
    pick fresh x and apply Typ_abs;eauto.
  -
    inverts typ. inverts H.
    forwards*: Typing_chk H8. inverts H.
    forwards*: IHep1.
    inverts H.
    forwards*: precise_type ep1 H8 H2.
    forwards*: dmatch_tpre H H5.
    lets(tt1&mma&tpp1): H4.
    inverts tpp1; try solve[inverts mma].
    forwards*: IHep2 H10.
    forwards*: epre_sim H0 H12 tp.
  -
    inverts typ. inverts H0.
    forwards*: IHep H.
    forwards*: epre_sim H1 H tp.
  -
    inverts typ.
    forwards* h1: inference_unique H H3. inverts h1.
    forwards*: epre_sim H4 H1 tp.
  -
    inverts typ. 
    inverts H3. inverts H11.
    forwards* h1: inference_unique H H3. inverts h1.
    forwards*: epre_sim H4 H1 tp.
  - 
    inverts typ. inverts H.
    forwards*: Typing_chk H4. inverts H.
    forwards*: IHep1.
    inverts H. *)




Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 precision e1 e2 ->
 Typing E1 e1 Chk t ->
 tpre t t2 ->
 Typing E2 e2 Chk t2.
Proof.
  introv cp ep typ tp. gen E1 E2 t t2.
  inductions ep; intros.
  - 
    inverts typ.
    inverts H.
    forwards*: env_less_precise_binds H4. inverts H. inverts H1.
    forwards*: cpre_uniq cp.
    forwards*: epre_sim H0 H3 tp.
  - 
    inverts typ. inverts H.
    forwards*: cpre_uniq cp.
    assert(tpre t_int t_int);eauto.
    forwards*: epre_sim H0 H1 tp.
  - 
    inverts* typ.
    inverts H3.
    eapply Typ_sim with (A := (t_arrow A2 B2)); eauto.
    pick fresh x and apply Typ_abs.
    assert(cpre ((x, A1) :: E1) ((x, A2) :: E2));eauto.
    assert(tpre (t_arrow A1 B1) (t_arrow A2 B2)); auto.
    forwards*: epre_sim H4 H3 tp.
  - 
    inverts typ. inverts H.
    forwards*: Typing_chk H8. inverts H.
    forwards*: IHep1.
    inverts H;try solve[forwards*: abs_nlam].
    forwards*: precise_type2 ep1 H8 H2.
    forwards*: dmatch_tpre H H5.
    inverts H4. inverts H6. inverts H7; try solve[inverts H4].
    forwards*: IHep2 H9 H11.
    forwards*: epre_sim H0 H13 tp.
  - 
    inverts typ. inverts H0.
    forwards*: IHep H.
    forwards*: epre_sim H1 H tp.
  -
    inverts typ. inverts H. 
    assert(tpre (t_arrow t_int (t_arrow t_int t_int)) (t_arrow t_int (t_arrow t_int t_int))); auto.
    forwards*: epre_sim H0 H tp.
    forwards*: cpre_uniq cp.
  -
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




Theorem SGG_both: forall e e' T E1 E2 dir,
   precision e e' ->  
   Typing E1 e dir T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp.
  destruct dir.
  -
    forwards* h1: Typing_chk Typ1.
    inverts h1 as h2.
    forwards* h3: SGG_chk ep h2.
    inverts* h3.
    inverts* H.
    inverts h2.
    forwards* h3: inference_unique Typ1 H; substs*.
    inverts H0.
    forwards*: precise_type2 Typ1 H3.
  -
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
Qed.


Lemma epre_lc2: forall G1 G2 e1 e2,
 epre G1 G2 e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. 
  inductions ep; intros; eauto;
  try solve [inverts lc; eauto].
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
  forwards*: lc_e_abs_exists H1.
  +
  pick fresh x.
  forwards*: H0 x. inverts* H1. inverts H2.
  forwards*: lc_e_abs_exists H3.
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
  forwards*: H0 y. inverts H2.
  assert (uniq ((y, A1) :: G1)) by auto.
  solve_uniq.
  +
  pick fresh y.
  forwards*: H0 y. inverts H2.
  assert (uniq ((y, A1) :: G1)) by auto.
  solve_uniq.
Qed.



Lemma precision_refl: forall G1 G2 e,
 uniq G1 ->
 uniq G2 ->
 lc_exp e ->
 epre G1 G2 e e.
Proof.
  introv uq1 uq2 lc. gen G1 G2.
  inductions lc; intros;eauto.
  -
   forwards*: tpre_refl t1.
   forwards*: tpre_refl t2.
   pick fresh y. 
   eapply ep_abs with (L := union (singleton l) (union (dom G1) (union (dom G2) (fv_exp e))) ); intros; eauto.
  -
    forwards*: tpre_refl.  
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
  pick fresh y. 
  eapply ep_abs with (L := union L
    (union (dom G1)
      (union (dom G3)
          (union (dom G2)
            (union (dom G4)
                (union (dom F1)
                  (union (dom F2) (union (fv_exp e1) (fv_exp e2)))))))));intros; auto.
    rewrite_env (((x, A1) :: G3) ++ F1 ++ G1).
    rewrite_env (((x, A2) :: G4) ++ F2 ++ G2).
    forwards*: H0 x G1 G2 ([(x, A1)] ++ G3) ([(x, A2)] ++ G4). 
    solve_uniq.
    solve_uniq.
  -
    forwards*: Typing_weaken H H3.
    forwards*: Typing_weaken H0 H4.
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
 Typing G1 u1 Inf A ->
 Typing G2 u2 Inf B ->
 epre (GG1++G1) (GG2++G2) [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 ty1 ty2. gen u1 u2.
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
               (fv_exp u2))))))))));intros; auto.
     forwards* lc: epre_llc ep2. inverts lc.
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     assert(([x ~> u2] (e2) ^^ e_var_f x0) = [x ~> u2] (e2 ^^ e_var_f x0) ).
     rewrite subst_exp_open_exp_wrt_exp_var; auto.
     rewrite H5.
     rewrite_env (([(x0, A1)] ++ GG1) ++ G1).
     rewrite_env (([(x0, A2)] ++ GG2) ++ G2).
     forwards*: H0 x0 x  ty1 ty2.
     auto.
     auto.
  -
    forwards*: IHep1 ep2.
    eapply ep_annor; eauto.
    forwards*: Typing_subst_1 H ty1.
    forwards*: Typing_subst_1 H0 ty2.
  -
    forwards*: IHep1 ep2.
    eapply ep_annol; eauto.
    forwards*: Typing_subst_1 H ty1.
    forwards*: Typing_subst_1 H0 ty2.
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x A B  G1 G2,
 epre ( [(x,A)] ++ G1) ([(x,B)] ++ G2) e1 e2 ->
 epre G1 G2 u1 u2 ->
 Typing G1 u1 Inf A ->
 Typing G2 u2 Inf B ->
 epre (G1) (G2) [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 ty1 ty2.
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
  forwards*: Principle_inf H. rewrite H3; auto.
  inverts* val1.
  forwards*: Principle_inf H0. rewrite H3; auto.
  inverts H1.
  forwards*: Principle_inf H0. rewrite H1; auto.
Qed.



Lemma epre_dyn: forall e1 e2 t1 t2 l b,
 Typing nil e1 Inf (t_arrow t1 t2) ->
 Typing nil e2 Inf (t_arrow t_dyn t_dyn) ->
 value e1 ->
 value e2 ->
 value (e_anno e2 l b t_dyn) ->
 epre nil nil e1 (e_anno e2 l b t_dyn) ->
 epre nil nil e1 e2.
Proof.
  introv ty1 ty2 val1 wal val2 ep. gen t1 t2.
  inductions ep; intros;eauto.
  -
  inverts ty1.
  inverts* H6.
  inverts val1.
  forwards* h1: Principle_inf H0.
  rewrite h1 in *. subst*.
  -
  inverts ty1. inverts val1.
  inverts* H9.
  forwards* h1: Principle_inf H3.
  rewrite h1 in *. substs*.
Qed.




Lemma epre_value_arrow: forall v1 v2 t1 t2 tt1 tt2,
 Typing nil v1 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 epre nil nil v1 v2 ->
 value v1 ->
 value v2 ->
 principal_type v1 = (t_arrow t1 t2) ->
 ( exists v2' l b , v2 = (e_anno v2' l b t_dyn) /\ 
 principal_type v2' = t_arrow t_dyn t_dyn) \/
 (exists t3 t4 ,  principal_type v2 = (t_arrow t3 t4))  .
Proof.
  introv typ1 typ2 ep val1 val2 ty. gen tt1 tt2 t1 t2.
  inductions ep; intros;try solve[inverts* val1];
  try solve[inverts* ty];
  try solve[simpl in *; subst; inverts* H1;
  try solve[inverts* val1]].
  -
    simpl in ty. inverts ty.
    inverts* H.
    +
    inverts val1. inverts val2.
    forwards*: tpre_principle ep.
    rewrite <- H5 in *.
    inverts H as h1; try solve[ rewrite <- h1 in *; inverts* H2].
    rewrite <- H3 in *; inverts* H2.
    +
    right. exists*.
  -
    inverts* val2.
    +
    right.  exists*.
    +
    rewrite ty in *.
    forwards*: tpre_principle ep.
    rewrite ty in *.
    inverts H3 as h1; try solve[ rewrite <- h1 in *; inverts* H5].
    rewrite <- H6 in *; inverts* H5.
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
  inverts* H11.
  forwards*: tpre_principle ep; simpl in *.
  rewrite <- H14 in *. inverts H7.
  forwards*: tpre_principle ep; simpl in *.
  inverts H9.
Qed.



(* Lemma tpre_v_dyn_fun: forall v1 v2 l1 b1 l2 b2,
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
  rewrite <- H6 in *.
  inverts H5; inverts H0; inverts* H3. 
  -
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep; simpl in *.
  inverts H8; inverts H3; inverts* H6. 
  -
  clear IHep.
  inverts val1. inverts val2.
  forwards*: epre_value_arrow ep.
  inverts H3.
  +
  lets(v2'&ll&bb&eq1&eq2): H4.
  inverts* eq1.
  +
  lets(t3&t4&eq): H4.
  inverts* eq. 
Qed. *)


Lemma tpre_v_dyn_fun: forall v1 v2 l2 b2,
 value v1  ->
 value (e_anno v2 l2 b2 t_dyn) ->
 principal_type v1 = (t_arrow t_dyn t_dyn) ->
 epre nil nil v1 (e_anno v2 l2 b2 t_dyn) ->
 principal_type v2 = t_arrow t_dyn t_dyn.
Proof.
  introv val1 val2 ty ep.
  inductions ep; eauto; simpl in *.
  -
  rewrite ty in *.
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep.
  rewrite <- H6 in *.
  inverts H5; inverts H0; inverts* H3. 
  -
  inverts val2. 
  forwards* h1: tpre_principle ep; simpl in *.
  rewrite ty in *.
  inverts* H7; inverts h1;inverts* H5. 
  -
  clear IHep.
  rewrite ty in *.
  inverts val1. inverts val2.
  forwards*: epre_value_arrow ep.
  inverts H3.
  +
  lets(v2'&ll&bb&eq1&eq2): H4.
  inverts* eq1.
  +
  lets(t3&t4&eq): H4.
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
 epre nil nil v1 v2.
Proof.
  introv typ1 typ2 val1 val2 ty1 ty2 ep. gen tt1 tt2 t1 t2.
  inductions ep;intros; eauto.
  -
    inverts ty1; simpl in *. subst.
    inverts typ1. inverts typ2.
    inverts H7.
    inverts val2.
    forwards*: Principle_inf H0.
    rewrite ty2 in *. subst.
    inverts val1. 
    inverts H6.
    forwards* h1: Principle_inf H2.
    rewrite h1 in *. subst*.
  -
    inverts val2. simpl in *; inverts* ty1.
    inverts* val1.
    inverts typ1 as h1. inverts h1.
    inverts typ2 as typ2. inverts typ2.
    forwards*: IHep.
    forwards* h2: Principle_inf H3.
    rewrite h2 in *. subst.
    forwards* h3: Principle_inf H8.
    rewrite h3 in *. subst*.
Qed.


Lemma remove_left_dynarr: forall v1 v2 tt1 tt2 l2 b2,
 Typing nil v1 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 value v1 ->
 value v2 ->
 principal_type v2 = (t_arrow t_dyn t_dyn) ->
 epre nil nil v1 (e_anno v2 l2 b2 (t_arrow t_dyn t_dyn)) ->
 epre nil nil v1 v2 .
Proof.
  introv typ1 typ2 val1 val2 ty ep. gen tt1 tt2.
  inductions ep; intros; eauto.
  -
  inverts typ1. inverts H.
  inverts val1. 
  inverts H6.
  forwards* h1: Principle_inf H.
  rewrite <- H8 in *. subst.
  forwards* h2: Principle_inf typ2.
  rewrite ty in *. subst.
  eapply ep_annol; eauto.
  -
  forwards* h2: Principle_inf typ2.
  rewrite ty in *. subst.
  inverts H0. inverts H1.
  inverts val1.
  forwards*: IHep ty. 
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


Lemma cast_dyn_same: forall v0 v1 A v2 v3 tt1 tt2 l1 b1 l2 b2,
 Typing nil v3 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 value v3 ->
 value v1 ->
 epre nil nil v0 v1 ->
 epre nil nil v3 v2 ->
 value (e_anno v1 l1 b1 t_dyn) ->
 Cast v1 l2 b2 A (e_exp v2) ->
 Cast (e_anno v1 l1 b1 t_dyn) l2 b2 A (e_exp v2) \/
 (exists v4, 
  Cast (e_anno v1 l1 b1 t_dyn) l2 b2 A (e_exp v4) /\ epre nil nil v3 v4).
Proof.
  introv typ1 typ2 val3 wal ep0 ep val red.
  inductions red; eauto;
  try solve[inverts val; inverts H2];
  try solve[inverts val; inverts H1];
  try solve[inverts val; inverts H3].
  -
    inverts val. rewrite H0 in *.
    inverts H3.
    destruct(eq_type A). destruct(eq_type B). subst.
    + 
    inverts wal; simpl in *; inverts H0.
    *
    right.
    exists. splits.
    apply Cast_vany; eauto.
    inverts typ2 as typ2.
    inverts typ2. 
    forwards*: remove_left_dynarr ep.
    *
    right.
    exists. splits.
    apply Cast_vany; eauto.
    inverts typ2 as typ2.
    inverts typ2. 
    forwards*: remove_left_dynarr ep.
    +
    left.
    apply Cast_dyna; eauto.
    rewrite H0 in *. eauto.
    +
    left.
    apply Cast_dyna; eauto.
    rewrite H0 in *. eauto.
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



Lemma cast_left: forall v1 v2 v1' t2 t l b,
 Typing nil v1 Chk t ->
 Typing nil v2 Inf t2 ->
 value v1 ->
 value v2 ->
 epre nil nil v1 v2 ->
 tpre t t2 ->
 Cast v1 l b t (e_exp v1') ->
 epre nil nil v1' v2.
Proof.
  introv typ1 typ2 val1 val2 ep tp red .
  destruct t.
  -
    gen t2 v1'.
    lets ep': ep.
    inductions ep;intros;
    try solve[inverts val1];
    try solve[inverts red].
    +
    inverts* red.
    +
    inverts typ1. inverts typ2.
    inverts H0.
    inverts H9; try solve[inverts tp];
    try solve[inverts H0].
    inverts red; eauto.
    inverts H8.
    inverts* H.
    inverts val1. inverts val2.
    forwards* h1: Principle_inf H0.
    forwards* h2: Principle_inf H3.
    forwards* h3: tpre_principle ep.
    rewrite h1 in *.
    rewrite h2 in *.
    eapply ep_annor; eauto.
    +
    inverts typ2. 
    inverts tp; try solve[inverts val2].
    inverts val2.
    lets red': red.
    inverts red; 
    try solve[
      forwards hh1: flike_int H5;inverts hh1].
    *
    inverts H.
    inverts* H2.
    *
    forwards h1: flike_int H4. inverts h1.
    *
    inverts H. inverts H2.
    forwards*: IHep.
    inverts H13;
    try solve[exfalso; apply H11; eauto];
    try solve[
      forwards*: flike_int].
    eapply ep_annor; eauto.
    +
    inverts typ1. inverts H3.  
    inverts tp; try solve[inverts val2].
    *
    inverts red; 
    try solve[forwards*: flike_int]; eauto.
    *
    inverts red; 
    try solve[forwards*: flike_int]; eauto.
  -
    inverts ep; intros; try solve[inverts val1];
    try solve[inverts typ2; inverts tp].
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: flike_int].
    inverts typ1; simpl in *.
    inverts typ2; simpl in *.
    *
    inverts* H1;inverts* H2.
    +
    inverts red; simpl in *; subst.
    *
    inverts typ1. inverts H1.
    inverts typ2.
    eapply ep_annol; eauto.
    *
    inverts typ1. inverts H1.
    inverts typ2. inverts H.
    inverts H11.
    eapply ep_anno; eauto.
    *
    inverts typ1. inverts H1. 
    inverts H10.
    inverts typ2. 
    inverts H11.
    inverts val1. 
    forwards* h1: principle_inf H1.
    rewrite h1 in *. subst.
    inverts H9.
    inverts H.
    inverts val2.
    eapply ep_annor; eauto.
    forwards* h2: tpre_principle H0.
    rewrite h1 in *. 
    forwards* h3: principle_inf H4.
    rewrite h3 in *.
    auto.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: flike_int]. 
    *
    inverts H. inverts H3. inverts H2.
    inverts typ2.
    inverts val2.
    forwards* h1: principle_inf H0.
    rewrite h1 in *.
    inverts H3.
    *
    inverts H. inverts H3. inverts H2.
    inverts val2.
    forwards* h1: principle_inf H0.
    rewrite h1 in *.
    inverts H3.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve[forwards*: flike_int].
    *
    inverts typ1.
    forwards*: inference_unique typ2 H0.
    subst*.  inverts H4.
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
    inverts typ1; 
    try solve[forwards*: flike_int].
    eapply ep_annol; eauto.
    +
    inverts* H. inverts tp.
    inverts typ1; 
    try solve[forwards*: flike_int].
    inverts H1. 
    forwards* h1: Principle_inf H.
    rewrite h1 in *.
    eapply ep_annol; eauto.
    +
    inverts* H.
    +
    inverts val1.
    rewrite x in *. inverts H1. 
Qed.

(* 
Lemma epre_abs_aux: forall v e t1 t2 l1 b1 ll1 bb1,
  value v ->
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
 *)



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


(* 
Lemma epre_wal: forall v1 v2,
 epre nil nil v1 v2 ->
 value v1 ->
 value v2 ->
 value v2.
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
 value v2 ->
 value v1 ->
 value v1.
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
Qed.  *)





Lemma Cast_dgg: forall e1 e2 e1' A B A1 B1 l1 b1 l2 b2,
 epre nil nil e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 Cast e1 l1 b1 A (e_exp e1') ->
 exists e2', Cast e2 l2 b2 B (e_exp e2') /\ epre nil nil e1' e2'.
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen e1' A B A1 B1.
  inductions ep; intros; 
  try solve[inverts* val1];
  try solve[inverts* val2];
    try solve[forwards*: flike_int]; eauto.
  - (* i i *)
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
  - (* \x.e1:a1->a2 \x.e2:b1->b2 *)
    inductions red; eauto;
    try solve[forwards*: flike_int];
    try solve[inverts* tp;inverts* H]; simpl in *; subst.
    +
    inverts typ1 as typ1. inverts typ2 as typ2.
    inverts typ1 as typ1. inverts typ2 as typ2. 
    inverts* tp.
    --
      destruct(eq_type A2). destruct(eq_type B2). subst.
      ++
      exists.
      splits*.
      ++
      exists.
      splits.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor; eauto.
      ++
      exists.
      splits.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor; eauto.
    --
      assert(tpre (t_arrow A B) (t_arrow C0 D0)) as h2; auto.
      forwards* h1: epre_sim H2 H1 h2.
      exists.
      splits.
      eapply Cast_abs; simpl in *; eauto.
      eapply ep_anno; eauto.
    +
    inverts tp.
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2.
    destruct(eq_type A2). destruct(eq_type B2). subst.
    ++
    exists.
    splits*.
    ++
    exists.
    splits.
    apply Cast_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor; eauto.
    ++
    exists.
    splits.
    apply Cast_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor; eauto.
    +
    inverts tp.
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2.
    destruct(eq_type A2). destruct(eq_type B2). subst.
    ++
    exists.
    splits*.
    eapply ep_anno; eauto.
    eapply ep_annol; eauto.
    ++
    exists.
    splits.
    apply Cast_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
    ++
    exists.
    splits.
    apply Cast_anyd; eauto; simpl; eauto.
    eapply ep_anno; eauto.
  - (* anno *)
    inductions red; eauto;
    try solve[forwards*: flike_int];
    try solve[inverts* tp;inverts* H]; simpl in *; subst.
    +
      inverts H.
      *
      inverts val1. 
      inverts val2.
      forwards* h1: tpre_principle ep. rewrite <- H6 in *.
      inverts H5; simpl in *; try solve[inverts* h1; inverts H3];
      try solve[forwards*: flike_int].
      --
        inverts typ2 as typ2. inverts typ2 as typ2. 
        inverts typ2 as typ2. inverts typ2 as typ2.  
        inverts typ1 as typ1. inverts H3.
        inverts tp.
        ---
        exists. splits.
        apply Cast_dd; eauto.
        eapply ep_annol; eauto.
        ---
        inverts typ1 as typ1; inverts typ1 as typ1;  
        try solve[forwards*: flike_int]; simpl in *.
        forwards* h2: principle_inf typ1.
        rewrite h2 in *. subst. inverts H3.
        destruct(eq_type C1). destruct(eq_type D1). subst.
        ++
        exists. splits.
        apply Cast_vany; eauto.
        eapply ep_annol; eauto.
        ++
        exists. splits.
        apply Cast_dyna; simpl; eauto.
        apply ep_anno;eauto.
        ++
        exists. splits.
        apply Cast_dyna; simpl; eauto.
        apply ep_anno;eauto.
      --
        inverts H3.
        forwards*: value_lc H.
        inverts typ1 as typ1. inverts typ2 as typ2. 
        inverts typ1 as typ1. inverts typ2 as typ2.
        inverts typ2 as typ2. inverts typ2 as typ2.
        inverts typ1 as typ1.
        inverts typ2 as typ2.
        forwards* h3: Principle_inf typ1. rewrite <- h3 in *. subst. 
        inverts* tp.
        ++
        exists(e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
        eapply ep_annol; eauto.
        ++
        destruct(eq_type C2). destruct(eq_type D2). subst.
        ---
        assert(Cast (e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn)
        l2 b2 
        (principal_type (e_anno v p0 b1 (t_arrow t_dyn t_dyn))) (e_exp (e_anno v p0 b1 (t_arrow t_dyn t_dyn)))).
        apply Cast_vany; eauto.
        exists((e_anno v p0 b1 (t_arrow t_dyn t_dyn))). splits*.
        eapply ep_annol; eauto.
        eapply ep_annol; eauto.
        rewrite <- H6 in *; auto.
        ---
        exists(e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow C2 D2)). splits*.
        apply Cast_dyna; simpl;eauto.
        apply ep_anno; eauto.
        eapply ep_annol; eauto.
        rewrite <- H6 in *; auto.
        ---
        exists(e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow C2 D2)). splits*.
        apply Cast_dyna; simpl;eauto.
        apply ep_anno; eauto.
        eapply ep_annol; eauto.
        rewrite <- H6 in *; auto.
      *
        inverts typ1 as typ1. inverts typ1 as typ1.
        inverts typ2 as typ2. inverts typ2 as typ2.
        inverts val1.
        inverts val2; 
        try solve[forwards*: flike_int].
        inverts typ2; 
        try solve[forwards*: flike_int]. 
        inverts typ1 as typ1; 
        try solve[forwards*: flike_int].
        forwards* h1: Principle_inf H.  rewrite <- h1 in *. subst.
        forwards* h2: Principle_inf typ1. rewrite <- h2 in *. subst.
        inverts tp.
        --
        destruct(eq_type C0). destruct(eq_type D0). subst.
        ++
        exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        ++
        exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
        splits*.
        apply Cast_anyd; simpl; eauto.
        apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
        apply Typ_anno; eauto.
        ++
        exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
        splits*.
        apply Cast_anyd; simpl; eauto.
        apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
        apply Typ_anno; eauto.
        --
        forwards*: epre_sim (t_arrow C0 D0) (t_arrow C3 D3) H1.
        exists(e_anno (e_anno e2 l3 b3 (t_arrow C0 D0)) l2 b2 (t_arrow C3 D3)).
        splits*.
    +
      inverts tp.
      inverts val1; try solve[inverts H0].
      inverts H0.
      inverts typ1 as typ1. inverts typ1 as typ1. 
      inverts typ2 as typ2. inverts typ2 as typ2. 
      inverts* val2.
      ++
      inverts H as h1 h2. inverts h1. inverts h2. 
      exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      ++
      forwards*: value_lc H9.
      exists(e_anno e2 l3 b3 t_dyn). splits*.
    +
      inverts tp. inverts* H.
      forwards*: epre_lc ep.
    +
      inverts typ1 as typ1. inverts typ1 as typ1. 
      inverts typ2 as typ2. inverts typ2 as typ2. 
      inverts tp.
      forwards*: flike_tpre H H0.
      lets(t1&t2&eq1&eq2): H1. subst.
      inverts eq2.
      ++
      inverts val2. 
      inverts val1.
      forwards* h1: tpre_principle ep.
      rewrite <- H12 in *.
      inverts H8; inverts* h1;inverts* H6; 
      try solve[forwards*: flike_int].
      +++
        exists. splits*.
        eapply ep_annol; eauto.
      +++
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards*: value_lc H4.
      exists(e_anno (e_anno v p0 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
      apply ep_anno; eauto.
      eapply ep_annol; eauto.
      inverts typ1 as typ1; 
      try solve[forwards*: flike_int].
      forwards* h1: Principle_inf typ1. rewrite <- H12 in *. subst.
      eapply ep_annol ; eauto.
      ++
      lets(t3&t4&eq2): H4. subst.
      destruct(eq_type t3). destruct(eq_type t4). subst.
      --
        exists(e_anno (e_anno e2 l3 b3 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        apply ep_anno; eauto. 
        eapply ep_annol; eauto.
      --
        exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        apply Cast_anyd; simpl; eauto.
      --
        exists(e_anno (e_anno (e_anno e2 l3 b3 (t_arrow t3 t4)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        apply Cast_anyd; simpl; eauto.
    +
      inverts H.
      inverts typ1 as typ1. inverts typ2 as typ2. 
      inverts typ1 as typ1. inverts typ2 as typ2. 
      inverts val1.
      inverts val2.
      forwards* h1: flike_tpre tp H1.
      lets(t1&t2&eq1&eq2): h1. subst.
      forwards* h2: tpre_principle ep.
      inverts H7; inverts H5;inverts* H0; 
      try solve[forwards*: flike_int]; simpl in *;
      try solve[exfalso; apply H1; eauto].
      ++
      inverts h2 as h3. 
      +++
        rewrite <- h3 in *. inverts H6.
      +++
        inverts typ1 as typ1. 
        inverts typ1 as typ1. 
        assert(principal_type e2 = (t_arrow t_dyn t_dyn)) as h4.
        inverts H9; inverts* H5;inverts* H6.
        inverts eq2; subst.
        ++++
          exists. splits*.
        ++++
          lets(t3&t4&eq3): H0. subst.
          inverts typ2 as typ2.
          forwards* h5: principle_inf typ2.
          rewrite h5 in *. subst. inverts H6.
          destruct(eq_type t3). destruct(eq_type t4). subst.
          +++++
          rewrite <- h5.
          exists. splits.
          apply Cast_vany; eauto.
          eapply ep_annol; eauto.
          +++++
          exists.
          splits*.
          apply Cast_dyna; simpl; eauto.
          rewrite h5; eauto.
          +++++
          exists.
          splits*.
          apply Cast_dyna; simpl; eauto.
          rewrite h5; eauto.
      ++
      inverts h2 as h3. 
      +++
        rewrite <- h3 in *. inverts H6.
      +++
        inverts typ1 as typ1. 
        inverts typ1 as typ1. 
        inverts H9; inverts H7;inverts* H6;
        try solve[forwards*: flike_int].
        ++++
          inverts eq2; subst.
          +++++
          exists. splits*.
          +++++
          lets(t3&t4&eq3): H6. subst.
          inverts typ2 as typ2. inverts typ2 as typ2. 
          destruct(eq_type t3). destruct(eq_type t4). subst.
          ++++++
          exists. splits.
          apply Cast_vany; eauto.
          eapply ep_annol; eauto.
          ++++++
          exists.
          splits*.
          apply Cast_dyna; simpl; eauto.
          ++++++
          exists.
          splits*.
          apply Cast_dyna; simpl; eauto.
        ++++
          inverts eq2; subst.
          +++++
          forwards*: value_lc H0.
          exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn). splits*.
          +++++
          lets(t3&t4&eq3): H6. subst.
          inverts typ2 as typ2. inverts typ2 as typ2. 
          destruct(eq_type t3). destruct(eq_type t4). subst.
          ++++++
          assert(Cast (e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn) l2 b2
          (principal_type (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn))) (e_exp (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)))).
          apply Cast_vany; eauto.
          exists((e_anno v0 p1 b1 (t_arrow t_dyn t_dyn))). splits*.
          ++++++
          exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow t3 t4)).
          splits*.
          apply Cast_dyna; simpl; eauto.
          ++++++
          exists(e_anno (e_anno v0 p1 b1 (t_arrow t_dyn t_dyn)) l2 b2 (t_arrow t3 t4)).
          splits*.
          apply Cast_dyna; simpl; eauto.
    +
      inverts H. 
      assert(value (e_anno e2 l3 b3 t_dyn)) as h2. auto.
      assert(value (e_anno e1' l0 b0 t_dyn)) as h3. auto.
      inverts h2.
      inverts h3.
      forwards*: tpre_principle ep.
      inverts H5; simpl in *;try solve[inverts* H2].
      *
      inverts H3; try solve[inverts* H1; inverts* H]. 
      inverts tp.
      ++
        assert(t_int = (principal_type (e_lit i0))) as h1. simpl; auto.
        rewrite h1.
        exists((e_lit i0)). splits*.
      ++
        exists(e_anno (e_lit i0) l3 b3 t_dyn). splits*.
      *
      assert(principal_type e2 = (t_arrow t_dyn t_dyn)) as h2.
      inverts H3; inverts H;inverts* H1.
      inverts typ1 as typ1. 
      inverts typ1 as typ1.
      inverts typ1 as typ1.
      inverts typ1 as typ1.
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      forwards* h1: principle_inf typ2.
      rewrite h1 in *. subst.
      inverts tp.
      ++
        forwards*: value_lc H3.
        exists. splits*.
      ++
        inverts H2.
        inverts H10. inverts H12.
        rewrite <- h1.
        exists. splits; auto.
      *
      inverts tp.
      ++
        forwards*: value_lc H0.
        inverts typ1 as typ1. inverts typ1 as typ1.
        inverts typ2 as typ2. inverts typ2 as typ2.
        inverts typ1 as typ1. inverts typ1 as typ1.
        inverts typ2 as typ2.
        inverts H2.
        forwards* h1: Principle_inf typ2. rewrite h1 in *.
        exists(e_anno e2 l3 b3 t_dyn). splits*.
      ++
        inverts typ1 as typ1. inverts typ1 as typ1.
        inverts typ1 as typ1. 
        assert(principal_type e2 = (t_arrow t_dyn t_dyn)) as h1.
        inverts H3; inverts H;inverts* H1.
        inverts H2. inverts H7. inverts H9.
        rewrite <- h1.
        exists. splits.
        eapply Cast_vany; eauto.
        rewrite h1.
        auto.
  -
    inverts typ2 as typ2. 
    inverts typ2 as typ2.
    assert(value (e_anno e2 l b A2)) as h1; auto.
    inverts h1.
    +
    inverts H1.
    inverts val1; try solve[inverts H]; 
    try solve[forwards*: flike_int].
    *
      inverts H.
      inverts* red.
      ++
      simpl in *. inverts H14.
      inverts tp.
      +++
        destruct(eq_type A). destruct(eq_type B3). subst.
        ++++
        exists.
        splits*.
        ++++
        exists.
        splits.
        apply Cast_anyd; eauto; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_anno; eauto.
        ++++
        exists.
        splits.
        apply Cast_anyd; eauto; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_anno; eauto.
      +++
        forwards*: epre_sim (t_arrow A B3) (t_arrow C1 D1) H3.
        exists. splits.
        eapply Cast_abs.
        apply H.
        auto.
        apply ep_anno; eauto.
      ++
      inverts tp.
      inverts H13. inverts H8. inverts H10.
      exists. splits*.
      ++
      simpl in *.
      inverts tp.
      destruct(eq_type A). destruct(eq_type B3). subst.
      +++ 
      exists.
      splits*.
      +++
      exists.
      splits.
      apply Cast_anyd; eauto; simpl; eauto.
      apply ep_anno; eauto.
      eapply ep_anno; eauto.
      +++
      exists.
      splits.
      eapply Cast_anyd; eauto; simpl; eauto.
      apply ep_anno; eauto.
      eapply ep_anno; eauto.
    *
      inverts H.
      inverts* red.
      ++
      simpl in *. inverts H15.
      inverts tp.
      +++
        destruct(eq_type A). destruct(eq_type B3). subst.
        ++++
        exists.
        splits*.
        ++++
        exists.
        splits.
        apply Cast_anyd; eauto; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_anno; eauto.
        ++++
        exists.
        splits.
        apply Cast_anyd; eauto; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_anno; eauto.
      +++
        forwards*: epre_sim (t_arrow A B3) (t_arrow C2 D2) H5.
        exists. splits.
        eapply Cast_abs.
        apply H.
        auto.
        apply ep_anno; eauto.
      ++
      inverts tp.
      inverts H14. inverts H8. inverts H10.
      exists. splits*.
      ++
      simpl in *.
      inverts tp.
      destruct(eq_type A). destruct(eq_type B3). subst.
      +++ 
      exists.
      splits*.
      +++
      exists.
      splits.
      apply Cast_anyd; eauto; simpl; eauto.
      apply ep_anno; eauto.
      eapply ep_anno; eauto.
      +++
      exists.
      splits.
      eapply Cast_anyd; eauto; simpl; eauto.
      apply ep_anno; eauto.
      eapply ep_anno; eauto.
    *
    inverts red; try solve[inverts H12].
    ++
      inverts H.
      inverts tp; simpl in *.
      +++
      destruct(eq_type A). destruct(eq_type B3). subst.
      ++++
      exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      ++++
      inverts typ2 as typ2;
      try solve[forwards*: flike_int]. inverts H13.
      forwards* h1: inference_unique H0 typ2. inverts h1.
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
      eapply Typ_anno; eauto.
      eapply ep_anno; eauto.
      ++++
      inverts typ2 as typ2;
      try solve[forwards*: flike_int]. inverts H13.
      forwards* h1: inference_unique H0 typ2. inverts h1.
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
      eapply Typ_anno; eauto.
      eapply ep_anno; eauto.
      +++
      inverts H13.
      inverts typ2 as typ2;
      try solve[forwards*: flike_int];
      try solve[simpl; inverts* H12]. 
      forwards* h1: inference_unique H0 typ2. subst.
      assert(tpre (t_arrow A3 B1) (t_arrow C1 D1) ) as h1; auto.
      forwards*: epre_sim ((t_arrow A B3)) H3 h1.
      exists. splits.
      eapply Cast_abs; eauto.
      eapply ep_anno; eauto.
    ++
      inverts tp.
      inverts typ2 as typ2;
      try solve[forwards*: flike_int].
      forwards*: inference_unique H0 typ2. subst.
      destruct(eq_type A). destruct(eq_type B3). subst.
      +++ 
      exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      +++
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_anno; eauto.
      +++
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_anno; eauto.
    *
    inverts red; try solve[inverts H12].
    ++
    inverts H.
    inverts tp; simpl in *.
    +++
      destruct(eq_type A). destruct(eq_type B3). subst.
      ++++
      exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      ++++
      inverts typ2 as typ2;try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int]. inverts H13.
      forwards* h1: inference_unique H0 typ2. inverts h1.
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
      eapply Typ_anno; eauto.
      eapply ep_anno; eauto.
      ++++
      inverts typ2 as typ2;try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int]. inverts H13.
      forwards* h1: inference_unique H0 typ2. inverts h1.
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_annor with (B2:= (t_arrow t_dyn t_dyn)); eauto.
      eapply Typ_anno; eauto.
      eapply ep_anno; eauto.
    +++
      inverts H13.
      inverts typ2 as typ2;
      try solve[forwards*: flike_int]. 
      forwards* h1: inference_unique H0 typ2. subst.
      assert(tpre (t_arrow A3 B1) (t_arrow C1 D1) ) as h1; auto.
      forwards*: epre_sim ((t_arrow A B3)) H3 h1.
      exists. splits.
      eapply Cast_abs; eauto.
      eapply ep_anno; eauto.
    ++
    inverts tp.
    inverts typ2 as typ2;
    try solve[forwards*: flike_int].
    forwards* h1: inference_unique H0 typ2. subst.
    destruct(eq_type A). destruct(eq_type B3). subst.
    +++ 
      exists(e_anno (e_anno e2 l b (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
    +++
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_anno; eauto.
    +++
      exists(e_anno (e_anno (e_anno e2 l b (t_arrow A B3)) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      apply Cast_anyd; eauto; simpl; eauto.
      eapply ep_anno; eauto.
    +
    forwards* h1: IHep red tp.
    lets(v2'&rred&eep): h1.
    forwards*: Cast_value red.
    inverts typ1; 
    try solve[forwards*: flike_int].
    forwards*: Cast_sim red.
    inverts typ2 as typ2;
    try solve[forwards*: flike_int].
    forwards*: Cast_sim red.
    forwards*: Cast_sim rred.
    forwards*: Cast_preservation red.
    forwards*: Cast_preservation rred.
    forwards*: cast_dyn_same eep rred.
  -   
    inverts typ1 as typ1. inverts typ1 as typ1.
    inductions red;simpl in *;subst;
    try solve[forwards*: flike_int].
    +
      assert(value (e_anno e1 l b (t_arrow C D))) as h1; auto.
      inverts h1.
      inverts tp.
      *
      forwards* h2: epre_value_arrow ep.
      inverts h2.
      ++
        lets(vv2&ll1&bb1&eq1&eq2): H3. subst.
        assert(value (e_anno vv2 ll1 bb1 t_dyn)); auto.
        inverts H6.
        forwards*: value_lc H13.
        inverts H0.
        exists(e_anno vv2 ll1 bb1 t_dyn). splits*.
        eapply ep_annol; eauto.
      ++
        lets(t3&t4&eq3): H3. subst.
        destruct(eq_type t3). destruct(eq_type t4). subst.
        --
        exists(e_anno (e2) l2 b2 t_dyn). splits*.
        eapply Cast_v; eauto.
        rewrite eq3; eauto.
        --
        exists(e_anno (e_anno (e2) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        apply Cast_anyd; simpl; eauto.
        rewrite eq3; eauto.
        --
        exists(e_anno (e_anno (e2) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn). splits*.
        apply Cast_anyd; simpl; eauto.
        rewrite eq3; eauto.
      *
      forwards* h1: epre_value_arrow ep.
      inverts h1.
      lets(vv2&ll&bb&eq1&eq2): H3. subst.
      ++
        assert(value (e_anno vv2 ll bb t_dyn)) as h2; auto.
        inverts h2.
        inverts typ2 as typ2. inverts typ2 as typ2.
        inverts typ2 as typ2; 
        try solve[forwards*: flike_int].
        inverts typ1 as typ1; 
        try solve[forwards*: flike_int].
        forwards* h3: remove_left_dyn ep.
        forwards* h4: Principle_inf typ1.
        forwards* h5: Principle_inf typ2.
        rewrite eq2 in *. subst.
        rewrite <- H11 in *.
        destruct(eq_type C1). destruct(eq_type D1). subst.
        --
        exists(vv2). splits*.
        rewrite <- eq2.
        apply Cast_vany; eauto.
        eapply ep_annol; eauto.
        --
        exists(e_anno (vv2 ) l2 b2 (t_arrow C1 D1)). splits*.
        apply Cast_dyna; simpl; eauto.
        rewrite eq2; auto.
        apply ep_anno; eauto.
        --
        exists(e_anno (vv2 ) l2 b2 (t_arrow C1 D1)). splits*.
        apply Cast_dyna; simpl; eauto.
        rewrite eq2; auto.
        apply ep_anno; eauto.
      ++
        lets(t3&t4&eq3): H3. subst.
        forwards*: epre_sim (t_arrow C1 D1) H4 H1.
        forwards* h1: principle_inf H0.
        rewrite eq3 in *. subst.
        exists(e_anno (e2) l2 b2 (t_arrow C1 D1)).
        splits*.
    +
      assert(value (e_anno e1 l b A2)) as h1;auto.
      inverts tp. inverts H3;inverts h1.
      forwards* h2: Principle_inf H. 
      rewrite <- H10 in *. subst.
      inverts H6; inverts H; try solve[forwards*: abs_epre_true2 ep];
      try solve[forwards*: absr_epre_true2 ep]; 
      try solve[forwards*: flike_int].
      *
        inverts H1.
        --
        inverts val2; inverts H0.
        forwards*: value_lc H1.
        exists. splits*.
        eapply ep_annol; eauto.
        --
        inverts typ1 as typ1.
        inverts typ1 as typ1.
        inverts H6. inverts H9.
        forwards* h1: Principle_inf H0.
        exists. splits.
        apply  Cast_v; eauto.
        rewrite h1; auto.
        eauto.
      *
        inverts H1.
        --
        inverts val2; inverts H0.
        forwards*: value_lc H1.
        exists. splits*.
        eapply ep_annol; eauto.
        --
        inverts typ1 as typ1.
        inverts typ1 as typ1.
        inverts H7. inverts H11.
        forwards* h1: Principle_inf H0.
        exists. splits.
        apply  Cast_v; eauto.
        rewrite h1; auto.
        eauto.
      *
        inverts H1.
        --
        inverts val2; inverts* H0.
        exists. splits*.
        eapply ep_annol; eauto.
        --
        inverts H5. inverts H8.
        forwards* h1: principle_inf H0.
        exists. splits.
        eapply Cast_v; eauto.
        rewrite h1; eauto.
        eapply ep_annol; eauto.
      *
        inverts H1.
        --
        inverts val2; inverts* H0.
        exists. splits*.
        eapply ep_annol; eauto.
        --
        inverts H5. inverts H7.
        forwards* h1: principle_inf H0.
        exists. splits.
        eapply Cast_v; eauto.
        rewrite h1; eauto.
        eapply ep_annol; eauto.
    +
      inverts H1. inverts tp.
      assert(value (e_anno e1 l b t_dyn)) as h1.
      auto.
      inverts h1.
      inverts val2; inverts H0.
      forwards*: value_lc H5.
      exists. splits*.
    +
      inverts tp.
      forwards* h1: flike_tpre H1 H3.
      lets(t1&t2&eq1&eq2): h1. subst.
      inverts H1.
      * 
      inverts val2; inverts H0.
      forwards*: value_lc H5.
      exists(e_anno v p0 b1 t_dyn). splits*.
      eapply ep_annol; eauto.
      eapply ep_annol; eauto.
      *
      inverts eq2; try solve[inverts H1].
      lets(t3&t4&eq3): H1. inverts eq3.
      forwards* h2: principle_inf H0.
      destruct(eq_type t3). destruct(eq_type t4). subst.
      --
        exists. splits.
        apply Cast_v; eauto.
        rewrite h2 in *; auto.
        apply ep_anno; eauto. 
        eapply ep_annol; eauto.
      --
        exists. splits.
        apply Cast_anyd; simpl; eauto.
        rewrite h2 in *; eauto.
        apply ep_anno; eauto. 
      --
        exists. splits.
        apply Cast_anyd; simpl; eauto.
        rewrite h2 in *; eauto.
        apply ep_anno; eauto. 
    +
      assert(value (e_anno e1 l b t_dyn)) as h1; auto.
      inverts h1. inverts H1.
      inverts val2; inverts H0.
      forwards* h2: flike_tpre tp H4.
      lets(t1&t2&eq1&eq2): h2. 
      inverts eq2; subst.
      *
        forwards*: value_lc H6.
        exists(e_anno v p0 b1 t_dyn). splits*.
      *
        lets(t3&t4&eq3): H0. inverts eq3.
        assert(principal_type e1 = (t_arrow t_dyn t_dyn)) as h1.
        inverts H10; inverts* H8; inverts* H3.
        forwards*: tpre_v_dyn_fun h1 ep.
    +
      assert(value (e_anno e1' l b t_dyn)) as h1; auto.
      inverts h1. inverts H1.
      inverts val2; inverts H0.
      inverts H6.
      *
      inverts H8;inverts* H5.
      *
      rewrite <- H5 in *.
      forwards*: tpre_v_dyn_fun ep.
      inverts tp.
      --
        forwards*: value_lc H3.
      --
        inverts H10. inverts H12.
        inverts H9.
        forwards* h1: principle_inf H6.
        rewrite H0 in *. subst.
        rewrite <- H0.
        exists. splits.
        apply Cast_vany; eauto.
        forwards*: remove_left_dyn ep.
        eapply value_dyn; eauto.
        rewrite H0; auto.
  -
    inverts red; try solve[inverts* H4]; simpl in *.
    +
    simpl in *. inverts H7.
    inverts tp.
    exists. splits.
    apply Cast_anyd; eauto.
    eapply ep_annor; eauto.
    assert(tpre (t_arrow t_int (t_arrow t_int t_int)) (t_arrow t_int (t_arrow t_int t_int))); auto.
    assert(tpre (t_arrow A0 B0)  (t_arrow C D)); auto.
    forwards*: epre_sim H2 H1 H3.
    exists. splits.
    eapply Cast_abs; eauto.
    eapply ep_anno;eauto. 
    +
    simpl in *.
    inverts tp.
    exists. splits.
    apply Cast_anyd;eauto.
    eapply ep_annol; eauto.
    apply Typ_anno;eauto.
    eapply Typ_sim;eauto.
    eapply ep_annor;eauto.
    eapply ep_annor;eauto.
    +
    simpl in *.
    inverts tp.
    exists. splits.
    apply Cast_anyd;eauto.
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
    apply Cast_anyd; eauto.
    eapply ep_annor; eauto.
    assert(tpre ((t_arrow t_int t_int)) ((t_arrow t_int t_int))); auto.
    assert(tpre (t_arrow A0 B0)  (t_arrow C D)); auto.
    forwards*: epre_sim H2 H1 H3.
    exists. splits.
    eapply Cast_abs;eauto.
    eapply ep_anno;eauto.
    +
    inverts tp.
    exists. splits.
    apply Cast_anyd; eauto.
    eapply ep_anno; eauto.
    eapply ep_annor;eauto.
    +
    inverts tp.
    exists. splits.
    apply Cast_anyd; eauto.
    eapply ep_anno; eauto.
Qed.



Lemma Cast_dggr: forall e1 e2 e2' A B l1 b1 l2 b2 ,
 epre nil nil e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B -> 
 Cast e2 l1 b1 B (e_exp e2') ->
 (exists e1', Cast e1 l2 b2 A (e_exp e1') /\ epre nil nil e1' e2') \/
 Cast e1 l2 b2 A (e_blame l2 b2).
Proof.
  introv ep tp val1 val2 typ1 typ2 red. 
  forwards*: Cast_progress typ1.
  inverts H. destruct x; eauto.
  forwards*: Cast_dgg ep tp H0.
  lets(ee2&tred&epp):H.
  forwards*: Cast_unique red tred.
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
  rewrite <- H6 in *.
  inverts H0.
  -
  forwards*: tpre_principle ep; simpl in *.
  rewrite ty in *.
  inverts H3.
  -
  subst.
  inverts val.
  forwards*: IHep.
Qed.



Lemma cast_right: forall v1 v2 t1 t l b,
 Typing nil v1 Inf t1 ->
 Typing nil v2 Chk t ->
 value v1 ->
 value v2 ->
 epre nil nil v1 v2 ->
 tpre t1 t ->
 exists v2', Cast v2 l b t (e_exp v2') /\
 epre nil nil v1 v2'.
Proof.
  introv typ1 typ2 val1 val2 ep tp.
  destruct t.
  -
    inverts ep; intros; 
    try solve[forwards*: flike_int];
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1].
    +
    inverts typ2 as typ2. 
    inverts typ2 as typ2.
    inverts val2; try solve[inverts H0];
    try solve[inverts H5].
    inverts tp.
    inverts val1; inverts typ1.
    forwards*: tpre_principle H1; simpl in *.
    inverts H10; simpl in *; inverts* H4;inverts H7.
    exists(e_lit i0). splits*.
    apply Cast_vany; eauto.
  -
     lets ep': ep.
    inverts ep; intros;
    try solve[forwards*: flike_int];
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1];
    try solve[inverts val2].
    +
      inverts tp.
      inverts typ1 as typ1. 
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      exists. splits*.
    +
      inverts tp. inverts typ1 as typ1. 
      inverts val1.
      inverts val2.
      *
        inverts typ2 as typ2. 
        inverts typ2 as typ2.
        exists.
        splits*.
      *
        inverts typ2 as typ2.
        inverts typ2 as typ2.
        inverts typ2 as typ2.
        inverts typ1 as typ1.
        forwards* h3:principle_inf typ1.
        forwards* h1: tpre_principle H0.
        rewrite <- H9 in *. subst.
        forwards* h4:principle_inf typ2.
        rewrite h4 in *.
        assert(principal_type e2 = t_arrow t_dyn t_dyn) as h2.
        inverts H10; inverts typ2; inverts* h1;inverts* H6.
        destruct(eq_type t2).
        destruct(eq_type t3). subst.
        ---
        rewrite <- h2.
        exists.
        splits.
        eapply Cast_vany; eauto.
        eapply ep_annol; eauto.
        rewrite h2; auto.
        ---
        exists.
        splits.
        eapply Cast_dyna; simpl; auto.
        rewrite h2. auto.
        eapply ep_anno; eauto.
        ---
        exists.
        splits.
        eapply Cast_dyna; simpl; auto.
        rewrite h2. auto.
        eapply ep_anno; eauto.
    +
      inverts tp. inverts typ2 as typ2. 
      inverts typ2 as typ2.
      inverts val2.
      *
      inverts typ2 as typ2.
      forwards* h1: Principle_inf H0.
      rewrite <- H12 in *.
      subst*.
      forwards* h2: Principle_inf H.
      forwards* h3: Principle_inf typ1.
      rewrite h3 in *. subst. 
      forwards* h4: Principle_inf typ2.
      rewrite h4 in *. subst.
      exists.
      splits.
      apply Cast_abs with (C:= A) (D := B0); eauto.
      apply ep_annor with (B1:= (t_arrow A0 B))
      (B2:=(t_arrow A B0) ); auto.
      apply Typ_anno.
      apply Typ_sim with (A:= (t_arrow C D)); auto.
      *
      forwards* h1: tpre_principle H1.
      forwards* h2: Principle_inf typ1.
      rewrite h2 in *.
      assert(principal_type e2 = (t_arrow t_dyn t_dyn)) as h3.
      inverts H12; inverts h1;inverts* H9.
      forwards* h5: Principle_inf H.
      rewrite h5 in *. subst.
      destruct(eq_type t2).
      destruct(eq_type t3). subst.
      ---
      exists.
      splits.
      rewrite <- h3.
      apply  Cast_vany;eauto.
      auto.  
      ---
      exists. splits.
      eapply Cast_dyna; simpl;eauto.
      rewrite h3; auto.
      eapply ep_annor; eauto.
      ---
      exists. splits.
      eapply Cast_dyna; simpl;eauto.
      rewrite h3; auto.
      eapply ep_annor; eauto.
    +
      inverts tp. inverts typ1 as typ1.
      inverts typ2 as typ2; 
      try solve[forwards*: flike_int];
      try solve[inverts val2].
      inverts val1.
      forwards* h1: tpre_principle H1.
      rewrite <- H13 in *.
      inverts typ1 as typ1; 
      try solve[forwards*: flike_int];
      try solve[inverts H].
      forwards* h2: Principle_inf typ1.
      rewrite h2 in *. subst*.
      inverts h1 as h3.
      *
        inverts val2; inverts* h3.
        inverts typ2 as typ2.  inverts typ2 as typ2.
        inverts H4 as h4.
        --
        inverts H10; inverts* h4.
        forwards*: epre_lit_false H1.
        --
        assert(Ground (principal_type v)) as h5.
        rewrite <- h4; auto.
        forwards*: remove_left_dyn H1.
        forwards* h6: principle_inf typ2.
        rewrite h6 in *. subst.
        destruct(eq_type t2).
        destruct(eq_type t3). subst.
        ---
          rewrite <- h6.
          exists.
          splits.
          eapply  Cast_vany ; eauto.
          eapply ep_annol; eauto.
        ---
          exists. splits.
          eapply  Cast_dyna; simpl;eauto.
          rewrite h6; auto.
          eapply ep_anno; eauto.
        ---
          exists. splits.
          eapply  Cast_dyna; simpl;eauto.
          rewrite h6; auto.
          eapply ep_anno; eauto.
      *
       forwards* h5: principle_inf typ2.
       rewrite h5 in *. subst.
       exists. splits.
       eapply Cast_abs; eauto.
       eapply ep_anno; eauto.
    +
      inverts typ2. inverts H1.
      inverts typ1.
      exists. splits.
      eapply Cast_abs; eauto. 
      eapply ep_annor; eauto.
    +
      inverts typ2. inverts H1.
      inverts typ1.
      exists. splits.
      eapply Cast_abs; eauto. 
      eapply ep_annor; eauto.
  -
    inverts ep; intros; 
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
      inverts val1. 
      inverts typ1 as typ1.
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      destruct(eq_type A2).
      destruct(eq_type B2).
      subst.
      --
        exists. splits*.
      --
        exists. splits.
        eapply  Cast_anyd; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_annor; eauto.
      --
        exists. splits.
        eapply  Cast_anyd; simpl; eauto.
        eapply ep_annor; eauto.
        eapply ep_annor; eauto.
    +
      inverts val2.
      *
        inverts H.
        inverts val1.
        inverts typ1 as typ1.
        inverts typ2 as typ2.
        inverts typ2 as typ2.
        destruct(eq_type A0).
        destruct(eq_type B0).
        subst.
        --
          exists. splits*.
          eapply ep_annor; eauto.
        --
          exists. splits.
          eapply  Cast_anyd; simpl; eauto.
          eapply ep_annor; eauto.
          eapply ep_annor; eauto.
        --
          exists. splits.
          eapply  Cast_anyd; simpl; eauto.
          eapply ep_annor; eauto.
          eapply ep_annor; eauto.
      *
        inverts val1; try solve[forwards* h1: value_lc H6].
    +
      inverts val2; try solve[inverts H0].
      *
        forwards* h1: tpre_principle H1.
        rewrite <- H9 in *.
        inverts h1 as h1 h2 h3.  
        forwards* h5: principle_inf H.
        rewrite h5 in *. subst.
        destruct(eq_type A0).
        destruct(eq_type B).
        subst.
        --
        inverts typ2 as typ2. 
        inverts typ2 as typ2.
        exists(e_anno (e_anno e2 l1 b0 (t_arrow t_dyn t_dyn)) l b t_dyn).
        splits*.
        --
        inverts typ2 as typ2.   
        inverts typ2 as typ2.
        exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
        splits*.
        apply Cast_anyd; simpl;eauto.
        eapply ep_annor; eauto.
        --
        inverts typ2 as typ2.   
        inverts typ2 as typ2.
        exists(e_anno (e_anno (e_anno e2 l1 b0 (t_arrow A0 B)) l b (t_arrow t_dyn t_dyn)) l b t_dyn).
        splits*.
        apply Cast_anyd; simpl;eauto.
        eapply ep_annor; eauto.
      *
      exists(e_anno e2 l1 b0 t_dyn). splits*. 
    +
      inverts val1.
      *
      inverts typ1 as typ1.
      inverts H2.
      --
        forwards* h1: tpre_principle H1.
        rewrite <- H9 in *.
        inverts val2; try solve[inverts H0]; simpl in *.
        inverts typ2 as typ2.
        inverts typ2 as typ2.
        inverts typ2 as typ2.
        forwards* h2: principle_inf typ2.
        rewrite h2 in *. 
        forwards*: value_lc H4.
      --
        inverts typ2 as typ2. 
        forwards* h1:Principle_inf typ2. 
        forwards* h2:Principle_inf H0. 
        rewrite h1 in *. inverts h2.
        destruct(eq_type C0).
        destruct(eq_type D0).
        subst.
        ---
          exists.
          splits.
          apply Cast_v; auto.
          rewrite TEMP; auto.
          eapply ep_anno; eauto.
        ---
          exists.
          splits.
          apply Cast_anyd; simpl;eauto.
          rewrite TEMP; auto.
          eapply ep_annor; eauto.
        ---
          exists.
          splits.
          apply Cast_anyd; simpl;eauto.
          rewrite TEMP; auto.
          eapply ep_annor; eauto.
      *
        inverts typ1 as typ1.
        inverts H2.
        inverts val2; inverts H0.
        forwards*: value_lc H4.
        exists. splits*.
     +
      inverts typ1 as typ1. inverts typ2 as typ2. 
      inverts typ2 as typ2.
      exists. splits.
      apply Cast_anyd;eauto.
      eapply ep_annor; eauto.
      eapply ep_annor; eauto.
     +
      inverts typ1 as typ1. inverts typ2 as typ2. 
      inverts typ2 as typ2.
      exists. splits.
      apply Cast_anyd;eauto.
      eapply ep_annor; eauto.
      eapply ep_annor; eauto.
Qed.



Lemma value_cast_keep0: forall v v' A l b,
 Typing nil v Chk A ->
 value (e_anno v l b A) ->
 Cast v l b A (e_exp v') ->
 v' = (e_anno v l b A).
Proof.
  introv typ val red.
  inverts* val; simpl in *.
  -
  inverts* typ; simpl in *; subst.
  inverts* red.
  inverts H4.
  inverts H4.
  -
  inverts* red; simpl in *; inverts* H1.
  rewrite <- H0 in *. inverts* H5. inverts* H1.
  inverts* H3.
  rewrite <- H0 in *. inverts* H5. 
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
    try solve[forwards*: flike_int].
  -
    forwards*: Typing_regular_1 typ2. 
    exists.
    splits*.
  -
    inverts typ2 as typ2. inverts typ2 as typ2. 
    inverts typ1 as typ1.  inverts typ1 as typ1.
    forwards* h1: IHep typ2.
    inverts* val.
    lets(v2'&red&val2&epr): h1.
    inverts val.
    +
      inverts H.
      *
      forwards*: preservation_multi_step red.
      inverts typ1 as typ1;
        try solve[forwards*: flike_int].
      inverts H; 
        try solve[forwards*: flike_int].
      forwards* h3: epre_value_arrow epr. 
      inverts h3 as h3.
      --
        lets(v21&ll&bb&eq&eq2): h3. substs.
        exists((e_anno v21 ll bb t_dyn)).
        splits*.
        eapply stars_trans.
        apply multi_rred_anno. apply red.
        apply stars_one.
        forwards*: value_lc val2. inverts H.
        apply Step_annov; eauto.
        unfold not; intros nt; inverts* nt. inverts H9.
        inverts H0.
        eapply ep_annol; eauto.
      --
        lets(t3&t4&eq): h3. 
        destruct(eq_type t3).
        destruct(eq_type t4); subst.
        ++
          exists((e_anno (v2') l2 b2 t_dyn)).
          splits*.
          apply multi_rred_anno. apply red.
          eapply value_dyn; eauto.
          rewrite eq; eauto.
        ++
          exists((e_anno (e_anno (v2') l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
          splits.
          eapply stars_trans.
          apply multi_rred_anno. apply red.
          apply stars_one.
          apply Step_annov; eauto.
          apply Cast_anyd; simpl; eauto.
          rewrite eq; eauto.
          unfold not; intros nt; inverts* nt. 
          rewrite eq in *; inverts* H9.
          apply value_dyn; eauto.
          forwards* h5: principle_inf H0.
          rewrite eq in *. subst.
          eapply ep_annor; eauto.
        ++
          exists((e_anno (e_anno (v2') l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
          splits.
          eapply stars_trans.
          apply multi_rred_anno. apply red.
          apply stars_one.
          apply Step_annov; eauto.
          apply Cast_anyd; simpl; eauto.
          rewrite eq; eauto.
          unfold not; intros nt; inverts* nt. 
          rewrite eq in *; inverts* H9.
          apply value_dyn; eauto.
          forwards* h5: principle_inf H0.
          rewrite eq in *. subst.
          eapply ep_annor; eauto.
      *
        forwards*: preservation_multi_step red.
        inverts typ1 as typ1; 
          try solve[forwards*: flike_int].
        inverts H; 
          try solve[forwards*: flike_int].
        forwards* h5: epre_value_arrow epr. inverts h5 as h6 h7.
        --
          lets(v21&ll1&bb1&eq1&eq2): h6. substs.
          inverts val2; 
            try solve[forwards*: flike_int];
            try solve[forwards*: abs_nlam].
          forwards* h8: Principle_inf typ1.
          rewrite <- H7 in *. substs.
          inverts* H0; 
            try solve[forwards*: flike_int].
          inverts* H16; 
            try solve[forwards*: flike_int].
          forwards* h9: Principle_inf H.
          rewrite eq2 in *. substs.
          forwards* h10: epre_dyn epr.
          apply value_dyn; eauto.
          rewrite eq2 in *. eauto.
          destruct(eq_type C0).
          destruct(eq_type D0); subst.
          ++
            exists.
            splits.
            eapply stars_trans.
            apply multi_rred_anno. apply red.
            apply stars_one.
            apply Step_annov; eauto.
            eapply value_dyn; eauto.
            rewrite eq2; auto.
            rewrite <- eq2.
            apply Cast_vany; eauto.
            unfold not; intros nt; inverts* nt. inverts* H17.
            auto. eauto.
          ++
            exists.
            splits.
            eapply stars_trans.
            apply multi_rred_anno. apply red.
            apply stars_one.
            apply Step_annov; eauto.
            eapply value_dyn; eauto.
            rewrite eq2; auto.
            apply  Cast_dyna; eauto.
            rewrite eq2; auto.
            unfold not; intros nt; inverts* nt; 
              try solve[forwards*: flike_int];
              try solve[inverts H18].
            eapply value_fanno; eauto.
            eauto.
          ++
            exists.
            splits.
            eapply stars_trans.
            apply multi_rred_anno. apply red.
            apply stars_one.
            apply Step_annov; eauto.
            eapply value_dyn; eauto.
            rewrite eq2; auto.
            apply  Cast_dyna; eauto.
            rewrite eq2; auto.
            unfold not; intros nt; inverts* nt; 
              try solve[forwards*: flike_int];
              try solve[inverts H18].
            eapply value_fanno; eauto.
            eauto.
        --
        lets(t3&t4&eq): h6. substs.
        exists(e_anno (v2') l2 b2 (t_arrow C0 D0)).
        splits*.
        eapply stars_trans.
        apply multi_rred_anno. apply red.
        apply step_refl. 
    +
      inverts H.
      forwards*: preservation_multi_step red.
      assert(Cast e1 l1 b1 t_dyn (e_exp (e_anno e1 l1 b1 t_dyn))); eauto.
      forwards* h5: Cast_dgg l2 b2 epr H0.
      lets(e2'&tred&epp): h5.
      forwards*: value_lc val2.
      destruct(value_decidable (e_anno v2' l2 b2 t_dyn)); eauto.
      *
      exists (e_anno v2' l2 b2 t_dyn).
      splits*.
      apply multi_rred_anno. apply red.
      *
      forwards*: Cast_value tred.
      exists e2'.
      splits*.
      eapply stars_trans.
      apply multi_rred_anno. apply red.
      apply stars_one.
      apply Step_annov; eauto.
  -
    inverts typ2 as typ2. 
    inverts typ2 as typ2.
    forwards* h1: IHep.
    lets(vv1&h2&h3&h4): h1.
    forwards* h5: preservation_multi_step typ2 h2.
    forwards* h6: cast_right l b h5 H1.
    lets(v2'& rred& epp):h6.
    exists v2'. splits*.
    eapply stars_trans.
    apply multi_rred_anno; eauto.
    forwards*: value_lc h3.
    destruct(value_decidable (e_anno vv1 l b A0)); auto.
    forwards* h7:value_cast_keep rred. inverts* h7.
    forwards*: Cast_value rred.
  -
    inverts typ1 as typ1. inverts typ1 as typ1.
    forwards* h1: IHep.
    inverts* val.
    lets(vv1&h2&h3&h4): h1.
    forwards*: preservation_multi_step H0 h2.
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



Lemma value_cast_keep: forall v r A l b,
Typing nil v Chk A ->
value (e_anno v l b A) ->
Cast v l b A r ->
r = (e_exp (e_anno v l b A)).
Proof.
 introv typ val red.
 inverts* val; simpl in *.
 -
 inverts typ as typ; simpl in *; subst.
 forwards* h1: principle_inf typ.
 rewrite <- h1 in *.
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
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2. 
    forwards*: IHep typ1 typ2.
    inverts* val.
    inverts* H0.
    lets(vv&rred&vval&epp): H3.
    +
    forwards*: preservation_multi_step rred.
    forwards*: Cast_progress l1 b1 H0.
    inverts H4. destruct x; eauto.
    *
    destruct(value_decidable (e_anno vv l1 b1 A0)); auto.
    forwards* hh1: value_cast_keep H5. inverts* hh1.
    --
    left. exists. splits.
    apply multi_rred_anno; eauto.
    auto.
    eapply ep_anno; eauto.
    --
    forwards*: Cast_dgg l1 b1 epp H.
    inverts* val.
    lets(vv1&rred1&epp1):H6.
    forwards* hh2: value_cast_keep rred1.
    inverts* hh2.
    left. exists. splits.
    eapply stars_trans.
    apply multi_rred_anno; eauto.
    apply stars_one.
    eapply Step_annov; eauto.
    forwards*: Cast_value H5.
    auto.
    *
    destruct(value_decidable (e_anno vv l1 b1 A0)); auto.
    forwards* hh3: value_cast_keep H5. inverts* hh3.
    inverts H5.
    right.
    exists.
    eapply stars_transb.
    apply multi_rred_anno; eauto.
    apply step_b; eauto.
    +
    inverts H3. inverts H0.
    forwards*: multi_bblame_anno H3.
  -
    inverts typ2 as typ2. inverts typ2 as typ2.
    forwards* h1: IHep.
    inverts* val.
    inverts* h1.
    lets(vv&rred&vval&epp): H3.
    forwards*: preservation_multi_step H rred.
  -
    inverts typ1 as typ1. inverts typ1 as typ1.
    forwards* h1: IHep.
    inverts h1.
    +
    lets(vv&rred&vval&epp): H3.
    forwards*: preservation_multi_step H rred.
    forwards*: preservation_multi_step H rred.
    destruct(value_decidable (e_anno vv l b A0)); eauto.
    left.
    exists. splits.
    apply multi_rred_anno.
    apply rred.
    auto. eauto.
    forwards h2: preservation_multi_step typ1 rred.
    forwards* h3: Cast_progress l b h2.
    inverts h3. destruct x.
    forwards*: cast_left epp H8.
    left. exists. splits.
    eapply stars_trans.
    apply multi_rred_anno.
    apply rred.
    apply stars_one.
    apply Step_annov; eauto.
    forwards*: Cast_value H8.
    auto.
    right. exists. 
    eapply stars_transb.
    apply multi_rred_anno.
    apply rred.
    apply step_b.
    apply Step_annov; eauto.
    +
    inverts H3. inverts H5.
    forwards*: multi_bblame_anno H3.
Qed.



Lemma unwrap_epre: forall v1 v2 v3 v4 t3 t4 l2 b2 tt1 tt2 c d,
 Typing nil (e_appv (e_anno (v1) l2 b2 (t_arrow t3 t4)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 value v1 ->
 value v2 ->
 value v3 ->
 value v4 ->
 epre nil nil (e_anno v1 l2 b2 (t_arrow t3 t4)) v3 ->
 epre nil nil v2 v4 ->
 principal_type v1 = (t_arrow c d) ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ (epre nil nil (e_anno (e_appv v1  (e_anno v2 l2 (negb b2) c)) l2 b2 t4) e2').
Proof.
  introv typ1 typ2 val1 wal1 val2 val3 val4 ep1 ep2 ty. 
  gen tt1 tt2 v2 v4 c d.
  inductions ep1; intros.
  -
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
    inverts val3.
    inverts H.
    forwards* h1: tpre_principle ep1.
    rewrite ty in *.
    rewrite <- H10 in *.
    inverts h1.
    exists. splits.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply ep_anno; eauto.
  -
    inverts typ1 as typ1. inverts typ1 as typ1. 
    inverts typ1 as typ1. 
    inverts typ2 as typ2. inverts typ2 as typ2. 
    inverts typ2 as typ2.
    inverts H. 
    inverts val3. 
    inverts val1. 
    forwards* hh1: tpre_principle ep1; simpl in *.
    inverts typ2 as typ2.
    forwards* hh2: principle_inf typ2.
    rewrite <- H12 in *. inverts hh2. 
    inverts H3. inverts hh1. 
    forwards* h1: cast_right ep2.
    lets (vv1&rred1&epp1): h1.
    forwards*: Cast_preservation rred1.
    forwards*: Cast_value rred1.
    forwards* h2: IHep1 v1 epp1.
    lets (vv&rred&epp): h2.
    assert(Typing nil (e_appv e2 vv1) Inf D); eauto.
    forwards*: preservation_multi_step rred.
    inverts H1.
    inverts typ1 as typ1; try solve[inverts wal1].
    forwards* h3: principle_inf typ1.
    rewrite h3 in *. subst.  inverts H19. 
    destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
    +
    forwards h6: rred1. 
    forwards* h7: value_cast_keep2 h6. inverts h7.
    inverts H15. 
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
    apply Step_eval; auto.
    apply Step_eval; auto.
    eapply Step_annov; simpl; eauto.
    unfold fill.
    apply multi_rred_anno.
    apply rred.
    eapply ep_annor; eauto.
    eapply Typ_anno;eauto.
  -
    inverts typ1 as typ1. 
    inverts typ1 as typ1.
    inverts typ1 as typ1.
    inverts typ2 as typ2. 
    inverts typ2 as typ2.
    forwards* h1 : principle_inf typ2.
    forwards* h2: principle_inf H0.
    rewrite h1 in *. inverts h2.
    inverts val1.
    forwards* h3: tpre_principle ep1; simpl in *.
    rewrite h1 in *. rewrite <- H13 in *.
    inverts h3. inverts ty.
    inverts typ1 as typ1; try solve[inverts wal1].
    forwards* h5: principle_inf typ1.
    rewrite <- H13 in *. subst.
    inverts H6.
    inverts H1.
    exists. splits.
    apply step_refl.
    eapply ep_annol; eauto.
Qed.


Lemma unwrap_eprer: forall v1 v2 v3 v4 t3 t4 tt1 tt2 l2 b2 ttt1 ttt2,
 Typing nil (e_appv (e_anno v1 l2 b2 (t_arrow t3 t4)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 value v2 ->
 value v3 ->
 value v4 ->
 epre  nil nil v3 (e_anno v1 l2 b2 (t_arrow t3 t4)) ->
 epre nil nil v4 v2 ->
 principal_type v1 = (t_arrow ttt1 ttt2) ->
 (exists e2', steps (e_appv v3 v4) (e_exp e2') /\ (epre  nil nil e2' (e_anno (e_appv v1 (e_anno v2 l2 (negb b2) ttt1)) l2 b2 t4)))
 \/ exists l b, steps (e_appv v3 v4) (e_blame l b).
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4 ttt1 ttt2.
  inductions ep1; intros.
  -
    inverts H. inverts val3. inverts val1.
    forwards*: tpre_principle ep1; simpl in *.
    rewrite <- H10 in *.
    inverts H.
    rewrite <- H8 in *.
    inverts H1.
    inverts H0.
    left. exists.
    splits.
    apply stars_one.
    eapply Step_abeta; eauto.
    apply ep_anno; eauto.
  -
    inverts H1.
    inverts typ1 as typ1. inverts typ1 as typ1. 
    inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2.
    forwards* h1: principle_inf typ2. 
    forwards* h2: principle_inf H. 
    rewrite h1 in *. inverts h2.
    inverts typ1.
    forwards* h4: principle_inf typ2.
    inverts val1.
    forwards* h5: principle_inf H0.
    forwards* h6: principle_inf H1.
    rewrite h5 in *. subst.
    inverts H2. inverts H6.
    left. exists. splits*.
    eapply ep_annor; eauto.
  -
    inverts H0 as h0. inverts H2. inverts H1.
    inverts val3. 
    inverts typ1 as typ1.  inverts typ1 as typ1.  inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
    inverts val1.
    inverts typ2; try solve[ inverts h1]. 
    forwards* h2: principle_inf H0.
    forwards* h3: principle_inf H.
    rewrite h3 in *. subst. inverts H9.
    rewrite <- H17 in *. inverts H3.
    forwards* hh1: Cast_progress v4 A0.
    inverts hh1. destruct x; eauto.
    +
      forwards* h4: cast_left ep2 H3. 
      forwards* h5: Cast_value H3.
      forwards* h6: Cast_preservation H3.
      forwards* h7: IHep1 v1 h4.
      inverts typ1; try solve[inverts wal1].
      forwards* h8: principle_inf H9.
      rewrite h8 in *. subst.
      inverts H13.
      inverts h7.
      *
      lets(vv1&rred1&epp1): H13.
      assert(Typing nil (e_appv e1 e) Inf B).
      eauto.
      forwards*: preservation_multi_step rred1.
      destruct(value_decidable (e_anno v4 l (negb b) A0)); auto.
      --
      forwards* h2: value_cast_keep2 H3.
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
      apply Step_eval; eauto.
      rewrite fill_appvr.
      eapply Step_eval;eauto.
      unfold fill.
      apply multi_rred_anno.
      apply rred1.
      eapply ep_annol; eauto.
      eapply Typ_anno;eauto.
      *
      destruct(value_decidable (e_anno v4 l (negb b) A0)); auto.
      --
      forwards* h2: value_cast_keep2 H15.
      inverts h2.
      lets(ll3&bb3&rred3):H13.
      right.
      exists.
      eapply stars_transb.
      apply stars_one.
      eapply Step_abeta; eauto.
      apply multi_bblame_anno; eauto.
      --
      lets(ll3&bb3&rred3):H13.
      right.
      exists.
      eapply stars_transb.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply stars_transb.
      apply stars_one.
      rewrite fill_anno.
      apply Step_eval; eauto.
      rewrite fill_appvr.
      eapply Step_eval;eauto.
      unfold fill.
      apply multi_bblame_anno; eauto.
    +
      inverts* H3.
      right. 
      exists.
      eapply stars_transb.
      apply stars_one.
      eapply Step_abeta; eauto.
      apply multi_bblame_anno.
      apply step_b; eauto.
      rewrite fill_appvr.
      apply Step_blame; eauto.
      eapply Step_annov; eauto.
      unfold not;intros nt;inverts* nt. inverts H19.
Qed.


Lemma add: forall i v3 v4 tt1 tt2,
 Typing nil (e_appv e_add (e_lit i)) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 epre nil nil e_add v3 ->
 epre nil nil (e_lit i) v4 ->
 value v3 ->
 value v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_addl i) e2'.
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. 
  gen i tt1 tt2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
  -
    inverts typ2 as typ2.  inverts typ2 as typ2.  inverts typ2 as typ2.
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts H. inverts typ2 as typ2; try solve[inverts ep1].
    inverts val3.
    forwards* hh1: principle_inf typ2. 
    forwards* hh2: tpre_principle ep1; simpl in *.
    rewrite <- H14 in *. subst. inverts H6. inverts hh2.
    forwards* hh2: cast_right l (negb b) ep2.
    lets (vv1&rred1&epp1): hh2.
    forwards* hh3: Cast_value rred1.
    forwards* hh4: Cast_preservation rred1. 
    forwards* hh5: IHep1 epp1.
    lets (vv2&rred2&epp2): hh5.
    forwards*: preservation_multi_step D rred2.
    inverts H1.
    destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
    --
    forwards* h1: value_cast_keep2 rred1.
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
    apply Step_eval; auto.
    apply Step_eval; auto.
    eapply Step_annov;eauto.
    unfold fill.
    apply multi_rred_anno. apply rred2.
    eapply ep_annor; eauto.
  -
    inverts typ2. inverts H1.
    forwards*: tpre_principle ep2; simpl in *.
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts H6. inverts val4;inverts H7.
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
 value v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_lit (i1+i2)) e2'.
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. 
  gen i2 tt1 tt2 v4.
  inductions ep1; intros; try solve[forwards*: abs_epre_true2 ep];
    try solve[forwards*: absr_epre_true2 ep]; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
  -
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts H. inverts typ2; try solve[inverts ep1].
    inverts val3.
    forwards* hh1: principle_inf H. 
    forwards* hh2: tpre_principle ep1; simpl in *.
    rewrite <- H15 in *. subst. inverts hh2. inverts H3.
    forwards* hh3: cast_right l (negb b) ep2.
    lets (vv1&rred1&epp1): hh3.
    forwards* hh4: Cast_value rred1.
    forwards* hh5: Cast_preservation rred1. 
    forwards* hh6: IHep1 epp1.
    lets (vv2&rred2&epp2): hh6.
    forwards* hh7: preservation_multi_step D rred2.
    inverts H1.
    destruct(value_decidable (e_anno v4 l (negb b) C));eauto.
    --
    forwards* h2:value_cast_keep2 rred1.
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
    apply Step_eval; auto.
    apply Step_eval; auto.
    eapply Step_annov;simpl; eauto.
    apply multi_rred_anno.
    unfold fill. apply rred2.
    eapply ep_annor; eauto.
  -
    inverts typ2. inverts H1.
    forwards* hh1: tpre_principle ep2; simpl in *.
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts H6. inverts val4;inverts H7.
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
 value v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_addl i).
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4. gen v4 i tt1 tt2.
  inductions ep1;intros.
  -
    inverts typ2 as typ2. inverts typ2 as typ2. 
    inverts typ2 as typ2. inverts H0.
    inverts val3.
    forwards* h1: tpre_principle ep2; simpl in *.
    inverts val4; inverts h1. inverts H8.
    forwards* h2: tpre_principle ep1; simpl in *.
    inverts h2. inverts H10.
    inverts typ2 as typ2.
    forwards* h3: principle_inf typ2.
    rewrite <- H0 in *. subst.
    inverts H9. inverts H13. inverts H14.
    forwards* h4: IHep1 ep2.
    lets(vv1&rred1&epp1):h4.
    inverts H1.
    forwards* h5: preservation_multi_step (t_arrow t_int t_int) rred1.
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno. apply Step_eval; auto.
    rewrite fill_appvr. apply Step_eval; auto.
    eapply Step_annov; eauto.
    unfold not;intros nt;inverts* nt. 
    unfold fill.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
  -
    inverts typ2. inverts H1.
    forwards* h1:tpre_principle ep2; simpl in *.
    inverts H6.
    inverts val4; inverts H7.
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
 value v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_lit (i1+i2)).
Proof.
  introv typ1 typ2 ep1 ep2 val3 val4.
  gen v4 i2 tt1 tt2.
  inductions ep1;intros.
  -
    inverts typ2 as typ2. inverts typ2 as typ2. 
    inverts typ2 as typ2. inverts H0.
    inverts val3.
    forwards* h1: tpre_principle ep2; simpl in *.
    inverts val4; inverts h1. inverts H8.
    forwards* h2: tpre_principle ep1; simpl in *.
    inverts h2. inverts H9. inverts H10.
    inverts typ2 as typ2; try solve[inverts H4].
    forwards* h3: principle_inf typ2.
    rewrite <- H0 in *. subst.
    forwards* h4: IHep1 ep2.
    lets(vv1&rred1&epp1):h4.
    inverts H1.
    forwards* h5: preservation_multi_step rred1.
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    eapply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno. apply Step_eval; auto.
    rewrite fill_appvr. apply Step_eval; auto.
    eapply Step_annov; eauto.
    unfold not;intros nt;inverts* nt. 
    unfold fill.
    apply multi_rred_anno; eauto.
    eapply ep_annol; eauto.
  -
    inverts typ2 as typ2. inverts typ2 as typ2.
    forwards* h1:tpre_principle ep2; simpl in *.
    inverts h1.
    inverts val4; inverts H3.
    exists. splits.
    eapply stars_one.
    eapply Step_addl; eauto.
    inverts* ep2. 
Qed. 


Lemma beta_epre: forall e v2 v3 v4 t1 t2 tt1 tt2 l1 b1,
 Typing nil (e_appv (e_abs t1 e l1 b1 t2) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_abs t1 e l1 b1 t2) ->
 value v2 ->
 value v3 ->
 value v4 ->
 epre nil nil (e_abs t1 e l1 b1 t2) v3 ->
 epre nil nil v2 v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil (e_anno (e ^^ v2) l1 b1 t2) e2'.
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros; 
    try solve[forwards*: flike_int];
    try solve[inverts H].
  -
    inverts typ1 as typ1. 
    inverts typ1 as typ1.
    inverts typ1 as typ1.
    inverts typ2 as typ2. 
    inverts typ2 as typ2.
    inverts typ2 as typ2.
    forwards* h1: value_lc val4.
    forwards* h2: value_lc val2.
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
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
    inverts val3.  inverts H.
    forwards* h1: principle_inf H0. rewrite h1 in *. inverts H13.
    forwards*: tpre_principle ep1; simpl in *.
    rewrite h1 in *.
    inverts H.
    inverts H1.
    inverts typ2 as typ2.
    forwards* h6: principle_inf typ2.
    rewrite h1 in *. subst.
    inverts H1.
    forwards* h2: cast_right l (negb b) ep2.
    lets (vv1&rred1&epp1): h2.
    forwards* h3: Cast_value rred1.
    forwards* h4: Cast_preservation rred1. 
    inverts H2.
    forwards* h5: IHep1 epp1.
    lets (vv2&rred2&epp2): h5.
    assert(Typing nil (e_appv e2 vv1) Inf D); eauto.
    forwards* h6: preservation_multi_step rred2.
    destruct(value_decidable (e_anno v4 l (negb b) C)); auto.
    +++
      forwards* h7: value_cast_keep2 rred1. inverts h7.
      exists. splits.
      eapply stars_trans.
      apply stars_one.
      eapply Step_abeta; eauto.
      apply multi_rred_anno. apply rred2.
      eapply ep_annor; eauto.
      apply Typ_anno; eauto.
      pick fresh y .
      forwards*: H16 y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
    +++
      exists. splits.
      eapply stars_trans.
      apply stars_one.
      eapply Step_abeta; eauto.
      rewrite fill_anno.
      rewrite fill_appvr.
      eapply stars_trans.
      apply stars_one.
      apply Step_eval; auto.
      apply Step_eval; eauto.
      unfold fill.
      apply multi_rred_anno. apply rred2.
      eapply ep_annor; eauto.
      apply Typ_anno; eauto.
      pick fresh y .
      forwards*: H16 y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
Qed.


Lemma beta_eprer: forall e v2 v3 v4 t1 t2 tt1 tt2 l1 b1,
 Typing nil (e_appv (e_abs t1 e l1 b1 t2) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_abs t1 e l1 b1 t2) ->
 value v2 ->
 value v3 ->
 value v4 ->
 epre nil nil v3 (e_abs t1 e l1 b1 t2) ->
 epre nil nil v4 v2 ->
 (exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre nil nil e2' (e_anno (e ^^ v2) l1 b1 t2)) \/
 exists l b, steps (e_appv v3 v4) (e_blame l b ).
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros;
    try solve[forwards*: flike_int];
    try solve[inverts H0].
  -
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2. 
    inverts val3.
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ1 as typ1.
    inverts H1.
    left. exists. splits.
    apply stars_one.
    eapply Step_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    assert((e ^^ v2) = [y ~> v2] (e ^^ e_var_f y)).
    rewrite (subst_exp_intro y); eauto.
    rewrite H1.
    forwards*: H y.
    forwards*: epre_open H2 ep2.
  -
    inverts H0. inverts H1. inverts H2.
    inverts typ1 as typ1. inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
    inverts typ2 as typ2. 
    inverts val3.
    forwards* h1: principle_inf typ2.
    forwards* h2: principle_inf H.
    rewrite <- H16 in *. subst. inverts H3. 
    forwards* h3: Cast_progress v4 C.
    inverts h3. destruct x.
    +
      forwards* h4: tpre_principle ep1; simpl in *.
      inverts h2. 
      rewrite <- H16 in *.
      inverts h4.
      forwards* h5: cast_left ep2 H0.
      forwards* h6: Cast_value H0.
      forwards* h7: Cast_preservation H0. 
      forwards* h8: IHep1 h5.
      inverts h8.
      *
      lets(vv1&rred1&epp1): H3.
      assert(Typing nil ( e_appv e1 e0) Inf B0).
      eauto.
      forwards* h9: preservation_multi_step H8 rred1.
      destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
      ---
      forwards* h1: value_cast_keep2 H0. inverts h1.
      left. exists. splits.
      eapply stars_trans.
      apply stars_one.
      eapply Step_abeta; eauto.
      apply multi_rred_anno; eauto.
      eapply ep_annol; eauto.
      inverts* H3; try solve[inverts H].
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      forwards*: typ1 y.
      apply Typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      ---
      left. exists. splits.
      eapply stars_trans.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_anno;eauto. apply Step_eval; auto.
      rewrite fill_appvr;eauto. 
      unfold fill.
      apply multi_rred_anno; eauto.
      eapply ep_annol; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      forwards*: typ1 y.
      apply Typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      *
      inverts H3. inverts H8.
      destruct(value_decidable (e_anno v4 l (negb b) A)); auto.
      ---
      forwards* h1: value_cast_keep2 H8. inverts h1.
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
      rewrite fill_anno;eauto. apply Step_eval; auto.
      rewrite fill_appvr;eauto. 
      unfold fill.
      apply multi_bblame_anno; eauto.
    +
      lets red': H0.
      inverts* H0.
      right. exists.
      eapply stars_transb.
      apply stars_one.
      eapply Step_abeta; eauto.
      apply step_b.
      rewrite fill_anno; eauto.
      rewrite fill_appvr.
      apply Step_blame;eauto.
      apply Step_blame;eauto.
      eapply Step_annov;eauto.
      unfold not;intros nt. inverts* nt. inverts H18.
Qed.


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
  try solve[inverts* red;destruct E; unfold fill in H2; inverts* H2];
  try solve[forwards*: step_not_value red ];
    try solve[forwards*: flike_int].
  - (* app *)
    inverts* red; 
    try solve[forwards*: flike_int].
    + destruct E; unfold fill in H; inverts* H.
      *
        inverts typ1 as typ1. inverts typ2 as typ2.
        inverts typ1 as typ1. inverts typ2 as typ2.
        forwards* h1: Typing_chk H10. inverts h1.
        forwards* h2: Typing_chk H12. inverts h2.
        forwards* h3: IHep1 H2. inverts h3.
        -- 
        inverts H5. inverts H1.
        inverts H6.
        forwards*: epre_lc2 ep2.
        left.
        exists. split. apply multi_rred_app2.
        auto.  apply H1.
        unfold fill; auto.
        -- 
        right.
        lets(ll1&bb1&rred1): H5.
        exists.
        apply multi_bblame_app2; auto.
        inverts H1.
        forwards*: epre_lc2 ep2.
        apply rred1.
      *
        inverts typ1 as typ1. inverts typ2 as typ2. 
        inverts typ1 as typ1. inverts typ2 as typ2.
        forwards* h1: Typing_chk H10. inverts h1.
        forwards* h2: Typing_chk H12. inverts h2.
        forwards* h3: epre_valr ep1. inverts* H1.
        inverts h3.
        ++
          inverts H5. inverts H6. inverts H7.
          forwards* h4: IHep2 H2. inverts h4.
          ---
            inverts H7. inverts H9.
            forwards* h5: Typing_regular_1 H11.
            inverts H1.
            forwards* h6: preservation_multi_step H10 H5.
            forwards* h7: tpre_principle H8.
            rewrite H16 in *.
            forwards* h8: principle_inf h6.
            inverts h7.
            rewrite <- H1 in *. subst.
            inverts typ1.
            left.
            exists(e_app x1 l1 b1 x2). split. 
            apply stars_trans with (b:=e_app x1 l1 b1 e2).
            apply multi_rred_app2;auto.  
            eapply multi_rred_app;auto.
            rewrite <- H1. reflexivity.
            unfold fill; eauto. 
          ---
            lets(ll1&bb1&rred1): H7.
            inverts H1.
            forwards* h5: tpre_principle H8.
            rewrite H15 in *. 
            inverts h5.
            forwards* h6: preservation_multi_step H10 H5.
            forwards* h7: tpre_principle H8.
            forwards* h8: principle_inf h6.
            rewrite <- H1 in *. subst. inverts typ1.
            forwards*: Typing_regular_1 H11.
            right. exists.
            eapply stars_transb.
            apply multi_rred_app2.
            auto. apply H5.
            eapply multi_bblame_app; auto.
            rewrite <- H1. reflexivity.
            apply rred1. 
        ++
          lets(ll1&bb1&rred1): H5.
          forwards*: Typing_regular_1 H11.
          right.
          exists.
          apply multi_bblame_app2; eauto.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards* h1: Typing_chk H11. inverts h1.
      forwards* h2: Typing_chk H14. inverts h2.
      forwards* h3: epre_valr ep1.
      inverts h3.
      *
        lets(vv1&rred1&vval1&epp1): H3.
        forwards* h4: epre_valr ep2.
        inverts h4.
        --
          lets(vv2&rred2&vval2&epp2): H8.
          forwards* h5: epre_lc2 ep2.
          forwards* h6: tpre_principle epp1.
          rewrite H6 in *. inverts h6.
          forwards* h7: preservation_multi_step H11 rred1.
          forwards* h8: preservation_multi_step H12 rred2.
          forwards* h9: principle_inf h7.
          rewrite <- H9 in *. subst. inverts typ1.
          forwards* h10: principle_inf H14.
          rewrite h10 in *. subst.
          inverts typ2.
          forwards* h4: Cast_dggr l1 b1 epp2 H7.
          inverts h4. 
          **
          lets(vv3&rred3&epp3): H6.
          left. exists.
          splits.
          eapply stars_trans.
          apply multi_rred_app2. auto.
          apply rred1.
          eapply stars_trans.
          eapply multi_rred_app. rewrite <- H9. auto.
          auto.
          apply rred2.
          apply stars_one.
          eapply Step_app; eauto.
          apply ep_appv; eauto.
          **
          right. exists. 
          eapply stars_transb.
          eapply stars_trans.
          apply multi_rred_app2. auto.
          apply rred1.
          eapply stars_trans.
          eapply multi_rred_app. rewrite <- H9.
          auto. auto.
          apply rred2.
          apply step_refl.
          apply step_b.
          eapply Step_betap; eauto.
        --
          forwards* h1: principle_inf H14.
          rewrite h1 in *. subst. inverts typ2.
          forwards* h2: tpre_principle epp1.
          rewrite h1 in *.
          inverts h2.
          forwards* h3: preservation_multi_step H11 rred1.
          forwards* h4: principle_inf h3.
          rewrite h4 in *. subst.
          forwards*: epre_lc2 ep2.
          lets(ll1&bb1&rred2): H8.
          right. exists.
          eapply stars_transb.
          apply multi_rred_app2. auto.
          apply rred1.
          eapply multi_bblame_app; eauto.
      *
        forwards*: epre_lc2 ep2.
        lets(ll1&bb1&rred1): H3.
        right. exists.
        apply multi_bblame_app2; eauto.
    +
      inverts typ1 as typ1. inverts typ1 as typ1. 
      inverts typ2 as typ2. inverts typ2 as typ2.
      inverts H12. inverts typ2.
      inverts typ1.
      --
        left. exists. splits.
        apply step_refl.
        eapply ep_app; eauto.
      --
        forwards* h1: Typing_chk H9. inverts h1.
        forwards* hh1: epre_valr ep1.
        inverts hh1.
        ++
        lets(vv1&rred1&vval1&epp1): H3.
        forwards* h2: preservation_multi_step H9 rred1.
        forwards* hh2: Typing_regular_1 H10.
        inverts vval1;inverts h2.
        left. exists. splits.
        eapply stars_trans.
        apply multi_rred_app2. auto.
        apply rred1.
        apply stars_one.
        apply Step_dyn. auto. auto.
        apply ep_app; eauto.
        ++
        forwards*: Typing_regular_1 H10.
        lets(ll1&bb11&rred1): H3.
        right. exists.
        apply multi_bblame_app2; eauto.
  - (* anno *)
    inverts typ1 as typ1. inverts typ1 as typ1. 
    inverts typ2 as typ2. inverts typ2 as typ2.
    inverts red.
    +
      destruct E; unfold fill in *; inverts* H0.
      forwards* h1: IHep H5.
      inverts h1.
      *
      lets(e2'&red&epp): H0.
      forwards*: multi_rred_anno A0 red.
      *
      lets(ll1&bb1&rred1): H0.
      right. exists. 
      apply multi_bblame_anno; eauto.
    +
      forwards*: value_lc H7.
      forwards*: epre_lc2 ep.
      forwards* h1: epre_valr ep.
      inverts h1.
      *
      lets(v2&red&vval&epp1): H4.
      forwards*: preservation_multi_step red.
      forwards* h2: Cast_dggr epp1 H H8.
      inverts h2.
      **
        lets(v2'&tred&epp2):H6.
        forwards* h3: multi_rred_anno A0 red.
        forwards* h1: Cast_value H8.
        forwards*: value_lc h1.
        forwards*: epre_lc2 epp1.
        destruct(value_decidable (e_anno v2 l1 b1 A0)); eauto.
        ***
        forwards*: Cast_preservation H8.
        forwards* h2: value_cast_keep tred. inverts* h2.
        ***
        left.
        exists v2'. splits*.
      **
        destruct(value_decidable (e_anno v2 l1 b1 A0)); eauto.
        ***
        forwards* h1: value_cast_keep H10. inverts* h1.
        ***
        lets red': H6.
        inverts* red'.
        right. exists.
        eapply stars_transb.
        forwards h2: multi_rred_anno A0 red.
        apply h2.
        apply step_b; auto.
      *
      lets(ll1&bb1&rred1): H4.
      right. exists.
      apply multi_bblame_anno; auto.
      apply rred1.
  - (* annor *)
    inverts typ2 as typ2. inverts typ2 as typ2.
    inverts red.
    +
      destruct E; unfold fill in *; inverts H3.
      forwards* h1: IHep H7.
      inverts h1.
      *
      lets(ee2'&rred&epp): H3.
      forwards* h1: preservation_multi_step H rred.
      forwards*: Typing_regular_1 h1.
      forwards*: preservation H0 H7.
      *
      right*.
    +
      forwards* h1: epre_valr ep.
      inverts* h1.
      lets(vv1& rred1 & vval1 & epp1): H3.
      forwards*: preservation_multi_step H rred1.
      forwards*: cast_right epp1.
      lets(vv2& rred2 & epp2): H6.
      forwards* h3: Cast_unique H10 rred2.
      inverts h3.
      left.
      exists. splits.
      apply rred1. auto.
  - (* annol *)
    inverts typ1 as typ1. inverts typ1 as typ1.
    forwards* h1: IHep.
    inverts* h1.
    +
      lets(vv1& rred1 & epp1): H3.
      forwards*: preservation_multi_step H rred1.
      left. exists. splits.
      apply multi_rred_anno.
      apply rred1.
      forwards*: preservation H0 red.
    +
      lets(ll1&bb1&rred1): H3.
      right. exists.
      apply multi_bblame_anno; auto.
      apply rred1.
  - (* appv *)
    inverts red; 
    try solve[destruct E; unfold fill in H; inverts* H];
    try solve[forwards*: flike_int].
    +
      destruct E; unfold fill in H; inverts* H.
      *
      inverts typ1 as typ1. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ2 as typ2.
      forwards* h1: Typing_chk typ1. inverts h1.
      forwards* h2: Typing_chk typ2. inverts h2.
      forwards* h3: IHep1 H2. inverts h3. 
      inverts H5. 
      --
      inverts H1.
      inverts H6.
      forwards*: epre_lc2 ep2.
      left.
      exists. split. apply multi_rred_appv2.
       auto.  apply H1.
      unfold fill; auto.
      -- 
      right.
      lets(ll1&bb1&rred1): H5.
      exists.
      apply multi_bblame_appv2; auto.
      inverts H1.
      forwards*: epre_lc2 ep2.
      apply rred1.
      *
      inverts typ1 as typ1. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ2 as typ2.
      forwards* h1: Typing_chk typ1. inverts h1.
      forwards* h2: Typing_chk typ2. inverts h2.
      forwards* h3: epre_valr ep1. inverts* H1.
      forwards*: Typing_regular_1 H7.
      inverts h3.
      ++
      lets(vv1& rred1 & vval1 & epp1): H6.
      forwards* h5: IHep2 H2. inverts h5.
      ---
      lets(vv2&rred2&epp2): H9.
      left. exists. splits.
      eapply stars_trans.
      apply multi_rred_appv2. auto.
      apply rred1.
      apply multi_rred_appv. auto.
      apply rred2.
      unfold fill;eauto.
      ---
      lets(ll3&bb3&rred3): H9.
      right. exists. 
      eapply stars_transb.
      apply multi_rred_appv2. auto.
      apply rred1.
      apply multi_bblame_appv. auto.
      apply rred3.
      ++
      lets(ll1&bb11&rred1): H6.
      right. exists.
      apply multi_bblame_appv2; eauto.
    +
      lets typ1': typ1.
      lets typ2': typ2.
      inverts typ1 as typ1. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ2 as typ2.
      forwards* hh1: Typing_chk typ1. inverts hh1.
      forwards* hh2: Typing_chk H7. inverts hh2.
      forwards* h1: epre_valr ep1.
      inverts h1.
      *
      lets(vv1&rred1&vval1&epp1): H5.
      forwards* h2: epre_valr ep2.
      inverts h2.
      --
        lets(vv2&rred2&vval2&epp2): H6.
        forwards* hh3: epre_lc2 ep2.
        forwards* hh4: preservation_multi_step typ1 rred1.
        forwards* hh5: preservation_multi_step H7 rred2.
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
        ++
        lets(vv3&rred3&epp3):H10.
        left.
        exists. splits.
        eapply stars_trans.
        apply H9.
        apply rred3.
        auto.
        ++
        lets(ll3&bb3&rred3):H10.
        right. exists.
        eapply stars_transb.
        apply H9.
        apply rred3.
      --
        lets(ll3&bb3&rred3):H6.
        forwards*: epre_lc2 ep2.
        right. exists.
        eapply stars_transb.
        apply multi_rred_appv2; eauto.
        apply multi_bblame_appv;eauto.
      *
        lets(ll3&bb3&rred3):H5.
        forwards*: epre_lc2 ep2.
        right. exists.
        apply multi_bblame_appv2;eauto.
    +
      lets typ1': typ1.
      lets typ2': typ2.
      inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ1 as typ1.
      forwards* hh1: Typing_chk typ1. inverts hh1.
      forwards* hh2: Typing_chk H8. inverts hh2.
      forwards* h1: epre_valr ep1.
      inverts h1.
      *
        lets(vv1&rred1&vval1&epp1): H7.
        forwards* h2: epre_valr ep2.
        inverts h2.
        --
        lets(vv2&rred2&vval2&epp2): H9.
        forwards* hh3: epre_lc2 ep2.
        forwards* hh4: preservation_multi_step typ1 rred1.
        forwards* hh5: preservation_multi_step H10 rred2.
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
        ++
          lets(vv3&rred3&epp3):H12.
          left.
          exists. splits.
          eapply stars_trans.
          apply H11.
          apply rred3.
          auto.
        ++
          lets(ll3&bb3&rred3):H12.
          right. exists.
          eapply stars_transb.
          apply H11.
          apply rred3.
        --
        lets(ll3&bb3&rred3):H9.
        forwards*: epre_lc2 ep2.
        right. exists.
        eapply stars_transb.
        apply multi_rred_appv2; eauto.
        apply multi_bblame_appv;eauto.
      *
        lets(ll3&bb3&rred3):H7.
        forwards*: epre_lc2 ep2.
        right. exists.
        apply multi_bblame_appv2;eauto.
    +
      lets typ1': typ1.
      lets typ2': typ2.
      inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ1 as typ1.
      forwards* hh1: Typing_chk typ1. inverts hh1.
      forwards* hh2: Typing_chk H6. inverts hh2.
      forwards* h1: epre_valr ep1.
      inverts h1.
      *
        lets(vv1&rred1&vval1&epp1): H3.
        forwards* h2: epre_valr ep2.
        inverts h2.
        --
        lets(vv2&rred2&vval2&epp2): H5.
        forwards*: epre_lc2 ep2.
        forwards* hh3: preservation_multi_step typ1 rred1.
        forwards* hh5: preservation_multi_step H6 rred2.
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
        lets(ll3&bb3&rred3):H5.
        forwards*: epre_lc2 ep2.
        right. exists.
        eapply stars_transb.
        apply multi_rred_appv2; eauto.
        apply multi_bblame_appv;eauto.
      *
        lets(ll3&bb3&rred3):H3.
        forwards*: epre_lc2 ep2.
        right. exists.
        apply multi_bblame_appv2;eauto.
    +
      lets typ1': typ1.
      lets typ2': typ2.
      inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ1 as typ1. 
      forwards* hh1: Typing_chk typ1. inverts hh1.
      forwards* hh2: Typing_chk H6. inverts hh2.
      forwards* h1: epre_valr ep1.
      inverts h1.
      *
      lets(vv1&rred1&vval1&epp1): H3.
      forwards* h2: epre_valr ep2.
      inverts h2.
      --
      lets(vv2&rred2&vval2&epp2): H5.
      forwards*: epre_lc2 ep2.
      forwards* hh3: preservation_multi_step typ1 rred1.
      forwards* hh5: preservation_multi_step H6 rred2.
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
      lets(ll3&bb3&rred3):H5.
      forwards*: epre_lc2 ep2.
      right. exists.
      eapply stars_transb.
      apply multi_rred_appv2; eauto.
      apply multi_bblame_appv;eauto.
      *
      lets(ll3&bb3&rred3):H3.
      forwards*: epre_lc2 ep2.
      right. exists.
      apply multi_bblame_appv2;eauto.
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
  try solve[inverts* red;destruct E; unfold fill in H2; inverts* H2];
  try solve[forwards*: step_not_value red ];
    try solve[forwards*: flike_int].
  - (* app *)
    inverts* red; 
    try solve[forwards*: flike_int].
    + 
      destruct E; unfold fill in *; inverts* H.
      *
        inverts typ1 as typ1. inverts typ2 as typ2.
        inverts typ1 as typ1. inverts typ2 as typ2.
        forwards* h1: Typing_chk H10. inverts h1.
        forwards* h2: Typing_chk H12. inverts h2.
        forwards* hh1: IHep1 H2. inverts hh1 as hh1. inverts hh1 as hh2 hh3.
        exists. split. inverts H1. apply multi_rred_app2.
        forwards*: epre_lc ep2. apply hh2.
        inverts H1.
        unfold fill. eauto.
      *
        inverts typ1 as typ1. inverts typ2 as typ2.
        inverts typ1 as typ1. inverts typ2 as typ2.
        forwards* h1: IHep2 H11. inverts h1 as h1. inverts h1 as hh1 hh2.
        inverts H1. 
        forwards* h2: Typing_chk H10. inverts h2.
        forwards* h3: Typing_chk H12. inverts h3.
        forwards* hh3: epre_val ep1. 
        inverts hh3 as hh3. inverts hh3 as hh4 hh5. inverts hh5 as hh6 hh7.
        forwards*: Typing_regular_1 H11.
        forwards*: epre_lc ep2.
        forwards*: preservation_multi_step H12 hh4.
        forwards* hh8: principle_inf H8.
        inverts typ2.
        --
          exists(e_app x2 l2 b2 x). split. 
          apply stars_trans with (b:=e_app x2 l2 b2 e2').
          apply multi_rred_app2;auto.
          eapply multi_rred_app;auto.
          rewrite TEMP. auto.
          unfold fill; eauto. 
        --
          inverts hh6;simpl in *; inverts TEMP.
          inverts H9; simpl in *.
          +++
            inverts H14; inverts* H16.
            forwards*: epre_lit_false hh7.
          +++
            forwards*: remove_left_dyn hh7.
            eapply value_dyn; eauto.
            rewrite <- H16 in *. eauto.
            exists. splits.
            eapply stars_trans.
            apply multi_rred_app2. auto.
            apply hh4.
            eapply stars_trans.
            apply stars_one.
            eapply Step_dyn; eauto.
            eapply value_dyn; eauto.
            rewrite <- H16 in *. eauto.
            eapply stars_trans.
            apply stars_one.
            rewrite fill_app; eauto.
            apply Step_eval; eauto.
            eapply Step_annov; eauto.
            eapply value_dyn; eauto.
            rewrite <- H16 in *. eauto.
            rewrite H16.
            eapply Cast_vany; eauto.
            unfold not;intros nt; inverts* nt. inverts H22.
            simpl in *.
            eapply multi_rred_app; simpl. 
            rewrite <- H16 in *. eauto.
            auto.
            apply hh1.
            eapply ep_app; eauto.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards* h1: Typing_chk H11. inverts h1.
      forwards* h2: Typing_chk H14. inverts h2.
      forwards* hh1: epre_val ep1.
      lets(vv1&red1&val1&epp1):hh1.
      forwards* hh2: epre_val ep2.
      lets(vv2&red2&val2&epp2):hh2.
      forwards* hh3: principle_inf H11.
      forwards* hh4: tpre_principle epp1; simpl in *.
      rewrite hh3 in *. subst*.
      inverts typ1.
      forwards* hh5: preservation_multi_step H14 red1.
      forwards* hh6: preservation_multi_step H15 red2.
      inverts hh4;  simpl in *; 
      try solve[forwards*: flike_int];
      try solve[inverts val1].
      *
        inverts val1; inverts H8. inverts hh5. inverts typ2.
        inverts H3.
        --
          inverts H6; inverts H9.
          forwards*: epre_lit_false epp1.
        --
          forwards* hh7: remove_left_dyn epp1.
          eapply value_dyn; eauto.
          rewrite <- H9. auto.
          forwards* hh8: value_lc H4.
          forwards* hh9: epre_lc ep2.
          forwards* hh10: multi_rred_app2 l2 b2 hh9 red1.
          forwards* hh11: multi_rred_app v l2 b2 red2.
          forwards* hh12: value_lc val2.
          forwards* hh13: Cast_dgg l2 b2 epp2 H7.
          lets(vv3&ttred&epp3):hh13.
          exists. splits.
          eapply stars_trans.
          apply hh10.
          eapply stars_trans.
          apply stars_one.
          apply Step_dyn.
          eapply value_dyn; simpl.
          rewrite <- H9. auto.
          auto. auto.
          eapply stars_trans.
          apply stars_one.
          rewrite fill_app.
          apply Step_eval.
          auto.
          apply Step_annov.
          eapply value_dyn; simpl.
          rewrite <- H9. auto.
          auto.
          rewrite H9.
          apply Cast_vany.
          unfold not; intros nt; inverts* nt. inverts H19.
          unfold fill.
          eapply stars_trans.
          apply hh11.
          apply stars_one.
          eapply Step_app; simpl; auto.
          rewrite H9. auto.
          apply ttred.
          apply ep_appv.
          auto. auto.
      *
        forwards* hh10: Cast_dgg l2 b2 epp2 H9 H7.
        lets(vv3&ttred&epp3):hh10.
        forwards* hh7: epre_lc ep2.
        forwards* hh8: multi_rred_app2 e2' hh7 red1.
        forwards* hh9: multi_rred_app vv1 red2.
        exists. splits.
        eapply stars_trans.
        apply hh8.
        eapply stars_trans.
        apply hh9.
        apply stars_one.
        eapply Step_app; simpl;eauto.
        apply ep_appv; eauto.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards* h1: Typing_chk H9. inverts h1.
      forwards* h2: Typing_chk H12. inverts h2.
      forwards* hh1: epre_val ep1.
      lets(vv1&red1&val1&epp1):hh1.
      forwards* hh2: tpre_principle epp1; simpl in *.
      inverts val1; simpl in *; inverts hh2.
      forwards* hh3: epre_lc ep2.
      forwards*: multi_rred_app2 l2 b2 hh3 red1.
      exists. splits.
      eapply stars_trans.
      apply H7.
      apply stars_one.
      apply Step_dyn; eauto.
      apply ep_app; eauto.
  - (* anno *)
    inverts typ1 as typ1.  inverts typ1 as typ1. 
    inverts typ2 as typ2. inverts typ2 as typ2.
    inverts red.
    +
      destruct E; unfold fill in *; inverts* H0.
      forwards* h1: IHep H5.
      lets(e2'&red&epp): h1.
      forwards*: multi_rred_anno A red.
    +
      forwards*: value_lc H7.
      forwards*: epre_lc ep.
      forwards* h1: epre_val ep.
      lets(v2&red&vval&epp1): h1.
      forwards* hh1: preservation_multi_step red.
      forwards* h2: Cast_dgg epp1 H hh1.
      lets(v2'&tred&epp2):h2.
      forwards* hh2: multi_rred_anno A red.
      forwards* hh3: Cast_value H8.
      forwards* hh4: value_lc hh3.
      forwards* hh5: epre_lc epp1.
      destruct(value_decidable (e_anno v2 l2 b2 A)); eauto.
      *
      forwards*: Cast_preservation H8.
      forwards*: value_cast_keep tred. inverts* H6.
      *
      exists v2'. splits*.
  - (* annor *)
    inverts typ2 as typ2.  inverts typ2 as typ2.
    forwards* hh1: IHep red.
    lets(ee2'&rred&epp): hh1.
    forwards* hh2: preservation_multi_step H0 rred.
    forwards* hh3: Typing_regular_1 hh2.
    forwards* hh4: preservation H red.
    exists(e_anno ee2' l b A0).
    splits*.
    apply multi_rred_anno; auto.
  - (* annol *)
    inverts typ1 as typ1. inverts typ1 as typ1. 
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H3.
    forwards* h1: IHep H7.
    lets(e2'&red&epp): h1.
    forwards* hh1: preservation_multi_step H0 red.
    forwards* hh2: preservation H H7.
    +
    forwards* h1: epre_val ep.
    lets(v2&red&vval&epp): h1.
    forwards* hh1: preservation_multi_step H0 red.
    forwards*: cast_left epp H1.
  - (* appv *)
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2.
    inverts red;  
    try solve[forwards*: flike_int].
    +
      destruct E; unfold fill in H; inverts* H.
      *
      forwards* h1: Typing_chk typ1. inverts h1.
      forwards* h2: Typing_chk typ2. inverts h2.
      forwards* hh1: IHep1 H5. inverts hh1 as hh1. 
      inverts hh1 as hh2 hh3. inverts H3.
      forwards*: epre_lc ep2.
      exists. split. apply multi_rred_appv2.
       auto.  apply hh2.
      unfold fill; auto. 
      *
      forwards* hh1: Typing_chk typ1. inverts hh1.
      forwards* hh2: Typing_chk typ2. inverts hh2. inverts H3.
      forwards* hh3: epre_val ep1.
      lets(vv1&red1&val1&epp1):hh3.
      forwards* hh5: Typing_regular_1 H6.
      forwards* h1: IHep2 H5.
      lets(vv3&rred3&epp3): h1.
      exists. split. 
      eapply stars_trans. 
      apply multi_rred_appv2.
      auto. apply red1.
      apply multi_rred_appv.
       auto.  apply rred3.
      unfold fill; auto. 
    +
      forwards* hh1: Typing_chk typ2. inverts hh1.
      forwards* h1: epre_val ep1.
      lets(vv1&rred1&vval1&epp1): h1.
      forwards* h2: epre_val ep2.
      lets(vv2&rred2&vval2&epp2): h2.
      inverts typ1 as typ1.
      forwards* hh2: preservation_multi_step typ2 rred1.
      forwards* hh3: preservation_multi_step H6 rred2.
      forwards* h3:  beta_epre epp1 epp2.
      lets(vv4&rred4&epp4): h3.
      forwards* hh5: Typing_regular_1 H6.
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
      forwards* hh1: Typing_chk typ2. inverts hh1.
      forwards* h1: epre_val ep1.
      lets(vv1&rred1&vval1&epp1): h1.
      forwards* h2: epre_val ep2.
      lets(vv2&rred2&vval2&epp2): h2.
      inverts typ1 as typ1.
      forwards* hh1: preservation_multi_step typ2 rred1.
      forwards* hh2: preservation_multi_step H6 rred2.
      forwards* h3: unwrap_epre epp1 epp2.
      lets(vv4&rred4&epp4): h3.
      forwards*: Typing_regular_1 H6.
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
      forwards* hh1: Typing_chk typ2. inverts hh1.
      forwards* h1: epre_val ep1.
      lets(vv1&rred1&vval1&epp1): h1.
      forwards* h2: epre_val ep2.
      lets(vv2&rred2&vval2&epp2): h2.
      inverts typ1 as typ1.
      forwards* hh2: preservation_multi_step typ2 rred1.
      forwards* hh3: preservation_multi_step H6 rred2.
      forwards* h3: add epp1 epp2.
      lets(vv4&rred4&epp4): h3.
      forwards*: Typing_regular_1 H6.
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
      forwards* hh1: Typing_chk typ2. inverts hh1.
      forwards* h1: epre_val ep1.
      lets(vv1&rred1&vval1&epp1): h1.
      forwards* h2: epre_val ep2.
      lets(vv2&rred2&vval2&epp2): h2.
      inverts typ1 as typ1.
      forwards* hh2: preservation_multi_step typ2 rred1.
      forwards* hh3: preservation_multi_step H6 rred2.
      forwards* h3: addl epp1 epp2.
      lets(vv4&rred4&epp4): h3.
      forwards*: Typing_regular_1 H6.
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




Lemma Cast_dgg_blame: forall e1 e2 A B B1 l1 b1 l2 b2,
 epre nil nil e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B1 -> 
 Cast e2 l1 b1 B (e_blame l1 b1) ->
 Cast e1 l2 b2 A (e_blame l2 b2).
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
      forwards* hh1: tpre_principle ep.
      inverts* val1.
      forwards*: epre_sim H0 hh1 tp.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts val2. 
      forwards* hh1: tpre_principle ep.
      inverts* val1.
      inverts H6; simpl in * ; inverts H4.
      *
        inverts val1.
        --
          inverts H4; simpl in *;inverts H8; inverts* hh1.
        --
          apply Cast_blame; eauto.
      *
        inverts val1.
        --
        rewrite <- H9 in *. 
        inverts* H2.
        ++
        inverts tp;
        exfalso; apply H7; auto.
        ++
        exfalso; apply H0; auto.
        --
        inverts hh1 as hh1 hh2 hh3.
        rewrite <- hh3 in *. inverts H5.
        apply Cast_blame; eauto.
        rewrite <- hh3. auto.
      *
        inverts hh1.
        inverts typ2 as typ2. inverts typ2 as typ2. inverts typ2 as typ2.
        inverts typ1 as typ1; simpl in *.
        forwards* hh2: principle_inf typ1.
        inverts* val1.
        rewrite hh2 in *. subst*.
        destruct A0; try solve[exfalso; apply H0; auto].
        --
        inverts H2; try solve[inverts* H11].
        apply Cast_blame; eauto.
        unfold not;intros nt.
        rewrite hh2 in *. inverts nt.
        --
        inverts tp; try solve[exfalso; apply H7; eauto]. 
  -
    inverts red.
    inverts val2.
    forwards* hh1: principle_inf H0.
    forwards* hh2: tpre_principle ep.
    inverts H5.
    +
    rewrite <- H4 in *.
    inverts hh1.
    destruct B; try solve[exfalso; apply H10; auto].
    inverts tp.
    inverts val1; simpl in *; inverts hh2.
    inverts typ1. inverts H3. inverts H5.
    +
    rewrite <- H4 in *.
    destruct B; try solve[exfalso; apply H10; auto].
    inverts hh2.
    inverts tp.
    inverts typ1.
    inverts val1; simpl in *; inverts* H3; inverts* H5;inverts* H6.
  -
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts red. 
    destruct(sim_decidable (principal_type e1) A0).
    +
    inverts typ1 as typ1.
    forwards* hh1: principle_inf typ1.
    inverts* val1.
    rewrite hh1 in *.
    forwards* hh2: IHep tp l b l2 b2.
    inverts* val1.
    inverts hh2. 
    inverts* val1. inverts* H13.
    inverts* H10.
    + 
    inverts typ1 as typ1.
    inverts val2.
    assert(A1 = t_dyn).
    inverts* val1.
    forwards* hh1: principle_inf typ1.
    rewrite hh1 in *. subst*.
    inverts H11; simpl in *; inverts H9.
    forwards*: epre_lit_false ep.
    destruct B; try solve[exfalso; apply H3; eauto].
    inverts* H4; inverts tp.
    destruct B; try solve[exfalso; apply H3; eauto].
    inverts* H4; inverts tp.
    subst*.
Qed. 



Lemma dynamic_guarantee_blame_chk: forall e1 e2 T1 T2 l1 b1,
 epre nil nil e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 ->
 step e2 (e_blame l1 b1) ->
 exists l2 b2, steps e1 (e_blame l2 b2).
Proof.
  introv ep typ1 typ2 red. gen T1 T2 l1 b1.
  inductions ep;intros; try solve[inverts* red].
  -
    inverts red; destruct E; unfold fill in *; inverts* H2.
  -
    inverts red.
    +
    destruct E; unfold fill in *; inverts H.
    *
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards* h1: Typing_chk H9. inverts h1.
      forwards* h2: Typing_chk H12. inverts h2.
      forwards* h3: IHep1 H3.
      lets(ll1&bb1&rred1): h3. 
      forwards*: Typing_regular_1 H10.
      exists.
      apply multi_bblame_app2; eauto.
    *
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      inverts H2.
      forwards* h1: Typing_chk H9.  forwards* h2: Typing_chk H12.
      inverts h1. inverts h2.   
      forwards* hh1: epre_valr ep1.
      forwards* hh2: Typing_regular_1 H10.
      inverts hh1.
      --
        forwards h3: principle_inf H12. auto.
        rewrite h3 in *. subst. inverts typ2.
        lets(vv1&rred1&vval1&epp1): H4.
        forwards* hh1: tpre_principle epp1.
        rewrite h3 in *.
        forwards* hh3: preservation_multi_step H9 rred1.
        forwards* h4: principle_inf hh3.
        inverts hh1.
        rewrite <- H5 in *. subst*. inverts typ1.
        forwards* h5: IHep2 H3.
        lets(ll2&bb2&rred2): h5.
        exists. 
        eapply stars_transb.
        apply multi_rred_app2.
        auto. apply rred1.
        eapply multi_bblame_app; eauto.
      --
        lets(ll1&bb1&rred1): H4.
        exists. 
        apply multi_bblame_app2; eauto.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2.
      forwards* h1: Typing_chk H11.  forwards* h2: Typing_chk H14.
      inverts h1. inverts h2.
      forwards* hh1: epre_valr ep1.
      inverts hh1.
      *
        lets(vv1&rred1&vval1&epp1): H3.
        forwards* hh2: preservation_multi_step H11 rred1.
        forwards* hh3: tpre_principle epp1.
        rewrite H7 in *. inverts hh3.
        forwards* h1: preservation_multi_step H11 rred1.
        forwards* h2: principle_inf h1.
        rewrite h2 in *. inverts H5. inverts typ1.
        forwards* hh5: principle_inf H14.
        forwards* h3: epre_valr ep2.
        inverts h3.
        --
          lets(vv2&rred2&vval2&epp2): H5.
          forwards*: preservation_multi_step H12 rred2.
          forwards*: Cast_dgg_blame A1 l1 b1 epp2 H8.
          forwards*: Typing_regular_1 H12.
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
        --
          lets(ll3&bb3&rred3): H5.
          exists.
          eapply stars_transb.
          apply multi_rred_app2.
          forwards*: Typing_regular_1 H12.
          apply rred1.
          eapply multi_bblame_app; eauto.
      *
      lets(ll3&bb3&rred3): H3.
      exists.
      apply multi_bblame_app2; eauto.
      forwards*: Typing_regular_1 H12.
  - (* anno *)
    inverts red.
    +
      destruct E; unfold fill in *; inverts H0.
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2. 
      forwards* hh1: IHep.
      lets(ll3&bb3&rred3): hh1.
      exists.
      apply multi_bblame_anno; auto.
      apply rred3.
    +
      inverts typ1 as typ1. inverts typ1 as typ1.
      inverts typ2 as typ2. inverts typ2 as typ2. 
      forwards* hh1: epre_valr ep.
      inverts hh1.
      *
      lets(vv1&rred1&vval1&epp1): H0.
      forwards* hh2: preservation_multi_step typ1 rred1.
      lets red1: H6. inverts red1.
      forwards* hh3: Cast_dgg_blame A0 epp1 H6.
      exists.
      eapply stars_transb.
      apply multi_rred_anno.
      apply rred1.
      forwards*: epre_lc2 epp1.
      destruct(value_decidable (e_anno vv1 l1 b1 A0)); auto.
      forwards* hh5: value_cast_keep H4.
      inverts hh5.
      apply step_b.
      eapply Step_annov; eauto.
      *
      lets(ll3&bb3&rred3): H0.
      exists.
      apply multi_bblame_anno; auto.
      apply rred3.
  - (* annor *)
    inverts red.
    +
      inverts typ2 as typ2. 
      inverts typ2 as typ2.
      destruct E; unfold fill in *; inverts* H3.
    +
      lets H9': H9.
      inverts H9. inverts H0.
      inductions ep; clear IHep.
      *
        inverts H.
        inverts H8.
        inverts H13.
        lets ep': ep.
        forwards*: epre_lc2 ep'.
        inverts* H12; simpl in *.
        forwards* hh1: precise_type H H7.
        forwards* hh2: epre_sim H3 hh1 H1.
        forwards* hh3: principle_inf H7.
        rewrite hh3 in *.
        apply BA_AB in hh2.
        exfalso; apply H11; eauto.
      * 
        forwards* hh1: precise_type H3 H0.
        inverts H8.
        forwards* hh2: principle_inf H0.
        rewrite hh2 in *.
        forwards* hh3:inference_unique H3 H.
        subst*.
        assert(sim B1 B1 ).
        apply sim_refl.
        forwards* hh5: epre_sim H6 H2 H4.
      *
        inverts H.
        forwards* hh1: epre_valr ep.
        inverts hh1.
        --
        lets(vv1&rred1&vval1&epp1): H.
        forwards* hh2: preservation_multi_step H16 rred1.
        forwards* hh3: Cast_dgg_blame B1 epp1  H9'.
        exists.
        eapply stars_transb.
        apply multi_rred_anno.
        apply rred1.
        forwards*: epre_lc2 epp1.
        destruct(value_decidable (e_anno vv1 l b B1)); auto.
        forwards* hh5: value_cast_keep H7.
        inverts hh5.
        apply step_b.
        apply Step_annov; eauto.
        --
        lets(ll3&bb3&rred3): H.
        exists.
        apply multi_bblame_anno; auto.
        apply rred3.
  - (* annol *)
    inverts typ1 as typ1. inverts typ1 as typ1.
    forwards* hh1: IHep typ1.
    lets(ll3&bb3&rred3): hh1.
    exists.
    apply multi_bblame_anno; auto.
    apply rred3.
  - (* appv *)
    inverts typ1 as typ1. inverts typ1 as typ1.
    inverts typ2 as typ2. inverts typ2 as typ2.
    inverts* red.
    destruct E; unfold fill in *; inverts* H.
    +
      inverts H5.
      forwards* h1: Typing_chk typ1.
      forwards* h2: Typing_chk typ2.
      inverts h1. inverts h2.
      forwards* h3: Typing_regular_1 H4.
      forwards* h4: IHep1 H7.
      lets(ll3&bb3&rred3): h4.
      exists.
      eapply multi_bblame_appv2; eauto.
    +
      inverts H5.
      forwards* h1: Typing_chk typ1.
      forwards* h2: Typing_chk typ2.
      inverts h1. inverts h2.
      forwards* h4: IHep2 H7.
      lets(ll3&bb3&rred3): h4.
      forwards* h5: Typing_chk H4.
      forwards* h6: Typing_chk H6.
      inverts h5. inverts h6.
      forwards* hh1: epre_valr ep1.
      inverts hh1 as hh2 hh3.
      *
      lets(vv1&rred1&vval1&epp1): hh2.
      forwards* hh5: preservation_multi_step typ1 rred1.
      forwards* h3: Typing_regular_1 H4.
      exists.
      eapply stars_transb.
      eapply multi_rred_appv2.
      auto. apply rred1.
      eapply multi_bblame_appv; 
      eauto.
      *
      forwards* h3: Typing_regular_1 H4.
      lets(ll4&bb4&rred4): hh2.
      exists. eapply multi_bblame_appv2; eauto.
Qed.



Lemma dynamic_guarantee_blame: forall dir e1 e2 T1 T2 l1 b1 ,
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
  forwards*: dynamic_guarantee_blame_chk red.
  -
  forwards*: dynamic_guarantee_blame_chk red.
Qed.


Lemma dynamic_guarantees_blame: forall dir e1 e2 T1 T2 l1 b1 ,
 epre nil nil e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 steps e2 (e_blame l1 b1) ->
 exists l2 b2, steps e1 (e_blame l2 b2).
Proof.
  introv ep typ1 typ2 red. gen e1 T1 T2.
  inductions red; intros.
  -
    forwards* h1: dynamic_guarantee_less ep H.
    inverts* h1.
    lets(ee1&h2&h3):H0.
    forwards* h4: preservation H.
    forwards* h5: preservation_multi_step h2.
    forwards* h6: IHred h3.
    lets(ll1&bb1&h7):h6.
    exists. eapply stars_transb; eauto.
  -
    forwards* h1: dynamic_guarantee_blame ep H.
Qed.



Lemma diverge_case: forall dir e1 e2 T1 T2,
  epre nil nil e1 e2 ->  
  Typing nil e1 dir T1 ->
  Typing nil e2 dir T2 ->
  diverge e1 ->
  diverge e2.
Proof.
  introv ep typ1 typ2 red.
  unfold diverge in *.
  unfold not in *;intros.
  apply red.
  inverts H.
  -
  lets(vv1&h1&h2):H0.
  forwards* h3:  dynamic_guarantees_less ep h1.
  inverts* h3.
  inverts* H.
  -
  lets(ll1&bb1&h1):H0.
  forwards* h2:  dynamic_guarantees_blame ep h1.
Qed.

