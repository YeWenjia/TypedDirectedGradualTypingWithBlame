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


Lemma add_epre_true: forall e2,
 epre e_add e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.

Lemma adda_epre_true: forall e2 A,
 epre (e_anno e_add A) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto; try solve[forwards*: add_epre_true ep].
Qed.


Lemma addr_epre_true: forall e1,
 epre e1 e_add  ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addi_epre_true: forall i5 e2,
 epre (e_addl i5) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addir_epre_true: forall i5 e2,
 epre e2  (e_addl i5) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addia_epre_true: forall i5 e2 A,
 epre (e_anno (e_addl i5) A) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto;try solve[forwards*: addi_epre_true ep].
Qed.


Lemma abs_epre_true: forall e1 e2,
 epre (e_abs e1) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma absr_epre_true: forall e1 e2,
 epre e1 (e_abs e2) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma absra_epre_true: forall e1 e2,
 epre e1 (e_anno (e_abs e2) t_dyn) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto;try solve[forwards*: absr_epre_true ep].
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
    unfold not; intros nt; inverts* nt. inverts H0.
Qed.



Inductive cpre : ctx -> ctx -> Prop :=
  | cp_nil: 
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre (cons ( x , A1 )  E) (cons ( x , A2 )  F) 
.

Hint Constructors cpre : core.




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
epre e e' ->
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
   forwards*: IHep1 H3 H6.
   forwards*: dmatch_tpre2 H1 H2.
    inverts* H0.
 -
   inverts* Typ2.
   inverts* H5.
   forwards*:
   absr_epre_true .
  +
    forwards*: Typing_strenthening H Typ1.
    substs*.
- inverts* Typ1. 
  inverts* H5.
  +
  forwards*: Typing_strenthening H0 Typ2.
  substs*.
  +
  forwards*: Typing_strenthening H0 Typ2.
  substs*.
  +
  forwards*: Typing_strenthening H0 Typ2.
  substs*.
Qed.



Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 epre e1 e2 ->
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
    inverts* typ. inverts H2. 
    inverts* H7.
    *
    forwards*: epre_sim H3 H1 tp.
    eapply Typ_sim with (A:= (t_arrow A2 B2));auto.
    apply Typ_anno; eauto.
    pick fresh x and apply Typ_abs;eauto.
    inverts H1.
    assert(cpre ((x, A1) :: E1) ((x, A2) :: E2));eauto.
    unfold not; intros nt; inverts* nt. inverts H5.
    *
    exfalso; apply H6; eauto.
  + 
    inverts typ. inverts H.
    forwards*: Typing_chk H6. inverts H.
    forwards*: IHep1.
    inverts H.
    forwards*:
    absr_epre_true . 
    forwards*: precise_type ep1 H6 H3.
    forwards*: dmatch_tpre H H4.
    inverts H9. inverts H10. inverts H11; try solve[inverts H9].
    forwards*: IHep2 H7 H13.
    forwards*: epre_sim H0 H15 tp.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts* nt. inverts H12.
  + 
    inverts typ. inverts H0.
    forwards*: IHep H.
    forwards*: epre_sim H1 H tp.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts* nt. inverts H4.
  +
    forwards*: IHep typ  tp.
    inverts typ.
    forwards*:abs_epre_true ep. 
    forwards*:abs_epre_true ep. 
    forwards*: Typing_strenthening H H4.
    subst.
    forwards*: epre_sim H5 H1 tp.
    assert(sim A0 A0). apply sim_refl.
    forwards*: epre_sim H8 H2 H1.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts* nt. inverts H10.
  +
    inverts typ. inverts H3.
    forwards*: epre_sim H4 H1 tp.
    forwards*: IHep H8  H1.
    inverts H6; try solve[inverts* H0];
    try solve[forwards*:abs_epre_true ep];
    try solve[forwards*:absr_epre_true ep].
    * 
    forwards*: Typing_strenthening H0 H7.
    substs*.
Qed.



Theorem SGG_chk: forall e e' T E1 E2,
   epre e e' ->  
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
   epre e e' ->  
   Typing E1 e dir T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp.
  destruct dir.
  -
  forwards*: Typing_chk Typ1. inverts H.
  forwards*: SGG_chk H0.
  inverts H. inverts H1.
  inverts H0; try solve[forwards*:abs_epre_true ep].
  inverts H; try  solve[forwards*:absr_epre_true ep].
  forwards*: precise_type H1 H0.
  forwards*: inference_unique Typ1 H1. substs*.
  -
  forwards*: SGG_chk Typ1.
Qed.




Inductive epre : exp -> exp -> Prop :=    
 | ep_var : forall (x:var),
    epre (e_var_f x) (e_var_f x)
 | ep_i i:
    epre (e_lit i) (e_lit i)  
 | ep_abs : forall (e1 e2:exp) (L:vars) A1 B1 A2 B2,
     ( forall x , x \notin  L  -> 
      epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
      tpre (t_arrow A1 B1) (t_arrow A2 B2) ->
     epre (e_anno (e_abs e1) (t_arrow A1 B1)) (e_anno (e_abs e2) (t_arrow A2 B2))
 | ep_app : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_annor : forall (A:typ) (e1 e2:exp) B1 B2,
   Typing nil e1 Inf B1 ->
   Typing nil e2 Inf B2 ->
   epre e1 e2 ->
   tpre B1 A ->
   tpre B1 B2 ->
   epre e1 (e_anno e2 A)
 | ep_annol : forall (A:typ) (e1 e2:exp) B1 B2,
   Typing nil e1 Inf B1 ->
   Typing nil e2 Inf B2 ->
   epre e1 e2 ->
   tpre A B2 ->
   tpre B1 B2 ->
   epre (e_anno e1 A) e2
 | ep_appv : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_appv e1 e2) (e_appv e1' e2')
 | ep_apv : forall (e1 e2 e1' e2':exp) B1 B2,
     Typing nil e1 Inf B1 ->
     Typing nil e2 Inf B2 ->
     value e1 ->
     walue e2 ->
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_appv e1' e2').


Hint Constructors epre: core.



Lemma add_epre_true2: forall e2,
 epre e_add e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.

Lemma adda_epre_true2: forall e2 A,
 epre (e_anno e_add A) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto; try solve[forwards*: add_epre_true2 ep].
Qed.


Lemma addr_epre_true2: forall e1,
 epre e1 e_add  ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addi_epre_true2: forall i5 e2,
 epre (e_addl i5) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addir_epre_true2: forall i5 e2,
 epre e2  (e_addl i5) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.


Lemma addia_epre_true2: forall i5 e2 A,
 epre (e_anno (e_addl i5) A) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto;try solve[forwards*: addi_epre_true2 ep].
Qed.


Lemma abs_epre_true2: forall e1 e2,
 epre (e_abs e1) e2 ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma absr_epre_true2: forall e1 e2,
 epre e1 (e_abs e2) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma absra_epre_true2: forall e1 e2,
 epre e1 (e_anno (e_abs e2) t_dyn) ->
 False.
Proof.
  introv ep.
  inductions ep; eauto;try solve[forwards*: absr_epre_true2 ep].
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

Hint Resolve  flike_int addir_epre_true2 addr_epre_true2 absra_epre_true2 add_epre_true2 addi_epre_true2 adda_epre_true2 addia_epre_true2 abs_epre_true2 absr_epre_true2: falseHd.

Ltac solve_false := try intro; try solve [false; eauto with falseHd].



Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. 
  inductions ep; intros; eauto;
  try solve [inverts lc; eauto].
  inverts* lc. inverts* H3.
Qed.

Lemma epre_lc2: forall e1 e2,
 epre e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. 
  inductions ep; intros; eauto;
  try solve [inverts lc; eauto].
  inverts* lc. inverts* H3.
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 epre [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - 
    apply ep_abs with (L := (union L (singleton x))); intros; auto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
  -
    forwards*: IHep1 ep2 x.
   forwards*: value_no_fv H.
   forwards*: value_no_fv H0.
   assert([x ~> u2] (e2) = e2).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   assert([x ~> u1] (e1) = e1).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   rewrite <- H7 in H;eauto.
   rewrite <- H6 in H0;eauto.
   -
   forwards*: IHep1 ep2 x.
   forwards*: value_no_fv H.
   forwards*: value_no_fv H0.
   assert([x ~> u2] (e2) = e2).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   assert([x ~> u1] (e1) = e1).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   rewrite <- H7 in H;eauto.
   rewrite <- H6 in H0;eauto.
   -
   forwards*: epre_lc ep1_1.
   forwards*: IHep1_1 ep1_1 x.
   forwards*: epre_lc ep1_2.
   forwards*: IHep1_2 ep1_2 x.
   forwards*: value_no_fv H.
   forwards*: value_no_fv H0.
   assert([x ~> u1] (e1) = e1).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   assert([x ~> u1] (e2) = e2).
   forwards*: subst_exp_fresh_eq.
   fsetdec.
   rewrite <- H9 in H;eauto.
   rewrite <- H10 in H0;eauto.
   rewrite <- H9 in H1.
   rewrite <- H10 in H2.
   eapply ep_apv; eauto.
Qed. 

Lemma anno_chk: forall e t1 t2,
 [] ⊢ e_anno e t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.


Lemma tpre_principle: forall v1 v2,
 epre v1 v2 ->
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


Lemma epre_dyn: forall e1 e2 t1 t2,
 Typing nil e1 Inf (t_arrow t1 t2) ->
 Typing nil e2 Inf (t_arrow t_dyn t_dyn) ->
 value e1 ->
 value (e_anno e2 t_dyn) ->
 epre e1 (e_anno e2 t_dyn) ->
 epre e1 e2.
Proof.
  introv ty1 ty2 val1 val2 ep. gen t1 t2.
  inductions ep; intros;try solve_false; eauto.
  -
  inverts ty1.
  inverts* H2; try solve_false.
  eapply ep_annol; eauto.
  inverts val1.
  forwards*: Principle_inf H0.
  rewrite H2 in H7. subst*.
  -
  inverts ty1. inverts val1.
  inverts* H5; try solve_false.
  forwards*: Principle_inf H3.
  rewrite <- H8 in *. substs*.
Qed.


Lemma epre_value_arrow: forall v1 v2 t1 t2 tt1 tt2,
 Typing nil v1 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 epre v1 v2 ->
 value v1 ->
 value v2 ->
 principal_type v1 = (t_arrow t1 t2) ->
 ( exists v2', v2 = (e_anno v2' t_dyn) /\ 
 principal_type v2' = t_arrow t_dyn t_dyn) \/
 (exists v2' t3 t4, v2 = (e_anno v2' (t_arrow t3 t4))).
Proof.
  introv typ1 typ2 ep val1 val2 ty. gen tt1 tt2 t1 t2.
  inductions ep; intros;try solve[inverts* val1];
  try solve[inverts* ty];
  try solve[simpl in *; subst; inverts* H1;
  try solve[inverts* val1]].
  -
  simpl in ty. inverts ty.
  inverts* H.
  inverts val1. inverts val2.
  forwards*: tpre_principle ep.
  rewrite <- H3 in *.
  inverts* H.
  rewrite <- H6 in *. inverts H0.
  rewrite <- H6 in *. inverts* H0.
  -
  inverts val2.
  forwards*: tpre_principle ep.
  left.
  rewrite ty in *.
  forwards*: tpre_principle ep.
  rewrite ty in *.
  inverts H6; simpl in *;inverts* H3; try solve[inverts* H5]. 
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


Lemma tpre_v_dyn_int: forall i v,
 value (e_anno v t_dyn) ->
 epre (e_lit i) (e_anno v t_dyn) ->
 principal_type v = t_int.
Proof.
  introv val ep.
  inductions ep; eauto.
  inductions ep; eauto.
  inverts* val; simpl in *. 
  inverts* H9.
  forwards*: tpre_principle ep; simpl in *.
  rewrite <- H12 in *. inverts H7.
  forwards*: tpre_principle ep; simpl in *.
  inverts H12; simpl in *;inverts H11; try solve[inverts H8].
Qed.


Lemma tpre_v_dyn_fun: forall v1 v2,
 value (e_anno v1 (t_arrow t_dyn t_dyn))  ->
 value (e_anno v2 t_dyn) ->
 epre (e_anno v1 (t_arrow t_dyn t_dyn)) (e_anno v2 t_dyn) ->
 principal_type v2 = t_arrow t_dyn t_dyn.
Proof.
  introv val1 val2  ep.
  inductions ep; eauto; simpl in *.
  -
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep.
  rewrite <- H4 in *.
  inverts H3; inverts H0; inverts* H1. 
  -
  inverts val1. inverts val2. 
  forwards*: tpre_principle ep; simpl in *.
  inverts H6; inverts H3; inverts* H4. 
  -
  clear IHep.
  inverts val1. inverts val2.
  forwards*: epre_value_arrow ep.
  inverts H3.
  +
  lets(v2'&eq1&eq2): H8.
  inverts* eq1.
  +
  lets(v2'&t3&t4&eq): H8.
  inverts* eq.
Qed.


Lemma remove_left_dyn: forall v1 v2 t1 t2 tt1 tt2,
 Typing nil v1 Inf tt1 ->
 Typing nil (e_anno v2 t_dyn) Inf tt2 ->
 value v1 ->
 value (e_anno v2 t_dyn) ->
 principal_type v1 = (t_arrow t1 t2) ->
 principal_type v2 = (t_arrow t_dyn t_dyn) ->
 epre v1 (e_anno v2 t_dyn) ->
 epre v1 v2.
Proof.
  introv typ1 typ2 val1 val2 ty1 ty2 ep. gen tt1 tt2 t1 t2.
  inductions ep;intros; eauto.
  -
  inverts ty1; simpl in *. subst.
  inverts typ1. inverts typ2.
  inverts H3; try solve_false.
  inverts val2.
  forwards*: Principle_inf H0.
  rewrite ty2 in *. subst.
  inverts val1.
  inverts H2; try solve_false.
  forwards*: Principle_inf H3.
  rewrite <- H10 in *. subst.
  eapply ep_annol; eauto.
  -
  inverts* val2. inverts ty1; simpl in *. subst.
  inverts val1.
  forwards*: IHep v2.
  inverts H0. 
  inverts H5; inverts ty2; try solve_false. 
  inverts H10. inverts H5.
  forwards*: Principle_inf H.
  rewrite H5 in *. subst.
  eapply ep_annol; eauto.
Qed.




Lemma remove_left_dynarr: forall v1 v2 tt1 tt2,
 Typing nil v1 Inf tt1 ->
 Typing nil (e_anno v2 (t_arrow t_dyn t_dyn)) Inf tt2 ->
 value v1 ->
 value (e_anno v2 (t_arrow t_dyn t_dyn)) ->
 epre v1 (e_anno (e_anno v2 (t_arrow t_dyn t_dyn)) (t_arrow t_dyn t_dyn)) ->
 epre v1 (e_anno v2 (t_arrow t_dyn t_dyn)) .
Proof.
  introv typ1 typ2 val1 val2 ep. gen tt1 tt2.
  inductions ep; intros; eauto; try solve_false.
  -
  inverts typ1. inverts H.
  inverts typ2.
  inverts val1. 
  inverts H2; try solve_false.
  forwards*: Principle_inf H.
  rewrite <- H7 in *. subst.
  eapply ep_annol; eauto.
  -
  inverts H0. inverts H1. inverts val1.
  inverts typ2.  
  forwards*: IHep.
Qed.



Lemma tred_dyn_same: forall v0 v1 A v2 v3 tt1 tt2,
 Typing nil v3 Inf tt1 ->
 Typing nil v2 Inf tt2 ->
 value v3 ->
 epre v0 v1 ->
 epre v3 v2 ->
 value (e_anno v1 t_dyn) ->
 TypedReduce v1 A (e_exp v2) ->
 TypedReduce (e_anno v1 t_dyn) A (e_exp v2) \/
 (exists v4, 
  TypedReduce (e_anno v1 t_dyn) A (e_exp v4) /\ epre v3 v4).
Proof.
  introv typ1 typ2 val3 ep0 ep val red.
  inductions red; eauto;
  try solve[inverts val; inverts H1];
  try solve[inverts val; inverts H0];
  try solve[inverts val; inverts H3].
  -
  inverts val. rewrite H0 in *.
  inverts H2.
  destruct(eq_type A). destruct(eq_type B). subst.
  + 
  inverts H3; inverts* H0.
  right.
  exists. splits.
  apply TReduce_vany; eauto.
  unfold not; intros nt; inverts* nt. inverts H0.
  inverts typ2. inverts H4.
  forwards*: remove_left_dynarr ep.
  +
  inverts H3; inverts* H0; try solve_false.
  left.
  apply TReduce_dyna; eauto.
  unfold not; intros nt; inverts* nt. inverts H0.
  +
  inverts H3; inverts* H0;try solve_false.
  left.
  apply TReduce_dyna; eauto.
  unfold not; intros nt; inverts* nt. inverts H0.
  -
  inverts val.
  forwards*: value_lc H2.
  -
  assert(principal_type (e_lit i5) = t_int); simpl; auto.
  rewrite <- H; eauto.
  -
  inverts val. 
  forwards*: flike_not_ground H.
Qed.


Lemma tred_left: forall v1 v2 v1' t2 t,
 Typing nil v1 Chk t ->
 Typing nil v2 Inf t2 ->
 value v1 ->
 value v2 ->
 epre v1 v2 ->
 tpre t t2 ->
 TypedReduce v1 t (e_exp v1') ->
 epre v1' v2.
Proof.
  introv typ1 typ2 val1 val2 ep tp red.
  destruct t.
  -
    gen t2 v1'.
    inductions ep;intros; try solve_false;
    try solve[inverts val1];
    try solve[inverts* red].
    +
    inverts typ1. inverts typ2.
    inverts H0.
    inverts H5; try solve_false.
    inverts H6; try solve_false.
    inverts red; try solve_false; eauto.
    inverts* H.
    inverts val1. inverts val2.
    forwards*: Principle_inf H0.
    forwards*: Principle_inf H5.
    forwards*: tpre_principle ep.
    rewrite H in *.
    rewrite H14 in *.
    eapply ep_annor; eauto.
    +
    inverts typ2. 
    inverts tp; try solve[inverts val2].
    inverts val2.
    lets red': red.
    inverts* red; try solve_false.
    inverts H.
    inverts* H2.
    forwards*: IHep.
    inverts H10; try solve_false.
    eapply ep_annor; eauto.
    +
    inverts typ1. inverts H3.  
    inverts tp; try solve[inverts val2].
    *
    inverts red; try solve_false; eauto.
    *
    inverts red; try solve_false; eauto.
  -
    inverts ep; intros; try solve[inverts val1];
    try solve[inverts typ2; inverts tp].
    +
    inverts* red; simpl in *. inverts H6.
    inverts* typ2. inverts* typ1.
    inverts* H1.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve_false.
    inverts typ1; simpl in *.
    inverts typ2; simpl in *.
    inverts* H1.
    inverts val1. 
    inverts* H.
    inverts* H5; try solve_false.
    inverts typ1. inverts H5. inverts H10.
    inverts H5. inverts typ2.
    inverts H11; try solve_false.
    inverts H3. simpl in *.
    inverts val2.
    forwards*: tpre_principle H0; simpl in *.
    inverts* H14; simpl in *;try solve[inverts* H3];
    try solve_false. inverts H5.
    inverts H11.
    eapply ep_annor; eauto.
    inverts H11.
    +
    inverts typ2. inverts val2.
    inverts H7; try solve[inverts* H5];
    try solve[inverts* red]; try solve_false.
    *
    forwards*: tpre_principle H1; simpl in *.
    inverts H7.
    forwards*: Principle_inf H.
    rewrite <- H9 in *. subst*.
    inverts H0.
    inverts H6. inverts H0. inverts H8.
    forwards*: TypedReduce_preservation red.
    forwards*: tpre_principle H1; simpl in *.
    inverts val1; inverts* H6; try solve_false.
    inverts red; simpl in *.
    eapply ep_anno; eauto.
    *
    forwards*: TypedReduce_preservation red.
    inverts typ1; try solve_false.
    inverts val1; inverts H5;try solve[ inverts H9];
    try solve_false.
    --
    inverts red; simpl in *. subst*.
    --
    forwards*: tpre_principle H1; simpl in *.
    inverts H5.
    rewrite <- H16 in *.
    inverts H7.
    +
    inverts* red; simpl in *; subst*;
    try solve[inverts* typ2; inverts* typ1];
    try solve_false.
    *
    inverts typ1.
    forwards*: inference_unique typ2 H0.
    subst*.  inverts H4.
    eapply ep_annol; eauto.
    *
    inverts* H2.
  -
    inductions red; try solve[inverts* tp].
    +
    inverts* tp.
    inverts typ1; try solve_false.
    eapply ep_annol; eauto.
    +
    inverts* H. inverts tp.
    inverts typ1; try solve_false.
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
    inverts val1.
    rewrite x in *. inverts H1. 
Qed.


Lemma tdynamic_guarantee: forall e1 e2 e1' A B A1 B1,
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 A (e_exp e1') ->
 exists e2', TypedReduce e2 B (e_exp e2') /\ epre e1' e2'.
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen e1' A B A1 B1.
  inductions ep; intros; 
  try solve[inverts* val1];
  try solve[inverts* val2];
  try solve_false; eauto.
  - 
    inverts red; try solve[inverts* H3];
    try solve[inverts* tp].
    +
    inverts* tp.
    exists. splits*.
    +
    inverts* H2. inverts* H0. inverts* H2.
  -
    inductions red; eauto.
    +
    inverts tp.
    *
    inverts typ1. inverts H3.
    inverts typ2. inverts H3.
    forwards*: Typing_regular_1 H8.
    forwards*: Typing_regular_1 H11.
    destruct(eq_type A2). destruct(eq_type B2). subst.
    --
    exists(e_anno (e_anno (e_abs e2) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    --
    forwards*: value_no_fv H8.
    forwards*: value_no_fv H11.
    exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    eapply ep_annor; eauto; simpl in *; try fsetdec.
    --
    forwards*: value_no_fv H8.
    forwards*: value_no_fv H11.
    exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    eapply ep_annor; eauto; simpl in *; try fsetdec.
    *
    inverts typ1. inverts H3.
    inverts typ2. inverts H3.
    forwards*: epre_sim (t_arrow C0 D0) H2 H1.
    exists(e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow C0 D0)).
    splits*.
    +
    inverts tp. inverts H2. inverts* H1. inverts H5. inverts* H7.
    exists*.
    +
    inverts typ1. inverts H3.
    inverts typ2. inverts H3.
    inverts tp.
    destruct(eq_type A2). destruct(eq_type B2). subst.
    --
    exists(e_anno (e_anno (e_abs e2) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    eapply ep_annol; eauto. 
    --
    exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    --
    exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
  -
    inductions red; eauto;
    try solve_false;
    try solve[inverts* tp;inverts* H]; simpl in *; subst.
    +
    inverts H.
    *
    inverts val1. inverts val2.
    forwards*: tpre_principle ep. rewrite <- H4 in *.
    inverts H3; try solve[inverts* H;inverts* H0]; try solve_false.
    inverts H0.
    forwards*: value_lc H5.
    inverts typ1. inverts typ2. inverts H3. inverts H9.
    inverts H13. inverts H3.
    inverts H14; try solve_false.
    forwards*: Principle_inf H3. rewrite <- H4 in *. subst. 
    inverts* tp.
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    destruct(eq_type C2). destruct(eq_type D2). subst.
    assert(TypedReduce (e_anno (e_anno v (t_arrow t_dyn t_dyn)) t_dyn) 
    (principal_type ((e_anno v (t_arrow t_dyn t_dyn)))) (e_exp (e_anno v (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    exists((e_anno v (t_arrow t_dyn t_dyn))). splits*.
    eapply ep_annol; eauto. 
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow C2 D2)). splits*.
    apply TReduce_dyna; simpl;eauto.
    apply ep_anno; eauto.
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow C2 D2)). splits*.
    apply TReduce_dyna; simpl;eauto.
    apply ep_anno; eauto.
    *
    inverts typ1. inverts H.
    inverts typ2. inverts H. 
    inverts val1. inverts val2.
    inverts H7; try solve_false. inverts H10; try solve_false.
    forwards*: Principle_inf H. rewrite <- H12 in *. subst.
    forwards*: Principle_inf H7. rewrite <- H14 in *. subst.
    inverts tp.
    --
    destruct(eq_type C0). destruct(eq_type D0). subst.
    ++
    exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    ++
    exists(e_anno (e_anno (e_anno e2 (t_arrow C0 D0)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
    apply Typ_anno; eauto.
    ++
    exists(e_anno (e_anno (e_anno e2 (t_arrow C0 D0)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_annor with (B1 := (t_arrow A0 B0)) (B2:= (t_arrow t_dyn t_dyn)); simpl; eauto.
    apply Typ_anno; eauto.
    --
    forwards*: epre_sim (t_arrow C0 D0) (t_arrow C3 D3) H1.
    exists(e_anno (e_anno e2 (t_arrow C0 D0)) (t_arrow C3 D3)).
    splits*.
    +
    inverts tp.
    inverts val1; inverts* H0.
    inverts H. inverts* val2.
    inverts typ1. inverts H. inverts typ2. inverts H.
    forwards*: value_lc H1. 
    exists(e_anno e2 t_dyn). splits*.
    inverts H2. inverts H6.
    exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    +
    inverts tp. inverts* H.
    forwards*: epre_lc ep.
    +
    inverts typ1. inverts H1. inverts typ2. inverts H1.
    inverts tp.
    forwards*: flike_tpre H H0.
    lets(t1&t2&eq1&eq2): H1. subst.
    inverts eq2.
    *
    inverts val2. inverts val1.
    forwards*: tpre_principle ep.
    rewrite <- H14 in *.
    inverts H10; inverts* H7;inverts* H8; try solve_false.
    inverts H9. inverts H7.
    forwards*: value_lc H11.
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply ep_anno; eauto.
    eapply ep_annol; eauto.
    inverts H6; try solve_false.
    forwards*: Principle_inf H9. rewrite <- H14 in *. subst.
    eapply ep_annol ; eauto.
    *
    lets(t3&t4&eq2): H7. subst.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply ep_anno; eauto. 
    eapply ep_annol; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    +
    inverts H.
    inverts typ1. inverts H. inverts typ2. inverts H. 
    inverts val1. inverts val2.
    forwards*: flike_tpre tp H2.
    lets(t1&t2&eq1&eq2): H. subst.
    forwards*: tpre_principle ep.
    inverts H9; inverts H8;inverts* H0; try solve_false; simpl in *.
    inverts H7. inverts H0.
    inverts H12; inverts H11;inverts* H13; try solve_false.
    inverts eq2; subst.
    *
    forwards*: value_lc H0.
    exists(e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    *
    lets(t3&t4&eq3): H11. subst.
    inverts H10. inverts H12.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    assert(TypedReduce (e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) t_dyn) 
    (principal_type (e_anno v0 (t_arrow t_dyn t_dyn))) (e_exp (e_anno v0 (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    exists((e_anno v0 (t_arrow t_dyn t_dyn))). splits*.
    --
    exists(e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) (t_arrow t3 t4)).
    splits*.
    apply TReduce_dyna; simpl; eauto.
    --
    exists(e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) (t_arrow t3 t4)).
    splits*.
    apply TReduce_dyna; simpl; eauto.
    +
    inverts H. inverts val2.
    inverts val1. 
    forwards*: tpre_principle ep.
    inverts H4; simpl in *;try solve[inverts* H3].
    *
    inverts H2; try solve[inverts* H1; inverts* H]. 
    inverts tp.
    assert(t_int = (principal_type (e_lit i0))). simpl; auto.
    rewrite H2.
    exists((e_lit i0)). splits*.
    exists(e_anno (e_lit i0) t_dyn). splits*.
    *
    inverts H2; simpl in *;try solve[inverts* H;inverts* H1];
    try solve_false.
    *
    inverts tp.
    forwards*: value_lc H2.
    inverts typ1. inverts H7. 
    inverts typ2. inverts H7.
    inverts H12. inverts H7.
    inverts H15; try solve_false.
    inverts H3.
    forwards*: Principle_inf H7. rewrite H3 in *.
    exists(e_anno e2 t_dyn). splits*.
    
    inverts H2; simpl in *;try solve[inverts* H;inverts* H1];
    try solve_false.
    inverts* H1. inverts* H3. inverts H8. inverts H10. 
    assert((t_arrow t_dyn t_dyn) = (principal_type (e_anno v0 (t_arrow t_dyn t_dyn)))). simpl; auto.
    assert(TypedReduce (e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) t_dyn)
    (principal_type (e_anno v0 (t_arrow t_dyn t_dyn)))
    (e_exp (e_anno v0 (t_arrow t_dyn t_dyn)))).
    apply TReduce_vany; eauto.
    unfold not; intros nt; inverts* nt. inverts H2.
    exists((e_anno v0 (t_arrow t_dyn t_dyn))).
    splits*.
  -
    inverts typ2. inverts H3. inverts val2.
    +
    inverts H1. 
    inverts val1; try solve[inverts H]; 
    try solve_false.
    inverts H.
    inverts* red.
    * simpl in *. inverts H14.
    inverts tp.
    --
    destruct(eq_type A). destruct(eq_type B3). subst.
    ++
    exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    ++
    exists(e_anno (e_anno (e_anno e2 (t_arrow A B3)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    eapply ep_annor; eauto.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts* nt. inverts H13.
    eapply ep_anno; eauto.
    ++
    exists(e_anno (e_anno (e_anno e2 (t_arrow A B3)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_annor; eauto.
    --
    forwards*: Principle_inf H0.
    inverts H8; try solve_false.
    forwards*: Principle_inf H10.
    rewrite H in *. inverts H9. inverts H8.
    forwards*: epre_sim (t_arrow A B3) (t_arrow C2 D2) H6.
    exists(e_anno (e_anno e2 (t_arrow A B3)) (t_arrow C2 D2)).
    splits*.
    apply ep_anno; eauto.
    *
    inverts H13.
    inverts tp. inverts H11. inverts* H12.
    exists((e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn)).
    splits*.
    *
    inverts tp; simpl in *.
    destruct(eq_type A). destruct(eq_type B3). subst.
    -- 
    exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    --
    exists(e_anno (e_anno (e_anno e2 (t_arrow A B3)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_anno; eauto.
    --
    exists(e_anno (e_anno (e_anno e2 (t_arrow A B3)) (t_arrow t_dyn t_dyn)) t_dyn).
    splits*.
    apply TReduce_anyd; eauto; simpl; eauto.
    apply ep_anno; eauto.
    eapply ep_anno; eauto.
    +
    forwards*: IHep red tp.
    lets(v2'&rred&eep): H3.
    forwards*: Tred_value red.
    inverts typ1; try solve_false.
    forwards*: TypedReduce_sim red.
    inverts H8; try solve_false.
    forwards*: TypedReduce_sim red.
    forwards*: TypedReduce_sim rred.
    forwards*: TypedReduce_preservation red.
    forwards*: TypedReduce_preservation rred.
    forwards*: tred_dyn_same eep rred.
  -
    inverts typ1. inverts H3.
    inductions red;simpl in *;subst;
    try solve_false.
    +
    inverts val1.
    inverts tp.
    *
    forwards*: epre_value_arrow ep.
    inverts H3.
    lets(vv2&eq1&eq2): H7. subst.
    inverts val2.
    forwards*: value_lc H12.
    inverts H0.
    exists(e_anno vv2 t_dyn). splits*.
    eapply ep_annol; eauto.
    lets(vv2&t3&t4&eq3): H7. subst.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e_anno vv2 (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    --
    exists(e_anno (e_anno (e_anno vv2 (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.  
    --
    exists(e_anno (e_anno (e_anno vv2 (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    *
    forwards*: epre_value_arrow ep.
    inverts H3.
    lets(vv2&eq1&eq2): H7. subst.
    ++
    inverts val2.
    inverts typ2. inverts H3.
    inverts H19; try solve_false.
    inverts H8; try solve_false.
    forwards*: remove_left_dyn ep.
    forwards*: Principle_inf H19.
    forwards*: Principle_inf H3.
    rewrite eq2 in *. subst.
    rewrite <- H11 in *.
    destruct(eq_type C1). destruct(eq_type D1). subst.
    --
    exists(vv2). splits*.
    rewrite <- eq2.
    apply TReduce_vany; eauto.
    eapply ep_annol; eauto.
    --
    exists(e_anno (vv2 ) (t_arrow C1 D1)). splits*.
    apply TReduce_dyna; simpl; eauto.
    rewrite eq2; auto.
    apply ep_anno; eauto.  
    --
    exists(e_anno (vv2 ) (t_arrow C1 D1)). splits*.
    apply TReduce_dyna; simpl; eauto.
    rewrite eq2; auto.
    apply ep_anno; eauto.  
    ++
    lets(vv2&t3&t4&eq3): H7. subst.
    inverts H0.
    forwards*: epre_sim (t_arrow C1 D1) H4 H1.
    exists(e_anno (e_anno vv2 (t_arrow t3 t4)) (t_arrow C1 D1)).
    splits*.
    +
    inverts tp. inverts H3;inverts val1.
    forwards*: Principle_inf H. 
    rewrite <- H10 in *. subst.
    inverts H7; inverts H; try solve_false.
    inverts H1.
    *
    inverts val2; inverts H0.
    forwards*: value_lc H1.
    exists(e_anno v0 t_dyn). splits*.
    eapply ep_annol; eauto.
    *
    inverts H9. inverts H12.
    forwards*: Principle_inf H0.
    exists(e_anno e2 t_dyn). splits*.
    apply  TReduce_v; eauto.
    rewrite H; auto.
    +
    inverts H1. inverts tp.
    inverts val1.
    inverts val2; inverts H0.
    forwards*: value_lc H9.
    +
    inverts tp.
    forwards*: flike_tpre H1 H3.
    lets(t1&t2&eq1&eq2): H6. subst.
    inverts H1.
    * 
    inverts val2; inverts H0.
    forwards*: value_lc H7.
    exists(e_anno v t_dyn). splits*.
    eapply ep_annol; eauto.
    eapply ep_annol; eauto.
    *
    inverts eq2; try solve[inverts H1].
    lets(t3&t4&eq3): H1. inverts eq3.
    inverts val2; inverts H0; try solve_false.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply ep_anno; eauto. 
    eapply ep_annol; eauto.
    --
    exists(e_anno (e_anno (e_anno v (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_anno; eauto.
    apply ep_anno; eauto.  
    --
    exists(e_anno (e_anno (e_anno v (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn). splits*.
    apply TReduce_anyd; simpl; eauto.
    apply ep_anno; eauto.
    apply ep_anno; eauto.  
    +
    inverts val1. inverts H1.
    inverts val2; inverts H0.
    forwards*: flike_tpre tp H5.
    lets(t1&t2&eq1&eq2): H0. 
    inverts eq2; subst.
    *
    forwards*: value_lc H9.
    exists(e_anno v t_dyn). splits*.
    *
    lets(t3&t4&eq3): H12. inverts eq3.
    inverts H11; inverts H4; inverts H10;try solve_false.
    forwards*: tpre_v_dyn_fun ep.
    destruct(eq_type t3). destruct(eq_type t4). subst.
    --
    inverts H14; try solve_false.
    forwards*: Principle_inf H10.
    rewrite H4 in *. subst.
    assert(TypedReduce (e_anno v t_dyn) (principal_type (v)) (e_exp v)).
    apply TReduce_vany; eauto.
    rewrite H4 in *.
    forwards*: remove_left_dyn ep.
    apply value_dyn; eauto. rewrite H4; auto.
    inverts H.
    exists v. splits*.
    --
    inverts H8. inverts H16.
    inverts typ2. inverts H8.
    inverts H25; try solve_false.
    forwards*: remove_left_dyn ep.
    exists(e_anno v (t_arrow t3 t4)). splits.
    apply TReduce_dyna; eauto.
    rewrite H4; eauto.
    eapply ep_anno; eauto.
    --
    inverts H8. inverts H11.
    inverts typ2. inverts H8.
    inverts H24; try solve_false.
    forwards*: remove_left_dyn ep.
    exists(e_anno v (t_arrow t3 t4)). splits.
    apply TReduce_dyna; eauto.
    rewrite H4; eauto.
    eapply ep_anno; eauto.
    +
    inverts val1. inverts H1.
    inverts val2; inverts H0.
    inverts H9; inverts H7; simpl in *;try solve_false.
    *
    forwards*: tpre_v_dyn_int ep.
    *
    forwards*: tpre_v_dyn_fun ep.
    inverts tp.
    forwards*: value_lc H6.
    inverts H13. inverts H15.
    inverts H12; try solve_false.
    assert(TypedReduce (e_anno v t_dyn) (principal_type v) (e_exp v)).
    apply TReduce_vany; eauto.
    rewrite H7 in H12; auto.
    forwards*: remove_left_dyn ep.
Qed.


Lemma epre_lit_false: forall v1 t1 t2 i,
 value v1 ->
 principal_type v1 = (t_arrow t1 t2) ->
 epre (v1 ) (e_anno (e_lit i) t_dyn) ->
 False.
Proof.
  introv val ty ep. gen t1 t2.
  inductions ep; intros; simpl in *;eauto.
  -
  subst.
  inverts val.
  forwards*: tpre_principle ep; simpl in *.
  rewrite <- H4 in *.
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




Lemma tred_right: forall v1 v2 t1 t,
 Typing nil v1 Inf t1 ->
 Typing nil v2 Chk t ->
 value v1 ->
 value v2 ->
 epre v1 v2 ->
 tpre t1 t ->
 exists v2', TypedReduce v2 t (e_exp v2') /\
 epre v1 v2'.
Proof.
  introv typ1 typ2 val1 val2 ep tp.
  destruct t.
  -
    inverts ep; intros; try solve_false;
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1].
    +
    inverts typ2. inverts H4.
    inverts val2; try solve[inverts H5].
    inverts tp.
    inverts val1; inverts typ1.
    forwards*: tpre_principle H1; simpl in *.
    inverts H10; simpl in *; inverts* H4;inverts H8.
    inverts H.
    inverts* H1.
    inverts* H0.
    exists(e_lit i0). splits*.
    apply TReduce_vany; try solve[unfold not; intros nt;
    inverts* nt;inverts H].
  -
    inverts ep; intros; try solve_false;
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1].
    +
    inverts typ2. inverts H1.
    inverts typ1.
    exists(e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t2 t3)).
    splits*.
    +
    inverts tp. inverts typ1. inverts val1.
    inverts val2.
    *
    inverts typ2. inverts H1.
    exists(e_anno (e_anno e2 (t_arrow A B1) ) (t_arrow t2 t3)).
    splits*.
    eapply ep_annor; eauto.
    *
    forwards*: tpre_principle H0.
    rewrite <- H8 in *.
    inverts H9; simpl in *; inverts H1; inverts H7;
    try solve_false.
    inverts typ2. inverts H1. inverts H14.
    inverts H1.
    inverts H3; try solve_false; simpl in *.
    forwards*: Principle_inf H1.
    rewrite H3 in *. inverts H8.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    exists( (e_anno v (t_arrow t_dyn t_dyn))).
    splits*.
    apply  TReduce_vany.
    unfold not;intros nt;inverts nt. inverts H8.
    ---
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    ---
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    +
    inverts tp. inverts typ2. inverts H4.
    inverts val2.
    *
    inverts H11; try solve_false.
    forwards*: Principle_inf H0.
    rewrite <- H12 in *.
    subst*.
    forwards*: Principle_inf H.
    forwards*: Principle_inf typ1.
    rewrite H11 in H14.
    rewrite H14 in *.
    exists(e_anno (e_anno e2 (t_arrow A B0)) (t_arrow t2 t3)).
    splits*.
    eapply ep_annor; eauto.
    *
    forwards*: tpre_principle H1.
    forwards*: Principle_inf typ1.
    rewrite H9 in *.
    inverts H12; simpl in *; 
    inverts H4; inverts H10; try solve_false.
    forwards*: Principle_inf H.
    rewrite H4 in H9. rewrite H9 in H.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    inverts H0. 
    exists( (e_anno v (t_arrow t_dyn t_dyn)) ).
    splits*.
    apply  TReduce_vany.
    unfold not;intros nt;inverts nt. inverts H0.
    ---
    inverts H0.
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    unfold not;intros nt;inverts nt. inverts H0.
    ---
    inverts H0.
    exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    unfold not;intros nt;inverts nt. inverts H0.
    +
    inverts tp. inverts typ1.
    inverts typ2; try solve_false.
    inverts val1.
    forwards*: tpre_principle H1.
    rewrite <- H14 in *.
    inverts H6; try solve_false.
    forwards*: Principle_inf H11.
    rewrite H6 in *. subst*.
    inverts val2; simpl in *;inverts H10; try solve_false.
    *
    inverts H4.
    exists(e_anno (e_anno v (t_arrow A1 B0)) (t_arrow t2 t3)).
    splits*.
    *
    inverts H12; simpl in *; inverts H6; try solve_false. 
    inverts H16; inverts H14;try solve_false.
    --
    forwards*: epre_lit_false H1.
    --
    forwards*: remove_left_dyn H1.
    destruct(eq_type t2).
    destruct(eq_type t3). subst.
    ---
    inverts H0. inverts H19. inverts H0.
    forwards*: Principle_inf H; simpl in *.
    rewrite <- H0 in *. inverts H.
    inverts H4. inverts H20.
    exists( (e_anno v1 (t_arrow t_dyn t_dyn)) ).
    splits*.
    apply  TReduce_vany.
    unfold not;intros nt;inverts nt. inverts H20.
    ---
    exists(e_anno (e_anno v1 (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    unfold not;intros nt;inverts nt. inverts H19.
    ---
    exists(e_anno (e_anno v1 (t_arrow t_dyn t_dyn)) (t_arrow t2 t3)).
    splits*.
    apply TReduce_dyna; simpl;eauto.
    unfold not;intros nt;inverts nt. inverts H18.
  -
    inverts ep; intros; try solve_false;
    try solve[inverts val1];
    try solve[inverts typ1;inverts tp];
    try solve[inverts tp; inverts* val1];
    try solve[inverts typ1;inverts tp;inverts* val1].
    +
     exists(e_anno (e_lit i) t_dyn).
     splits*.
    +
     destruct(eq_type A2).
     destruct(eq_type B2).
     subst.
     *
     inverts typ1. inverts typ2. inverts H1.
     exists(e_anno (e_anno (e_abs e2) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     *
     inverts typ1. inverts typ2. inverts H3.
     exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     *
     inverts typ1. inverts typ2. inverts H2.
     exists(e_anno (e_anno (e_anno (e_abs e2) (t_arrow A2 B2)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
    +
     inverts val2.
     *
     inverts H.
     destruct(eq_type A0).
     destruct(eq_type B0).
     subst.
     --
     inverts typ1. inverts typ2. inverts H.
     exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     eapply ep_annor; eauto.
     --
     inverts typ1. inverts typ2. inverts H2.
     exists(e_anno (e_anno (e_anno e2 (t_arrow A0 B0)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     inverts typ1. inverts typ2. inverts H1.
     exists(e_anno (e_anno (e_anno e2 (t_arrow A0 B0)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     *
     exists(e_anno e2 t_dyn). splits*.
    +
     inverts val2.
     *
     forwards*: tpre_principle H1.
     rewrite <- H7 in *. 
     inverts val1; inverts H4; try solve_false.
     destruct(eq_type A0).
     destruct(eq_type B).
     subst.
     --
     inverts typ2. inverts H4.
     exists(e_anno (e_anno e2 (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     --
     inverts typ2.  inverts H10.
     inverts typ1. inverts H. 
     exists(e_anno (e_anno (e_anno e2 (t_arrow A0 B)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     --
     inverts typ2.  inverts H9.
     inverts typ1. inverts H. 
     exists(e_anno (e_anno (e_anno e2 (t_arrow A0 B)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     eapply ep_annor; eauto.
     eapply ep_annor; eauto.
     *
     exists(e_anno e2 t_dyn). splits*.
    +
     inverts val1.
     *
     inverts typ1. 
     inverts H2.
     --
     forwards*: tpre_principle H1.
     rewrite <- H7 in *.
     inverts val2; try solve[inverts H0]; simpl in *.
     exists(e_anno v t_dyn). splits*.
     --
     inverts val2; inverts H0; try solve_false.
     inverts typ2. inverts H0.
     forwards*:Principle_inf H. rewrite <- H7 in *.
     subst*.
     destruct(eq_type C0).
     destruct(eq_type D0).
     subst.
     ---
     exists(e_anno (e_anno v (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     ---
     exists(e_anno (e_anno (e_anno v (t_arrow C0 D0)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     ---
     exists(e_anno (e_anno (e_anno v (t_arrow C0 D0)) (t_arrow t_dyn t_dyn)) t_dyn).
     splits*.
     apply TReduce_anyd; simpl;eauto.
     *
     inverts typ1.
     inverts H2.
     inverts val2; inverts H0.
     forwards*: value_lc H4.
     exists(e_anno v t_dyn). splits*.
Qed.



Lemma value_tred_keep: forall v v' A,
 Typing nil v Chk A ->
 value (e_anno v A) ->
 TypedReduce v A (e_exp v') ->
 v' = (e_anno v A).
Proof.
  introv typ val red.
  inverts* val; simpl in *.
  -
  inverts* typ; simpl in *; subst.
  inverts* H2.
  inverts* red.
  forwards*: Principle_inf H.
  rewrite <- H4 in *.
  subst*.
  rewrite <- H2 in *.
  inverts* red; try solve[simpl in *; inverts* H2].
  -
  inverts* red; simpl in *; inverts* H1.
  rewrite <- H0 in *. inverts* H3. inverts* H1.
  inverts* H4.
  rewrite <- H0 in *. inverts* H3. 
Qed.


Lemma epre_val: forall v1 v2 t1 t2,
 Typing nil v1 Chk t1 ->
 Typing nil v2 Chk t2 ->
 epre v1 v2 ->
 value v1 ->
 exists v2', steps v2 (e_exp v2') /\ value v2' /\ epre v1 v2'.
Proof.
  introv typ1 typ2 ep val. gen t1 t2.
  inductions ep; intros;try solve[inverts* val];
  try solve_false.
  -
  forwards*: Typing_regular_1 typ2. inverts H2.
  exists.
  splits*.
  -
  inverts typ2. inverts H0.
  inverts typ1. inverts H0.
  forwards*: IHep H5.
  inverts* val.
  lets(v2'&red&val2&epr): H0.
  inverts val.
  +
  inverts H.
  *
  forwards*: preservation_multi_step red.
  inverts H8; try solve_false.
  inverts H; try solve_false.
  forwards*: epre_value_arrow epr. inverts H.
  lets(v21&eq&eq2): H14. substs.
  exists((e_anno v21 t_dyn)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  forwards*: value_lc val2. inverts H.
  apply Step_annov; eauto.
  unfold not; intros nt; inverts* nt. inverts H15.
  inverts H8.
  eapply ep_annol; eauto.
  lets(v21&t3&t4&eq): H14. substs.
  destruct(eq_type t3).
  destruct(eq_type t4); subst.
  exists((e_anno (e_anno v21 (t_arrow t_dyn t_dyn)) t_dyn)).
  splits*.
  apply multi_rred_anno. apply red.
  exists((e_anno (e_anno (e_anno v21 (t_arrow t_dyn t4)) (t_arrow t_dyn t_dyn)) t_dyn)).
  splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply TReduce_anyd; simpl; eauto.
  unfold not; intros nt; inverts* nt. inverts* H16.
  apply value_dyn; eauto.
  eapply value_fanno; eauto. reflexivity.
  inverts H8.
  eapply ep_annor; eauto.
  exists((e_anno (e_anno (e_anno v21 (t_arrow t3 t4)) (t_arrow t_dyn t_dyn)) t_dyn)).
  splits.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply TReduce_anyd; simpl; eauto.
  unfold not; intros nt; inverts* nt. inverts* H16.
  apply value_dyn; eauto.
  eapply value_fanno; eauto. reflexivity.
  inverts H8.
  eapply ep_annor; eauto.
  *
  forwards*: preservation_multi_step red.
  inverts H8; try solve_false.
  inverts H; try solve_false.
  forwards*: epre_value_arrow epr. inverts H.
  lets(v21&eq&eq2): H16. substs.
  inverts val2; try solve_false.
  forwards*: Principle_inf H6.
  rewrite <- H10 in *. substs.
  inverts* H8; try solve_false.
  inverts* H20; try solve_false.
  forwards*: Principle_inf H.
  rewrite eq2 in H20. substs.
  forwards*: epre_dyn epr.
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
  unfold not; intros nt; inverts* nt; try solve_false.
  exists(e_anno v21 (t_arrow t_dyn D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply  TReduce_dyna; eauto.
  rewrite eq2; auto.
  unfold not; intros nt; inverts* nt; try solve_false.
  exists(e_anno v21 (t_arrow C0 D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply stars_one.
  apply Step_annov; eauto.
  apply  TReduce_dyna; eauto.
  rewrite eq2; auto.
  unfold not; intros nt; inverts* nt; try solve_false.

  lets(v21&t3&t4&eq): H16. substs.
  exists(e_anno ((e_anno v21 (t_arrow t3 t4))) (t_arrow C0 D0)).
  splits*.
  eapply stars_trans.
  apply multi_rred_anno. apply red.
  apply step_refl.
  eapply value_fanno; eauto.
  reflexivity.
  +
  inverts H.
  forwards*: preservation_multi_step red.
  assert(TypedReduce e1 t_dyn (e_exp (e_anno e1 t_dyn))); eauto.
  forwards*: tdynamic_guarantee epr H.
  lets(e2'&tred&epp): H7.
  forwards*: value_lc val2.
  destruct(value_decidable (e_anno v2' t_dyn)); eauto.
  exists (e_anno v2' t_dyn).
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
  inverts typ2. inverts H3.
  forwards*: IHep.
  inverts H3. inverts H6. inverts H7.
  forwards*: preservation_multi_step H8 H3.
  inverts H7; try solve_false.
  forwards*: tred_right H9 H1.
  lets(v2'& rred& epp):H7.
  forwards*: Tred_value rred.
  exists v2'. splits*.
  eapply stars_trans.
  apply multi_rred_anno; eauto.
  forwards*: value_lc H6.
  destruct(value_decidable (e_anno x A0)); auto.
  forwards*:value_tred_keep rred. subst*.
  -
  inverts typ1. inverts H3.
  forwards*: IHep.
  inverts* val.
  inverts H3. inverts H6. inverts H7.
  forwards*: preservation_multi_step H0 H3.
Qed.



Lemma epre_wal: forall v1 v2,
 epre v1 v2 ->
 walue v1 ->
 value v2 ->
 walue v2.
Proof.
  introv ep wal val.
  inductions ep; try solve[inverts* wal;try solve_false];
  try solve[inverts* val].
  -
  inverts* val. inverts* wal;
  try solve_false.
  inverts* wal; try solve_false. 
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



Lemma fill_app: forall e1 e2,
  lc_exp e2 ->
  (e_app e1 e2) = (fill (appCtxL e2)  e1).
Proof.
  introv lc.
  unfold fill; eauto.
Qed.



Lemma fill_anno: forall e t,
  (e_anno e t) = (fill (annoCtx t)  e).
Proof.
  introv.
  unfold fill; eauto.
Qed.





Lemma unwrap_epre: forall v1 v2 v3 v4 t1 t2 t3 t4 tt1 tt2,
 Typing nil (e_appv (e_anno (e_anno v1 (t_arrow t1 t2)) (t_arrow t3 t4)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno (e_anno v1 (t_arrow t1 t2)) (t_arrow t3 t4)) ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre (e_anno (e_anno v1 (t_arrow t1 t2)) (t_arrow t3 t4)) v3 ->
 epre v2 v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ (epre (e_anno (e_app (e_anno v1 (t_arrow t1 t2)) v2) t4) e2').
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros.
  -
    inverts typ1. inverts H0.
    inverts H9. inverts H11. inverts H0. 
    inverts typ2. inverts H0. inverts H18.  
    inverts val3.
    inverts H17; simpl in *; inverts H20; try solve_false.
    inverts H.
    exists. splits.
    apply stars_one.
    apply Step_abeta; eauto.
    apply ep_anno; eauto.
  -
    inverts typ1. inverts H3. inverts H12.
    inverts typ2. inverts H3. inverts H19.
    inverts H. inverts H18. inverts H.
    inverts val3. 
    inverts H3.
    inverts H12; try solve_false.
    forwards*: principle_inf H. 
    rewrite H12 in H23. inverts H23.
    inverts H3.
    apply BA_AB in H27.
    forwards*: tpre_principle ep1; simpl in *.
    rewrite H12 in *. inverts H3.
    forwards*: tred_right ep2.
    lets (vv1&rred1&epp1): H3.
    inverts H19; inverts H; try solve_false.
    forwards*: TypedReduce_preservation rred1.
    forwards*: TypedReduce_walue rred1.
    forwards*: IHep1 v1 epp1.
    eapply Typ_sim; eauto.
    unfold not; intros nt;inverts nt. inverts H25.
    lets (vv&rred&epp): H25.
    forwards*: preservation_multi_step rred.
    inverts H1.
    inverts H9.
    exists. splits.
    eapply stars_trans.
    apply stars_one.
    apply Step_abeta; eauto.
    eapply stars_trans.
    apply stars_one.
    rewrite fill_anno.
    apply do_step; auto.
    eapply Step_equal; simpl; eauto. simpl.
    apply multi_rred_anno.
    apply rred.
    eapply ep_annor; eauto.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    eapply Typ_app; eauto.
    inverts H14. inverts H1. inverts H9.
    apply BA_AB in H40; eauto.
    unfold not; intros nt;inverts nt. inverts H1.    
  -
    inverts typ1. inverts H3. inverts H12.
    inverts H.
    inverts typ2. inverts H. 
    forwards*: principle_inf H19.
    forwards*: principle_inf H0.
    rewrite H in *. inverts H11.
    inverts val1.
    forwards*: tpre_principle ep1; simpl in *.
    rewrite H in *. inverts H11.
    inverts H1.
    inverts H14. inverts H1. inverts H11.
    apply BA_AB in H28.
    exists. splits.
    apply step_refl.
    eapply ep_annol; eauto.
Qed.


Lemma beta_epre: forall e v2 v3 v4 t1 t2 tt1 tt2,
 Typing nil (e_appv (e_anno (e_abs e) (t_arrow t1 t2)) v2) Chk tt1 ->
 Typing nil (e_appv v3 v4) Chk tt2 ->
 value (e_anno (e_abs e) (t_arrow t1 t2)) ->
 walue v2 ->
 value v3 ->
 walue v4 ->
 epre (e_anno (e_abs e) (t_arrow t1 t2)) v3 ->
 epre v2 v4 ->
 exists e2', steps (e_appv v3 v4) (e_exp e2') /\ epre (e_anno (e ^^ v2) t2) e2'.
Proof.
  introv typ1 typ2 val1 val2 val3 val4 ep1 ep2. 
  gen tt1 tt2 v2 v4.
  inductions ep1; intros; try solve_false.
  -
  inverts typ1. inverts H2. inverts H11. inverts H1.
  inverts typ2. inverts H1. inverts H19. 
  forwards*: walue_lc val4.
  forwards*: walue_lc val2.
  inverts val3. inverts H19.
  exists. splits.
  apply stars_one.
  apply Step_beta; eauto.
  apply ep_anno; eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); eauto.
  assert((e2 ^^ v4) = [y ~> v4] (e2 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H11.
  forwards*: H y.
  forwards*: epre_open H19 ep2.
  -
  inverts typ1. inverts H3. inverts H12. inverts H14; try solve_false.
  inverts typ2. inverts H3. inverts H19. 
  inverts val3.  inverts H.
  forwards*: principle_inf H0. rewrite H in *. inverts H21.
  inverts H18; simpl in *;inverts H;try solve_false.
  inverts H14. inverts H. inverts H18.
  forwards*: tpre_principle ep1; simpl in *.
  inverts H.
  apply BA_AB in H24.
  forwards*: tred_right ep2.
  lets (vv1&rred1&epp1): H.
  forwards*: TypedReduce_walue rred1.
  forwards*: TypedReduce_preservation rred1. 
  forwards*: IHep1 epp1.
  eapply Typ_sim; eauto.
  unfold not; intros nt;inverts nt. inverts H22.
  lets (vv2&rred2&epp2): H22.
  inverts H1. inverts H16; simpl in *. inverts H32.
  forwards*: preservation_multi_step rred2.
  exists. splits.
  eapply stars_trans.
  apply stars_one.
  apply Step_abeta; eauto.
  rewrite fill_anno.
  eapply stars_trans.
  apply stars_one.
  apply do_step; auto.
  eapply Step_equal;simpl; auto.
  apply rred1.
  unfold fill.
  apply multi_rred_anno. apply rred2.
  eapply ep_annor; eauto.
  apply Typ_anno; eauto.
  pick fresh y .
  forwards*: H12 y.
  rewrite (subst_exp_intro y); eauto.
  eapply typing_c_subst_simpl; eauto.
Qed.



Lemma dynamic_guarantee_chk: forall e1 e2 e1' T1 T2,
 epre e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 -> 
 step e1 (e_exp e1') ->
 exists e2', steps e2 (e_exp e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' T1 T2.
  inductions ep; intros;
  try solve[inverts* red;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* red;destruct E; unfold fill in H1; inverts* H1];
  try solve[forwards*: step_not_value red ];
  try solve_false.
  - forwards*: Typing_regular_1 typ1. inverts H2.
    inverts red;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H6].
    inverts* H6.
  - 
    inverts* red; try solve_false.
    + destruct E; unfold fill in H; inverts* H.
      *
      inverts typ1. inverts typ2.
      inverts H. inverts H4.
      forwards*: Typing_chk H11. inverts H.
      forwards*: Typing_chk H13. inverts H.
      forwards*: IHep1 H2. inverts H. inverts H10.
      exists. split. inverts H1. apply multi_rred_app2.
      forwards*: epre_lc ep2. apply H.
      unfold fill. eauto.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H12. inverts H. inverts H4.
      inverts H1. 
      forwards*: Typing_chk H13. inverts H1.
      forwards*: Typing_chk H11. inverts H1.
      forwards*: epre_val ep1. 
      inverts H1. inverts H16. inverts H17.
      forwards*: Typing_regular_1 H12.
      forwards*: epre_lc ep2.
      exists(e_app x2 x). split. 
      apply stars_trans with (b:=e_app x2 e2').
      apply multi_rred_app2;auto.
      apply multi_rred_app;auto.
      unfold fill. eauto.
    +
      inverts typ1. inverts H. 
      inverts typ2. inverts H.
      forwards*: Typing_chk H13. inverts H.
      forwards*: Typing_chk H8. inverts H.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H.
      forwards*: epre_val ep2.
      lets(vv2&red2&val2&epp2):H12.
      forwards*: tpre_principle epp1; simpl in *.
      inverts val1; simpl in *; inverts H15.
      forwards*: value_lc H3.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 H18 red1.
      forwards*: multi_rred_app ( e_anno v t_dyn) red2.
      exists. splits.
      eapply stars_trans.
      apply H19.
      eapply stars_trans.
      apply H20.
      apply stars_one.
      apply Step_betad; eauto.
      apply ep_app; eauto.
    +
      inverts typ1. inverts H. 
      inverts typ2. inverts H.
      forwards*: Typing_chk H10. inverts H.
      forwards*: Typing_chk H15. inverts H.
      forwards*: epre_val ep1.
      lets(vv1&red1&val1&epp1):H.
      forwards*: epre_val ep2.
      lets(vv2&red2&val2&epp2):H14.
      forwards*: principle_inf H10.
      forwards*: tpre_principle epp1; simpl in *.
      rewrite H17 in *. subst*.
      inverts H8.
      forwards*: preservation_multi_step H15 red1.
      forwards*: preservation_multi_step H16 red2.
      inverts val1; simpl in *; inverts H18; try solve_false.
      *
      inverts H4. inverts H13.
      forwards*: tdynamic_guarantee epp2 H24 H5.
      lets(vv3&ttred&epp3):H4.
      forwards*: value_lc H3.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 H18 red1.
      forwards*: multi_rred_app (e_anno v (t_arrow A4 A2)) red2.
      exists. splits.
      eapply stars_trans.
      apply H21. 
      eapply stars_trans.
      apply H23.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      apply ep_appv; eauto.
      *
      inverts H20; inverts H19; try solve_false.
      forwards*: epre_lit_false epp1.
      forwards*: remove_left_dyn epp1.
      inverts H4. inverts H13. 
      inverts H23. inverts H4.
      forwards*: value_lc H3.
      forwards*: epre_lc ep2.
      forwards*: multi_rred_app2 H22 red1.
      forwards*: multi_rred_app (e_anno (e_anno v0 (t_arrow t_dyn t_dyn)) t_dyn) red2.
      forwards*: value_lc val2.
      forwards*: tdynamic_guarantee epp2 H5.
      lets(vv3&ttred&epp3):H27.
      exists. splits.
      eapply stars_trans.
      apply H23.
      eapply stars_trans.
      apply H25.
      eapply stars_trans.
      apply stars_one.
      apply Step_betad; eauto.
      eapply stars_trans.
      apply stars_one.
      rewrite fill_app; eauto.
      apply do_step; eauto.
      apply Step_annov; eauto.
      apply TReduce_vany; eauto.
      unfold not; intros nt; inverts* nt. inverts H32.
      unfold fill.
      apply stars_one.
      eapply Step_equal; simpl ;auto.
      eapply value_fanno; eauto.
      apply ttred.
      apply ep_appv; eauto.
  -
    inverts typ1. inverts H0. inverts typ2. inverts H0.
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H0.
    forwards*: IHep H9.
    lets(e2'&red&epp): H0.
    forwards*: multi_rred_anno A red.
    +
    forwards*: value_lc H7.
    forwards*: epre_lc ep.
    forwards*: epre_val ep.
    lets(v2&red&vval&epp1): H10.
    forwards*: preservation_multi_step red.
    forwards*: tdynamic_guarantee epp1 H H9.
    lets(v2'&tred&epp2):H13.
    forwards*: multi_rred_anno A red.
    forwards*: Tred_value H9.
    forwards*: value_lc H15.
    forwards*: epre_lc epp1.
    destruct(value_decidable (e_anno v2 A)); eauto.
    *
    forwards*: TypedReduce_preservation H9.
    forwards*: value_tred_keep tred. subst*.
    *
    exists v2'. splits*.
  -
    inverts typ2. inverts H3.
    forwards*: IHep red.
    lets(ee2'&rred&epp): H3.
    forwards*: preservation_multi_step H0 rred.
    forwards*: Typing_regular_1 H6.
    forwards*: preservation H red.
    exists(e_anno ee2' A0).
    splits*.
    apply multi_rred_anno; auto.
  -
    inverts typ1. inverts H3.
    inverts red.
    +
    destruct E; unfold fill in *; inverts* H3.
    forwards*: IHep H9.
    lets(e2'&red&epp): H3.
    forwards*: preservation_multi_step H0 red.
    forwards*: preservation H H9.
    +
    forwards*: epre_val ep.
    lets(v2&red&vval&epp): H3.
    forwards*: preservation_multi_step H0 red.
    forwards*: tred_left epp H1.
  -
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    inverts red;  try solve_false.
    +
    destruct E; unfold fill in * ; inverts H.
    +
    forwards*:  beta_epre ep1 ep2.
    +
    forwards*: unwrap_epre ep1 ep2.
  -
    inverts typ1. inverts H3.
    inverts typ2. inverts H3.
    inverts red;  try solve_false.
    +
    destruct E; unfold fill in * ; inverts H3.
    forwards*: step_not_value H16.
    forwards*: step_not_value H16.
    +
    forwards*: tpre_principle ep1; simpl in *.
    forwards*: principle_inf H17. rewrite H9 in *.
    inverts H3.
    +
    inverts H8.
    *
    forwards*: principle_inf H10. rewrite H3 in *.
    inverts H20.
    forwards*: principle_inf H17.
    forwards*: tpre_principle ep1.
    rewrite H3 in *. rewrite H8 in *.
    inverts H9.
    forwards*: tred_left ep2 H21.
    *
    forwards*: principle_inf H10. rewrite H3 in *.
    inverts H20.
Qed.


Lemma dynamic_guarantee_dir_test: forall e1 e2 e1' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e1 (e_exp e1') ->
 exists e2', steps e2 (e_exp e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  - forwards*: Typing_chk typ1. inverts H. 
    forwards*: Typing_chk typ2. inverts H.
    forwards*: dynamic_guarantee_chk H0 H1.
  - forwards*: dynamic_guarantee_chk typ1 typ2.
Qed.


Lemma dynamic_guarantees: forall e1 e2 dir m1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value m1 ->
 steps e1 (e_exp m1) ->
 exists m2, value m2 /\ steps e2 (e_exp m2) /\ epre m1 m2.
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
  - forwards*: dynamic_guarantee_dir_test ep typ1 typ2 H.
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

