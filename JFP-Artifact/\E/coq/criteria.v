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

Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. gen e2.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.

Lemma epre_lc2: forall e1 e2,
 epre e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. gen e1.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
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
  - inverts* tp1. inverts* tp2. 
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


Lemma dmatch_pro_tpre: forall t1 t2 t3,
 tpre t1 t2 ->
 pattern_pro t1 t3 ->
 exists t4, pattern_pro t2 t4 /\
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


Lemma dmatch_pro_tpre2: forall t1 t2 t3 t4,
 tpre t1 t2 ->
 pattern_pro t1 t3 ->
 pattern_pro t2 t4 ->
 tpre t3 t4.
Proof.
  introv tp dm1 dm2. gen t3 t4.
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm1; inverts* dm2].
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
   forwards*: IHep1 H1 H2.
   forwards*: dmatch_tpre2 H3 H6.
    inverts* H0.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   forwards*: dmatch_pro_tpre2 H2 H4.
   inverts* H3.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   forwards*: dmatch_pro_tpre2 H2 H4.
   inverts* H3.
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
  + inverts typ;try solve[inverts H1]. inverts H4.
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, A1) :: E1) ((x, t_dyn) :: E2));eauto.
    pick fresh x and apply Typ_abs;auto.
    assert(cpre ((x, A1) :: E1) ((x, C) :: E2));eauto.
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
    forwards*: abs_nlam.
  + 
    inverts typ. inverts H.
    forwards*: Typing_chk H4. inverts H.
    forwards*: IHep1.
    inverts H; try solve[inverts ep1;inverts H5].
    *
    inverts H5. inverts ep1. inverts H4. inverts H6.
    forwards*: IHep2 H7.
    *
    forwards*: IHep2.
    forwards*: precise_type ep1 H4 H3.
    forwards*: dmatch_tpre H9 H6.
    inverts H10. inverts H11. inverts H12; try solve[inverts H10].
    forwards*: IHep2 H7 H14.
    forwards*: epre_sim H0 H16 tp.
  + inverts typ. inverts H.
    forwards*: IHep1 H5 t_int.
    forwards*: IHep2 H6 t_int.
    assert(tpre t_int t_int);auto.
    forwards*: epre_sim H0 H3 tp.
  + inverts typ. inverts H0.
    forwards*: IHep H5 H.
    forwards*: epre_sim H1 H tp.
  +
    inverts typ. inverts H.
    forwards* h1: Typing_chk H5. inverts h1.
    forwards*: IHep1.
    forwards* h2: Typing_chk H6. inverts h2.
    forwards*: IHep2.
    inverts H2; try solve[inverts ep1; inverts H4].
    *
    inverts H8. 
    inverts H4; try solve[inverts ep2; inverts H5].
    inverts H8.
    --
    inverts ep1. inverts ep2. inverts H5. inverts H6.
    assert(tpre (t_pro ((t_arrow t_dyn t_dyn)) (t_arrow t_dyn t_dyn)) (t_pro (t_arrow t_dyn t_dyn) (t_arrow t_dyn t_dyn))); auto.
    forwards*: epre_sim H0 H4 tp.
    --
    inverts ep1. inverts H5.
    forwards*: precise_type ep2 H6 H2.
    assert(tpre (t_pro ((t_arrow t_dyn t_dyn)) A2) (t_pro (t_arrow t_dyn t_dyn) A)); auto.
    forwards*: epre_sim H0 H5 tp.
    *
    inverts H4; try solve[inverts ep2; inverts H5].
    inverts H10. inverts ep2. inverts H6.
    forwards*: precise_type ep1 H5 H7.
    assert(tpre (t_pro A1 (t_arrow t_dyn t_dyn)) (t_pro A (t_arrow t_dyn t_dyn))); auto.
    forwards*: epre_sim H0 H6 tp.
    forwards*: precise_type ep1 H5 H7.
    forwards*: precise_type ep2 H6 H2.
    assert(tpre (t_pro A1 A2) (t_pro A A0)); auto.
    forwards*: epre_sim H0 H13 tp.
  +
    inverts typ. inverts H.
    forwards*: Typing_chk H3. inverts H.
    forwards*: IHep.
    inverts H; try solve[inverts ep; inverts H2].
    *
    inverts ep.
    inverts H3. inverts H5.
    *
    forwards*: precise_type ep H3 H4.
    forwards* h1: dmatch_pro_tpre H H5.
    inverts h1. inverts H8. inverts H10; try solve[inverts H9].
    forwards*: epre_sim H0 H12 tp.
  +
    inverts typ. inverts H.
    forwards*: Typing_chk H3. inverts H.
    forwards*: IHep.
    inverts H; try solve[inverts ep; inverts H2].
    *
    inverts ep.
    inverts H3. inverts H5.
    *
    forwards*: precise_type ep H3 H4.
    forwards* h1: dmatch_pro_tpre H H5.
    inverts h1. inverts H8. inverts H10; try solve[inverts H9].
    forwards*: epre_sim H0 H14 tp.
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
  introv ep Typ1 cp. gen E1 E2 T dir.
  lets ep':ep.
  inductions ep;intros;
  try solve[destruct dir;
  try solve[forwards*: Typing_chk Typ1;
  inverts H;
  forwards*: SGG_chk ep'; inverts H; inverts H1;
  inverts* H;
  forwards*: precise_type Typ1 H1];
  try solve[ forwards*: SGG_chk ep']].
  -
  destruct dir.
  +
  inverts Typ1.
  exists. splits.
  pick fresh x and apply Typ_sugar;eauto.
  assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
  forwards* h1: H0 H1.
  inverts h1. inverts H2. inverts* H5. eauto.
  +
  forwards*: SGG_chk ep'.
  -
  destruct dir.
  +
  forwards*: Typing_chk Typ1.
  inverts H0.
  forwards*: SGG_chk ep'. inverts H0. inverts H2.
  inverts* H0.
  forwards*: precise_type Typ1 H2.
  +
  forwards*: SGG_chk ep'.
Qed.





Lemma ssval_prel: forall e1 e2,
  epre e1 e2 ->
  ssval e1 ->
  ssvalue e2.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  -
  inverts val.
  forwards*: epre_lc ep.
  inductions ep; eauto.
  inverts* H.
Qed.



Lemma ssval_pre: forall e1 e2,
  epre e1 e2 ->
  ssval e2 ->
  ssval e1.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  -
  inverts val.
  forwards*: epre_lc2 ep.
  inductions ep; eauto.
  inverts* H.
Qed.


Lemma val_pre: forall e1 e2,
  epre e1 e2 ->
  value e2 ->
  value e1.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  -
  inverts val.
  forwards*: ssval_pre ep.
Qed.




Lemma epre_principal_type: forall e1 e2,
 ssval e1 ->
 epre e1 e2 ->
 tpre (principal_type e1) (principal_type e2).
Proof.
  introv sval ep.
  inductions ep; simpl;eauto.
  inverts* sval.
Qed.


Lemma ssval_one: forall e,
 ssval e ->
 e ->* (Expr (e_anno e (principal_type e))).
Proof.
  introv sval.
  inductions sval; simpl;eauto.
  eapply star_trans.
  eapply multi_red_pro2.
  auto. apply IHsval1.
  eapply star_trans.
  eapply multi_red_pro.
  auto. apply IHsval2.
  eapply star_one; eauto.
Qed.



Lemma ssvalue_ep: forall e1 e2 t,
  Typing nil e1 Chk t ->
  epre e1 e2 ->
  ssval e1 ->
  ssval e2 \/ (exists e2', e2 ->* (Expr e2') /\ value e2' /\ epre (e_anno e1 (principal_type e1)) e2').
Proof.
  introv typ ep sval. gen t.
  inductions ep; intros;try solve[inverts sval]; eauto.
  -
  inverts* sval.
  forwards*: epre_lc ep.
  inverts* ep.
  inverts* H.
  right. exists.
  splits.
  eapply star_one.
  eapply Step_absd; eauto.
  eapply value_pro; eauto.
  eapply ep_anno; simpl; eauto.
  -
  inverts sval. inverts typ. inverts H.
  forwards* h1: Typing_chk H7. inverts h1.
  forwards* h2: Typing_chk H8. inverts h2.
  forwards*: IHep1. forwards*: IHep2.
  inverts H5;inverts* H6; simpl in *.
  +
  lets(ee2'&rred1&vval1&epp1): H5.
  inverts vval1. inverts epp1.
  forwards* rred2: ssval_one H9.
  forwards* lc2:  epre_lc ep2.
  forwards* ep1': epre_principal_type ep1.
  right. exists. splits.
  eapply star_trans.
  eapply multi_red_pro2.
  auto. apply rred2.
  eapply star_trans.
  eapply multi_red_pro.
  auto. apply rred1.
  eapply star_one; eauto.
  eapply value_pro; eauto.
  apply ep_anno; eauto.
  +
  lets(ee2'&rred1&vval1&epp1): H9.
  inverts vval1. inverts epp1.
  forwards* rred2: ssval_one H5.
  forwards* lc2:  epre_lc ep2.
  forwards* ep1': epre_principal_type ep2.
  right. exists. splits.
  eapply star_trans.
  eapply multi_red_pro2.
  auto. apply rred1.
  eapply star_trans.
  eapply multi_red_pro.
  auto. apply rred2.
  eapply star_one; eauto.
  eapply value_pro; eauto.
  apply ep_anno; eauto.
  +
  lets(ee2'&rred1&vval1&epp1): H5.
  inverts vval1. inverts epp1.
  lets(ee1'&rred2&vval2&epp2): H9.
  inverts vval2. inverts epp2.
  forwards*: epre_lc ep2.
  right. exists. splits.
  eapply star_trans.
  eapply multi_red_pro2.
  auto.
  apply rred2.
  eapply star_trans.
  eapply multi_red_pro.
  auto.
  apply rred1.
  eapply star_one.
  eapply Step_pro; eauto.
  eapply value_pro; eauto.
  eapply ep_anno; eauto.
Qed.



Lemma vval_prel: forall e1 e2 t,
  Typing nil e1 Chk t ->
  epre e1 e2 ->
  value e1 ->
  value e2 \/ (exists e2', e2 ->* (Expr e2') /\ value e2' /\ epre e1 e2').
Proof.
  introv typ ep val1. gen t.
  inductions ep; intros; try solve[inverts* val1];eauto.
  inverts val1.
  inverts typ. inverts H0.
  forwards*: ssvalue_ep ep H1.
  inverts* H0.
  inverts* H4.
  inverts H0. inverts H5.
  inverts H0.
  inverts H7.
  forwards*: epre_lc ep.
  destruct(value_decidable (e_anno e2 B)); auto.  
  inverts H6; try solve[inverts H1].
  forwards*: principle_inf H8.
  rewrite <- H6 in *.
  forwards*: epre_principal_type H12.
  forwards*: epre_sim H9 H13 H.
  right. exists.
  splits.
  eapply star_trans.
  eapply multi_red_anno; auto.
  apply H4.
  eapply star_one.
  eapply Step_annov; eauto.
  eapply value_pro; eauto.
  eapply ep_anno; eauto.
Qed.


Lemma val_prel: forall e1 e2 t,
  Typing nil e1 Chk t ->
  epre e1 e2 ->
  walue e1 ->
  walue e2 \/ (exists e2', e2 ->* (Expr e2') /\ walue e2' /\ epre e1 e2').
Proof.
  introv typ ep val1. 
  inverts val1.
  -
  forwards*: vval_prel H. inverts* H0.
  inverts* H1. 
  -
  forwards*: epre_lc ep.
  inverts* ep.
Qed.



Lemma anno_chk: forall e t1 t2,
 [] ⊢ e_anno e t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.




Lemma ano_ano_epre: forall e t e2,
 epre (e_anno e t) e2 ->
 exists e3 t2, e2 = (e_anno e3 t2) /\ epre e e3 /\ tpre t t2.
Proof.
  introv ep.
  inverts* ep.
Qed.




Lemma tdynamic_guarantee: forall e1 e2 e1' A B A1 B1,
 epre e1 e2 ->  
 tpre A B ->
 walue e1 ->
 walue e2 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 A (Expr e1') ->
 exists e2', TypedReduce e2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen e2 B A1 B1.
  inductions red; intros; eauto.
  inverts val1. inverts ep.
  inverts val2. inverts H3.
  forwards*: epre_principal_type H7.
  forwards*: epre_sim H1 H3 tp.
  exists. splits*.
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




Lemma TypeLists_prv_value: forall v B A1 A2 v',
 value v -> Typing nil v Chk B ->
 TypeLists v (cons A2 (cons A1 nil)) (Expr v') 
     -> value v'.
Proof with auto.
  introv Val Typ Red.
  inductions Red; 
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  -
    inverts Red.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_prv_value H5.
    inverts H7.
Qed.




Lemma walue_lc : forall v,
    walue v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
Qed.

Hint Resolve walue_lc: core. 


Lemma typlist_guarantee2: forall e1 e2 e2' e1' A B A1 A2 A3 A4 B1 B2 B3 B4 v' t2,
 walue e2' ->
 walue e2 ->
 lc_exp (e_abs e1) ->
 Typing nil e2 Chk A ->
 Typing nil e2' Chk B ->
 epre (e_abs e1) (e_abs e1') -> 
 tpre (t_arrow A1 A2) (t_arrow B1 B2) ->
 tpre (t_arrow A3 A4) (t_arrow B3 B4) ->
 epre e2 e2' ->
 TypeLists e2 [A3; A1] (Expr v') ->
 pattern t2 (t_arrow B3 B4) ->
 exists e2'0,
 e_app (e_anno (e_anno (e_abs e1') (t_arrow B1 B2)) t2) e2' ->* Expr e2'0 /\ epre (e_anno (e_anno (e1 ^^ v') A2) A4) e2'0.
Proof.
  introv val1 val2 lc typ1 typ2 ep1 tp1 tp2. intros ep2 tlist pa2.
  inverts tlist. inverts H5; try solve[inverts H8].
  forwards*:  TypedReduce_prv_walue H3.
  forwards*: TypedReduce_preservation H3.
  forwards*: TypedReduce_nlam H3. 
  forwards*:  TypedReduce_prv_walue H6.
  forwards*: TypedReduce_preservation H6. 
  forwards*: Typing_regular_1 H7.
  inverts tp1. inverts tp2.
  forwards*: tdynamic_guarantee ep2 H13 H3. inverts H9. inverts H10.
  forwards*:  TypedReduce_prv_walue H9. 
  forwards*: walue_lc H10. 
  forwards*: TypedReduce_preservation H9.
  forwards*: TypedReduce_nlam H9. 
  forwards*: tdynamic_guarantee H11 H12. inverts H19. inverts H20.
  forwards*:  TypedReduce_prv_walue H19. forwards*: walue_lc H20.
  forwards*: epre_lc ep2.
  assert(epre (e_abs e1) (e_abs e1')); eauto.
  forwards*: epre_lc H24.
  inverts ep1.
  exists. split. 
  apply star_one. apply Step_beta with (A2:= B3); eauto. 
  apply ep_anno; eauto.  apply ep_anno; eauto. 
  pick fresh xx.
  assert((e1' ^^ x0) = [xx ~> x0] (e1' ^ xx)).
  rewrite (subst_exp_intro xx); eauto.
  rewrite (subst_exp_intro xx); eauto.
  rewrite H26.
  forwards*: H28 xx.
  forwards*: epre_open H27 H21. 
Qed.



Lemma dynamic_guarantee_chk_test: forall e1 e2 e1' T1 T2,
 epre e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 -> 
 step e1 (Expr e1') ->
 exists e2', e2 ->*(Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' T1 T2.
  inductions ep; intros;
  try solve[inverts* red;destruct E; unfold simpl_fill in H; inverts* H];
  try solve[inverts* red;destruct E; unfold simpl_fill in H1; inverts* H1]; eauto.
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      *
      inverts typ1. inverts typ2.
      inverts H. inverts H4.
      forwards*: Typing_chk H9. inverts H.
      forwards*: Typing_chk H8. inverts H.
      forwards*: IHep1 H2. inverts H. inverts H10.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H14.
      lets(vv1&rred1&epp1): H. 
      inverts H1. inverts H7; try solve[inverts H7].
      forwards* h1: Typing_chk H9. inverts h1.
      forwards*: val_prel ep1.
      inverts H7.
      --
      exists(e_app e1' vv1). split. 
      apply multi_red_app;auto.
      unfold simpl_fill. eauto.
      --
      lets(vv2&rred2&vval2&epp2): H10. 
      forwards*: Typing_regular_1 H12.
      forwards*: epre_lc ep2.
      exists(e_app vv2 vv1). split. 
      eapply star_trans.
      apply multi_red_app2;auto.
      apply rred2.
      apply multi_red_app.
      eauto.
      apply rred1.
      unfold simpl_fill. eauto.
      --
      forwards*: Typing_regular_1 H8.
      inverts ep1. 
      exists. splits.
      apply multi_red_app.
      eauto.
      apply rred1.
      simpl.
      eauto.     
    + 
      inverts typ1. inverts H.
      inverts typ2. inverts H.
      forwards*: epre_lc ep2.
      inverts ep2.
      forwards* h1: Typing_chk H7. inverts h1.
      forwards* h2: val_prel ep1.
      inverts h2.
      *
      forwards*: principle_inf3 H7.
      forwards*: precise_type H7 H12.
      forwards*: principle_inf3 H12.
      rewrite H16 in *.
      forwards* h3: pattern_abs_uniq H4 H9.
      inverts h3.
      forwards* h4: dmatch_tpre2 H9 H14.
      inverts h4. 
      exists. splits*.
      *
      lets (vv2&rred2&vval2&epp2): H13.
      forwards*: preservation_multi_step rred2.
      forwards*: principle_inf3 H7.
      forwards*: precise_type H7 H12.
      forwards*: principle_inf3 H16.
      rewrite H17 in *.
      forwards*: pattern_abs_uniq H4 H9.
      inverts H20.
      forwards* h1: dmatch_tpre2 H4 H14.
      inverts h1. 
      exists. splits.
      eapply star_trans.
      eapply multi_red_app2; eauto.
      eapply star_one.
      eapply Step_absr; eauto.
      eapply ep_app; eauto.
    + 
      inverts typ2. inverts H.
      inverts typ1. inverts H.
      forwards* ha: precise_type ep1.
      forwards* hb: dmatch_tpre2 H15 H10.
      forwards*: val_prel ep1.
      forwards*: val_prel ep2.
      inverts H.
      *
      inverts H9.
      --
      inverts ep1. inverts H19. inverts H8.
      lets ep': H21. inverts ep'.
      inverts H13.
      inverts H20. inverts H8.
      forwards* eq: pattern_abs_uniq H5 H15. inverts eq.
      inverts H12. inverts H8. inverts H20.
      forwards* he: typlist_guarantee2 H21 H18 hb  ep2 H10.
      --
      lets(vv2&rred2&vval2&epp2): H.
      forwards*: epre_lc ep2.
      forwards* hd: preservation_multi_step rred2.
      inverts H13.
      forwards* eq: pattern_abs_uniq H5 H15. inverts eq.
      inverts ep1. inverts H20. inverts H8.
      lets ep': H22. inverts ep'.
      inverts H12.
      inverts H8. inverts H14. 
      forwards* he: typlist_guarantee2  H22 H19 hb epp2 H10.
      lets(vv3&rred3&epp3):he.
      exists. splits.
      eapply star_trans.
      eapply multi_red_app.
      auto. apply rred2.
      apply rred3.
      auto.
      *
      inverts H9.
      --
      lets(vv1&rred1&vval1&epp1): H12.
      forwards*: epre_lc ep2.
      forwards* hd: preservation_multi_step rred1.
      inverts H13.
      forwards* eq: pattern_abs_uniq H5 H15. inverts eq.
      inverts epp1. inverts H20. 
      lets ep': H22. inverts ep'.
      inverts vval1.
      inverts H13. inverts H21. 
      forwards* he: typlist_guarantee2  H22 H19 hb ep2 H10.
      inverts hd.
      lets(vv3&rred3&epp3):he.
      exists. splits.
      eapply star_trans.
      eapply multi_red_app2.
      auto. apply rred1.
      apply rred3.
      auto.
      --
      lets(vv1&rred1&vval1&epp1): H12.
      lets(vv2&rred2&vval2&epp2): H.
      forwards*: epre_lc ep2.
      forwards* hc: preservation_multi_step  rred1.
      forwards* hd: preservation_multi_step rred2.
      inverts epp1.
      inverts H20.  lets epp': H22.
      inverts H22.
      inverts vval1. inverts H14. inverts hc.
      inverts H21. inverts H13. 
      forwards* eq: pattern_abs_uniq H5 H15. inverts eq.
      forwards* he: typlist_guarantee2  epp' H19 hb epp2 H10.
      lets(vv3&rred3&epp3):he.
      exists. splits.
      eapply star_trans.
      eapply multi_red_app2.
      auto. apply rred1.
      eapply star_trans.
      eapply multi_red_app.
      auto. apply rred2.
      eapply rred3.
      auto.
    +
     forwards*: epre_lc ep1.
     inverts ep1.
     inverts typ1. inverts H0.
     inverts typ2. inverts H0.
     forwards*: val_prel ep2.
     inverts H0.
     *
     inverts H14.
     inverts H16.
     forwards* h1: tdynamic_guarantee ep2 H4.
     lets(vv1&rred1&epp1):h1.
     forwards*: TypedReduce_prv_walue H4.
     forwards*: TypedReduce_prv_walue rred1.
     exists. splits.
     eapply star_one.
     eapply Step_nbeta;eauto.
     eapply ep_anno;eauto.
     pick fresh xx.
     assert((e0 ^^ vv1) = [xx ~> vv1] (e0 ^ xx)).
     rewrite (subst_exp_intro xx); eauto.
     rewrite (subst_exp_intro xx); eauto.
     rewrite H14.
     forwards*: H1 xx.
     forwards*: epre_open H16 epp1. 
     *
     inverts H9.
     inverts H11.
     lets(vv3&rred3&wal3&epp3):H10.
     forwards*: preservation_multi_step rred3.
     forwards* h1: tdynamic_guarantee epp3 H4.
     lets(vv1&rred1&epp1):h1.
     forwards*: TypedReduce_prv_walue H4.
     forwards*: TypedReduce_prv_walue rred1.
     exists. splits.
     eapply star_trans.
     apply multi_red_app.
     eauto.
     apply rred3.
     apply star_one.
     eapply Step_nbeta;eauto.
     eapply ep_anno;eauto.
     pick fresh xx.
     assert((e0 ^^ vv1) = [xx ~> vv1] (e0 ^ xx)).
     rewrite (subst_exp_intro xx); eauto.
     rewrite (subst_exp_intro xx); eauto.
     rewrite H13.
     forwards*: H1 xx.
     forwards*: epre_open H18 epp1. 
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep1 H2. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_add2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards* ha: IHep2 H2.
      inverts H1. 
      lets(vv1&rred1&epp1):ha.
      forwards*: val_prel ep1.
      inverts H. 
      --
      forwards*: Typing_regular_1 H10.
      inverts H1.
      exists. splits. 
      eapply multi_red_add.
      auto. apply rred1.
      unfold simpl_fill. eauto.
      inverts H9; try solve[forwards*: abs_nlam]. inverts H14.
      --
      lets(vv2&rred2&vval2&epp2):H1.
      forwards*: Typing_regular_1 H12.
      inverts vval2.
      exists. splits.
      eapply star_trans. 
      eapply multi_red_add2.
      auto. apply rred2.
      eapply multi_red_add.
      auto. apply rred1.
      unfold simpl_fill. eauto.
      inverts epp2.
      inverts H10; try solve[forwards*: abs_nlam]. inverts H16.
    + 
      inverts typ2. inverts ep1. inverts ep2.
      inverts H6. inverts H8.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
  -  inverts* red.
    + 
      inverts ep. 
      assert(epre (e_abs e) (e_abs e0)); eauto.
      forwards*: epre_lc H0.
      inverts typ2. inverts H. inverts H4.
      exists* ((e_anno (e_anno (e_abs e0) (t_arrow t_dyn t_dyn)) t_dyn)).
      forwards*: epre_lc H0.
      exists* ((e_anno (e_anno (e_abs e0) (t_arrow C D) ) (t_arrow C D) )).
    + 
      forwards*: epre_lc ep.
      inverts ep. inverts* H.
      exists(e_anno (e_anno (e_abs e0) (t_arrow t_dyn t_dyn)) t_dyn).
      splits*.
    +
      destruct E; unfold simpl_fill in H0; inverts H0.
    +
      forwards*: Typing_regular_1 typ2. inverts H0. 
      forwards*: Typing_regular_1 typ1. inverts H0. 
      destruct(value_decidable (e_anno e2 B)); eauto.
      * inverts H0; try solve [forwards*: ssval_pre ep;exfalso; apply H4; eauto];
        try solve [exfalso; apply H4; eauto].
      *
       inverts typ1. inverts typ2. 
       forwards* h1: anno_chk H1. inverts h1.
       forwards* h2: anno_chk H8. inverts h2.
       forwards*: IHep H3. inverts H13. inverts H14.
       forwards*: multi_red_anno H13.
    + 
      inverts typ1. inverts typ2.
      forwards* h1: anno_chk H0. inverts h1. 
      forwards* h2: anno_chk H5. inverts h2.
      forwards*: val_prel ep. inverts H10. 
      *
      forwards*: epre_lc ep.
      assert(not (value (e_anno e2 B))).
      unfold not; intros nt; inverts* nt.
      inverts H11; inverts* H3; try solve[inverts* H13;inverts H12].
      inverts* H13;inverts H12. inverts H13.
      forwards* ha: tdynamic_guarantee ep H H4.
      lets(vv1&rred1&epp1): ha. 
      exists. splits.
      eapply star_one; eauto.
      auto.
      *
      lets(vv1&rred1&vval1&epp1): H11. 
      forwards*: preservation_multi_step rred1.
      forwards* ha: tdynamic_guarantee epp1 H H4.
      lets(vv2&rred2&epp2): ha.
      forwards*: epre_lc ep.
      destruct(value_decidable (e_anno e2 B)); auto.
      --
      inverts H13.
      forwards*: ssval_pre ep.
      inverts H13; inverts H2; try solve[inverts* H13].
      inverts* H13. inverts H16.
      -- 
      exists. splits.
      eapply star_trans.
      eapply multi_red_anno.
      auto.
      eapply rred1. 
      eapply star_one; eauto.
      auto.
  -
    inverts red.
    +
    inverts typ1. inverts H.
    forwards*: val_prel ep1.
    forwards*: val_prel ep2.
    inverts H.
    *
      inverts* H4.
      --
      inverts H5. 
      ++ 
      inverts* H.
      inverts ep1; inverts* ep2.
      inverts H4. inverts H5.
      exists. splits*.
      inverts ep2.
      ++
      inverts ep1.
      --
      lets(vv2&rred2&vval2&epp2): H. 
      inverts epp2. inverts vval2.
      forwards*: epre_lc ep2.
      inverts ep2. inverts H4. 
      inverts ep1. inverts H5. inverts H4.
      exists. splits.
      eapply star_trans.
      eapply multi_red_pro.
      auto. apply rred2.
      eapply star_one.
      eapply Step_pro; auto.
      eapply ep_anno; eauto.
    *
      inverts* H4.
      --
      lets(vv2&rred2&vval2&epp2): H5. 
      inverts epp2. inverts H. inverts H4.
      inverts vval2. inverts H4.
      forwards*: epre_lc ep2.
      inverts ep2. 
      exists. splits.
      eapply star_trans.
      eapply multi_red_pro2.
      auto. apply rred2.
      eapply star_one.
      eapply Step_pro; auto.
      eapply ep_anno; eauto.
      inverts ep2.
      --
      lets(vv1&rred1&vval1&epp1): H5. 
      lets(vv2&rred2&vval2&epp2): H. 
      inverts vval1. inverts* vval2.
      inverts epp2. inverts epp1.
      inverts H4. inverts H6.
      forwards*: epre_lc ep2.
      exists. splits.
      eapply star_trans.
      eapply multi_red_pro2.
      auto. apply rred1.
      eapply star_trans.
      eapply multi_red_pro.
      auto. apply rred2.
      eapply star_one.
      eapply Step_pro; auto.
      eapply ep_anno; eauto.
      inverts epp2.
      inverts epp1.
    +
    destruct E; unfold simpl_fill; inverts H.
    *
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H7. inverts h1.
    forwards* h2: Typing_chk H11. inverts h2.
    forwards* ha: IHep1 H2.
    lets (vv1&rred1&epp1): ha.
    inverts H1.
    forwards*: epre_lc ep2.
    exists. splits.
    eapply multi_red_pro2; eauto.
    eapply ep_pro; eauto.
    *
    inverts typ1. inverts typ2. inverts H. inverts H4.
    forwards* h1: Typing_chk H11. inverts h1.
    forwards* h2: Typing_chk H12. inverts h2.
    forwards* ha: IHep2 H2.
    lets(vv1&rred1&epp1): ha.
    inverts H1.
    forwards* h3: Typing_chk H10. inverts h3.
    forwards* hb: val_prel ep1.
    inverts hb.
    --
    inverts H7.
    exists(e_pro e1' vv1). split. 
    apply multi_red_pro;auto.
    unfold simpl_fill. eauto.
    inverts ep1. inverts H8.
    --
    lets(vv2&rred2&vval2&epp2): H7. 
    forwards*: Typing_regular_1 H11.
    forwards*: epre_lc ep2.
    inverts vval2.
    exists(e_pro vv2 vv1). split. 
    eapply star_trans.
    apply multi_red_pro2;auto.
    apply rred2.
    apply multi_red_pro.
    eauto.
    apply rred1.
    unfold simpl_fill. eauto.
    inverts epp2. inverts H8.
   +
     forwards*: Typing_regular_1 typ2. inverts H.
     inverts ep1.
     exists. splits.
     apply star_one;eauto.
     eapply ep_pro;eauto.
     eapply ep_anno;eauto.
    +
    forwards*: Typing_regular_1 typ2. inverts H.
    inverts typ1. inverts H.
    forwards* h3: Typing_chk H9. inverts h3.
    forwards* h4: vval_prel ep1.
    inverts h4.
    inverts ep2.
    exists. splits.
    apply star_one;eauto.
    eapply ep_pro;eauto.
    lets(vv2&rred2&vval2&epp2): H6.
    inverts ep2.
    exists. split. 
    eapply star_trans.
    apply multi_red_pro2;auto.
    apply rred2.
    apply star_one;eauto.
     eapply ep_pro;eauto.
  -
    inverts red.
    +
    destruct E; unfold simpl_fill; inverts H.
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H5. inverts h1.
    forwards* h2: Typing_chk H9. inverts h2.
    forwards* ha: IHep H2.
    lets (vv1&rred1&epp1): ha.
    exists. splits.
    eapply multi_red_l; eauto.
    eapply ep_l; eauto.
    +
    lets typ1':typ1.
    inverts typ1. inverts H.
    forwards* ha: val_prel ep.
    inverts ha.
    *
    inverts H5. inverts typ2.
    inverts H4.
    forwards*: precise_type ep.
    forwards* hb: dmatch_pro_tpre2 H2 H12.
    inverts hb.
    inverts H; try solve[inverts ep].
    inverts H8.
    inverts ep. inverts H19.
    inverts H10. 
    exists. splits.
    eapply star_one;eauto. 
    eapply ep_anno;eauto.
    *
    lets (vv1&rred1&vval1&epp1): H.
    inverts vval1;inverts epp1.
    lets typ: H5.
    inverts H11. inverts H5.
    inverts typ2. inverts H5.
    forwards*: precise_type typ H14.
    forwards* h1: dmatch_pro_tpre2 H7 H16.
    inverts h1.
    forwards* ha: preservation_multi_step rred1.
    inverts ha.
    forwards* hb: pattern_pro_uniq H2 H7.
    inverts hb.
    exists. splits.
    eapply star_trans.
    eapply multi_red_l.
    eapply rred1.
    eapply star_one; auto.
    eapply Step_l; eauto.
    eapply ep_anno;eauto.
  -
    inverts red.
    +
    destruct E; unfold simpl_fill; inverts H.
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H5. inverts h1.
    forwards* h2: Typing_chk H9. inverts h2.
    forwards* ha: IHep H2.
    lets (vv1&rred1&epp1): ha.
    exists. splits.
    eapply multi_red_r; eauto.
    eapply ep_r; eauto.
    +
    lets typ1':typ1.
    inverts typ1. inverts H.
    forwards* ha: val_prel ep.
    inverts ha.
    *
    inverts H5. inverts typ2.
    inverts H4.
    forwards*: precise_type ep.
    forwards* hb: dmatch_pro_tpre2 H2 H12.
    inverts hb.
    inverts H; try solve[inverts ep].
    inverts H8.
    inverts ep. inverts H19.
    inverts H10. 
    exists. splits.
    eapply star_one;eauto. 
    eapply ep_anno;eauto.
    *
    lets (vv1&rred1&vval1&epp1): H.
    inverts vval1;inverts epp1.
    lets typ: H5.
    inverts H11. inverts H5.
    inverts typ2. inverts H5.
    forwards*: precise_type typ H14.
    forwards* h1: dmatch_pro_tpre2 H7 H16.
    inverts h1.
    forwards* ha: preservation_multi_step rred1.
    inverts ha.
    forwards* hb: pattern_pro_uniq H2 H7.
    inverts hb.
    exists. splits.
    eapply star_trans.
    eapply multi_red_r.
    eapply rred1.
    eapply star_one; auto.
    eapply Step_r; eauto.
    eapply ep_anno;eauto.
Qed.


Lemma dynamic_guarantee_dir_test: forall e1 e2 e1' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e1 (Expr e1') ->
 exists e2', e2 ->*(Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  - forwards*: Typing_chk typ1. inverts H. 
    forwards*: Typing_chk typ2. inverts H.
    forwards*: dynamic_guarantee_chk_test H0 H1.
  - forwards*: dynamic_guarantee_chk_test typ1 typ2.
Qed.


Lemma dynamic_guarantees_test: forall e1 e2 dir m1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 walue m1 ->
 e1 ->* (Expr m1) ->
 exists m2, walue m2 /\ e2 ->* (Expr m2) /\ epre m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  - inverts val.
    +
    destruct dir.
    *
    forwards*: Typing_chk typ1. inverts H1.
    forwards*: dynamic_guarantee_dir_test ep typ1 typ2 H.
    lets(vv1&rred1&epp1):H1.
    forwards*: preservation H2 H.
    forwards*: val_prel epp1.
    inverts* H4.
    lets(vv2&rred2&vval1&epp2):H5.
    exists*.
    *
    forwards*: dynamic_guarantee_dir_test ep typ1 typ2 H.
    lets(vv1&rred1&epp1):H1.
    forwards*: preservation typ1 H.
    forwards*: val_prel epp1.
    inverts* H3.
    lets(vv2&rred2&vval1&epp2):H4.
    exists*.
    +
    inverts* H.
    *
    destruct E; unfold simpl_fill;inverts* H1 .
    *
    inverts* H2.
  - forwards*: dynamic_guarantee_dir_test ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: preservation H.
    forwards*: preservation_multi_step H0.
    forwards*: IHred val H2 H1 H3.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    apply star_trans with (b := x).
    apply H0.
    apply H5. auto.
Qed.


