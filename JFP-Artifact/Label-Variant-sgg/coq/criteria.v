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
  - destruct (x == x0); eauto.
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
   forwards*: IHep1 H3 H4.
   forwards*: dmatch_tpre2 H6 H9.
    inverts* H0.
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
  + inverts typ;try solve[inverts H3]. inverts H4.
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, A1) :: E1) ((x, t_dyn) :: E2));eauto.
    pick fresh x and apply Typ_abs;auto.
    assert(cpre ((x, A1) :: E1) ((x, C) :: E2));eauto.
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
  + inverts typ. inverts H.
    forwards*: Typing_chk H6. inverts H.
    forwards*: IHep1.
    inverts H. inverts H4.
    forwards*: IHep2.
    forwards*: precise_type ep1 H6 H3.
    forwards*: dmatch_tpre H H9.
    inverts H7. inverts H8. inverts H11; try solve[inverts H7].
    inverts* H7.
    forwards*: IHep2 H10 H13.
    forwards*: epre_sim H0 H15 tp.
  + inverts typ. inverts H.
    forwards*: IHep1 H10 t_int.
    forwards*: IHep2 H11 t_int.
    assert(tpre t_int t_int);auto.
    forwards*: epre_sim H0 H3 tp.
  + inverts typ. inverts H0.
    forwards*: IHep H9 H.
    forwards*: epre_sim H1 H tp.
    forwards*: Typing_chk H11. inverts H0.
    forwards*: IHep H3.
    inverts* H0.
    inverts* ep;inverts H9.
    forwards: cpre_uniq cp;auto.
    rewrite_env(E2++[]) in H0.
    forwards*: Typing_weakening H4 H0. simpl_env in *.
    inverts H9.
    inverts ep. inverts H18. 
    forwards*: epre_sim H1 H tp.
    inverts H17.
    inverts* H7.
    inverts H.
    inverts* H7. 
    destruct(sim_decidable (t_arrow C0 D) (t_arrow C1 D0) ).
    inverts* H7.
    forwards*: Typing_regular_1 H7.
    inverts H14.
    eapply Typ_sim;eauto.
    apply Typ_save with (C:= (t_arrow C0 D));eauto.
    inverts* H4.
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
  forwards*: Typing_chk Typ1.
  inverts H.
  forwards*: SGG_chk ep. inverts H. inverts H1.
  inverts* H. inverts* ep. 
  forwards*: tpre_chk H0.
  inverts* H. inverts* H8.
  inverts Typ1.
  exists* (t_arrow t_dyn t_dyn).
  inverts H7.
  forwards*: precise_type Typ1 H1.
  -
  forwards*: SGG_chk ep Typ1.
Qed.


Lemma val_prel: forall e1 e2 t,
  Typing nil e1 Chk t ->
  epre e1 e2 ->
  value e1 ->
  exists e2', e2 ->* (Expr e2') /\ value e2' /\ epre e1 e2'.
Proof.
  introv Typ ep val1. gen e2 t.
  inductions val1; intros; eauto.
  - inverts* ep. inverts* H5.
  - inverts* ep. 
    forwards*:  epre_lc H6.
    inverts H6. inverts H0.
    inverts H9. 
    inverts* H8.
    inverts Typ.
    destruct B0; try solve[inverts* H2; inverts* H0].
    inverts H5. inverts H0. inverts* H11. inverts H0. inverts H5.
    inverts H15.
    exists* (e_anno (e_anno (e_abs e0) l4 b4 (t_arrow t_dyn t_dyn)) l3 b3 (t_arrow B0_1 B0_2)).
    splits*.
    eapply star_trans.
    apply star_one.
    apply Step_anno;eauto.
    unfold not; intros nt; inverts* nt.
    apply star_one.
    apply Step_annov;eauto.
    exists* (e_anno (e_anno (e_abs e0) l4 b4 (t_arrow t_dyn t_dyn)) l3 b3 t_dyn).
    splits*.
    eapply star_trans.
    apply star_one.
    apply Step_anno;eauto.
    unfold not; intros nt; inverts* nt.
    apply star_one.
    apply Step_annov;eauto.

   inverts Typ.
    destruct B0; try solve[inverts* H2; inverts* H0].
    inverts H5. inverts H0. inverts* H13. inverts H0. inverts H5.
    inverts H17.
    exists*.
    exists*.
Qed.



Lemma anno_chk: forall e t1 t2 l b ,
 [] ⊢ e_anno e l b t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
  forwards*: Typing_chk H7. 
Qed.



Lemma ano_ano_epre: forall e t e2 l1 b1 ,
 epre (e_anno e l1 b1 t) e2 ->
 exists e3 t2 l2 b2, e2 = (e_anno e3 l2 b2 t2) /\ epre e e3 /\ tpre t t2.
Proof.
  introv ep.
  inverts* ep.
  exists*.
Qed.


Lemma tdynamic_guarantee: forall e1 e2 e1' A B A1 B1 l1 b1 l2 b2,
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 value e2 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 l1 b1 A (Expr e1') ->
 exists e2', TypedReduce e2 l2 b2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val1 val2 typ1 typ2 red. gen l2 b2 e2 B A1 B1.
  inductions red; intros; eauto.
  -
    inverts val1. inverts ep.
    +
    inverts H8;simpl in *.
    assert(tpre t_int t_int);auto.
    forwards*: epre_sim H1 H2 tp.
    +
    inverts ep. inverts* H9;try solve[inverts* val2].
    inverts* H11. inverts* H10;try solve[inverts* val2].
    inverts val2.
    simpl in *.
    assert(tpre (t_arrow A0 B2) (t_arrow C D));auto.
    forwards*: epre_sim H1 H2 tp.
    inverts* H7.
    exists*.
    exists*.
  -
   inverts val1. inverts ep.
   inverts* H6;try solve[inverts* val2].
   inverts* H8. inverts* H7;try solve[inverts* val2].
   inverts val2. 
   inverts* tp.
   exists*.
   exists* (e_anno (e_anno (e_abs e0) l6 b6 (t_arrow C0 D0)) l3 b3 (t_arrow C1 D1)).
   splits*.
   apply ep_anno;eauto.
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



Lemma typlist_guarantee2: forall e1 e2 e2' e1' t1 t2 A1 A2 A3 A4 B1 B2 B3 B4 v' l0 b0 l1 b1 l3 b3 l4 b4 l5 b5 l6 b6,
 value e2' ->
 value e2 ->
 lc_exp (e_abs e1) ->
 Typing nil e2 Chk t1  ->
 Typing nil e2' Chk t2 ->
 epre (e_abs e1) (e_abs e1') -> 
 tpre (t_arrow A1 A2) (t_arrow B1 B2) ->
 tpre (t_arrow A3 A4) (t_arrow B3 B4) ->
 epre e2 e2' ->
 TypeLists e2 [t_typs A3 l1 (negb b1);t_typs A1 l3 (negb b3) ] (Expr v') ->
 exists e2'0,
 e_app (e_anno (e_anno (e_abs e1') l4 b4 (t_arrow B1 B2)) l5 b5 (t_arrow B3 B4)) l6 b6 e2' ->* Expr e2'0 /\ epre (e_anno (e_anno (e_anno (e1 ^^ v') l0 b0 A2) l3 b3 t_dyn) l3 b3 A4) e2'0.
Proof.
  introv val1 val2 lc typ1 typ2 ep1 tp1 tp2. intros ep2 tlist.
  inverts tlist. inverts H7; try solve[inverts H10].
  forwards*:  TypedReduce_prv_value H6.
  forwards*: TypedReduce_preservation H6.
  forwards*: TypedReduce_nlam H6. 
  forwards*:  TypedReduce_prv_value H8.
  forwards*: TypedReduce_preservation H8. 
  forwards*: value_lc H3.
  inverts tp1. inverts tp2.
  forwards*: tdynamic_guarantee ep2 H13 H6. inverts H9. inverts H10.
  forwards*:  TypedReduce_prv_value H9. forwards*: value_lc H10. 
  forwards*: TypedReduce_preservation H9.
  forwards*: TypedReduce_nlam H9. 
  forwards*: tdynamic_guarantee H11 H12. inverts H19. inverts H20.
  forwards*:  TypedReduce_prv_value H19. forwards*: value_lc H20.
  forwards*: epre_lc ep2.
  assert(epre (e_abs e1) (e_abs e1')); eauto.
  forwards*: epre_lc H24.
  inverts ep1.
  exists. split. 
  apply star_one. apply Step_beta; eauto. 
  apply ep_anno; eauto.  apply ep_anno; eauto. apply ep_anno; eauto. 
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
      forwards*: Typing_chk H11. inverts H.
      forwards*: Typing_chk H10. inverts H.
      forwards*: IHep1 H7. inverts H. inverts H8.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      *
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H15. inverts H. inverts H4.
      inverts H1. inverts H8.
      forwards*: Typing_chk H11. inverts H4.
      forwards*: val_prel ep1. 
      inverts H4. inverts H9. inverts H12.
      forwards*: Typing_regular_1 H17.
      exists(e_app x1 l2 b2 x). split. 
      apply star_trans with (b:=e_app x1 l2 b2 e2').
      apply multi_red_app2;auto.
      apply multi_red_app;auto.
      unfold simpl_fill. eauto.
      forwards*: epre_lc ep1.
      inverts ep1.
      exists(e_app (e_abs e0) l2 b2 x). splits.
      apply multi_red_app;auto.
      unfold simpl_fill. eauto.
    + 
      forwards*: epre_lc ep2.
      inverts ep2.
      inverts H6.
      *
      inverts typ1. inverts H3. forwards: Typing_chk H11. inverts H3.
      forwards*: val_prel ep1. inverts H3. inverts H8. inverts H9.
      inverts H0;inverts H5; simpl in *;
      try solve[inverts H0; inverts H11; try solve[inverts H19]; 
      try solve[inverts H17; inverts H0; inverts H5]].
      subst.
      inverts H10. inverts H18. inverts H19.
      inverts H16; try solve[inverts H8].
      inverts* H17.
      --
      forwards*: multi_red_app2 l2 b2 H H3.
      exists (
       e_app (e_anno (e_anno (e_abs e3) l6 b6 (t_arrow C D)) 
       l5 b5 (t_arrow t_dyn t_dyn)) l2 b2 (e_anno (e_abs e2) l2 (negb b2) t_dyn)).
      forwards: value_lc H8.
      inverts H10. inverts H16.
      splits.
      eapply star_trans.
      apply H0.
      eapply star_trans.
      apply star_one.
      apply Step_dyn;eauto.
      eapply star_trans.
      rewrite sfill_appl.
      apply star_one;eauto.
      simpl in *.
      apply star_one;eauto.
      eapply Step_absr;eauto.
      simpl;eauto.
      apply ep_app;eauto.
      apply ep_anno;eauto.
      --
      forwards*: multi_red_app2 l2 b2 H H3. 
      exists((e_app (e_anno (e_anno (e_abs e3) l6 b6 (t_arrow C D)) l5 b5 (t_arrow C0 D0))
      l2 b2 (e_anno (e_abs e2) l2 (negb b2) C0))).
      splits.
      eapply star_trans.
      apply H0.
      apply star_one; eauto.
      eapply  Step_absr;eauto.
      simpl;eauto.
      apply ep_app;eauto.
      apply ep_anno;eauto.
      *
      forwards*: epre_lc ep1.
      inverts ep1. inverts* H5.
      assert(principal_type (e_abs e3) = (t_arrow t_dyn t_dyn));eauto.
      exists((e_app (e_abs e3) l2 b2 (e_anno (e_abs e2) l2 (negb b2) t_dyn))).
      splits*.
    + 
      inverts typ1. inverts typ2.  inverts H. inverts H3.
      inverts H12. inverts H15. 
      forwards*: val_prel ep2. inverts H. inverts H3. inverts H9.
      forwards*: epre_lc ep1. 
      inverts ep1.
      inverts H11.
      forwards*: multi_red_app (e_abs e0) l2 b2 H.
      forwards*: preservation_multi_step H.
      forwards*: tdynamic_guarantee l2 b2 H10 H6. 
      inverts H14. inverts H19.
      exists (e_anno (e0 ^^ x0) ignore true t_dyn). split*.
      pick fresh xx.
      assert((e0 ^^ x0  = [xx ~> x0] (e0 ^ xx))).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H19.
      forwards*: TypedReduce_prv_value H14.
      forwards*: TypedReduce_prv_value H14.
      forwards*: value_lc H21.
      forwards*: epre_lc2 H20.
      forwards*: H13.
      forwards*: epre_open H25 H20.
    +
      inverts typ2. inverts H.
      inverts typ1. inverts H.
      forwards*: Typing_regular_1 H13.
      forwards*: val_prel ep1. 
      inverts H7. inverts H8. inverts H10.
      forwards*: val_prel ep2. 
      inverts H10. inverts H15. inverts H16.
      inverts H11. inverts H25. inverts H26.
      inverts H23; try solve[inverts* H8].
      forwards*: TypeLists_prv_value H6.
      forwards*: preservation_multi_step H10.
      inverts H24.
      *
      assert(tpre (t_arrow A1 B1) (t_arrow C D));auto.
      assert(tpre (t_arrow A2 B2) (t_arrow t_dyn t_dyn));auto.
      assert(e_app (e_anno (e_anno (e_abs e0) l6 b6 (t_arrow C D)) l5 b5 t_dyn) l2 b2 x0 ->*
      (Expr (e_app (e_anno (e_anno (e_abs e0) l6 b6 (t_arrow C D)) l5 b5 (t_arrow t_dyn t_dyn)) l2 b2 x0))).
      forwards*: value_lc H15.
      eapply star_trans.
      apply star_one;eauto.
      apply star_one;eauto.
      rewrite sfill_appl. rewrite sfill_appl.
      apply do_step;eauto.
      forwards*: typlist_guarantee2 H22 H23 H19 H6.
      inverts H26. inverts* H27.
      forwards*: multi_red_app2 H H7.
      forwards*: multi_red_app (e_anno (e_anno (e_abs e0) l6 b6 (t_arrow C D)) l5 b5 t_dyn) H10.
      exists x. splits*.
      *
      assert(tpre (t_arrow A1 B1) (t_arrow C D));auto.
      assert(tpre (t_arrow A2 B2) (t_arrow C0 D0));auto.
      assert(A5=(t_arrow A2 B2)). inverts* H14.
      subst. inverts H17.
      forwards*: typlist_guarantee2 H22 H23 H19 H6.
      inverts H17. inverts H24.
      forwards*: multi_red_app2 H H7.
      forwards*: multi_red_app (e_anno (e_anno (e_abs e0) l6 b6 (t_arrow C D)) l5 b5 (t_arrow C0 D0)) H10.
    +
      forwards*: value_lc H5.
      forwards*: epre_lc ep1.
      inverts typ1. inverts H2.
      forwards*: Typing_chk H10. inverts H2.
      forwards*: val_prel ep1.
      inverts H2. inverts H7. inverts H8.
      inverts H9. inverts* H17.
      forwards*: Typing_regular_1 H14.
      forwards*: epre_lc ep2.
      forwards*: multi_red_app2 l2 b2 H9 H2.
      inverts H1.
      forwards*: val_prel ep2. inverts H1. inverts H15. inverts H16.
      assert(walue (e_anno e0 l4 b4 t_dyn));auto.
      forwards*: multi_red_app l2 b2 H16 H1.
      exists((e_app (e_anno (e_anno e0 l4 b4 t_dyn) l4 b4 (t_arrow t_dyn t_dyn)) l2 b2 x0)).
      splits*.
      eapply star_trans;eauto.
      inverts ep2.
      exists((e_app (e_anno (e_anno e0 l4 b4 t_dyn) l4 b4 (t_arrow t_dyn t_dyn)) l2 b2 (e_abs e3))).
      splits*.
      eapply ep_app;eauto.
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep1 H2. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_add2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H2. inverts H. inverts H4.
      inverts H1.
      forwards*: val_prel ep1.
      inverts H1. inverts H4. inverts H9.
      forwards*: Typing_regular_1 H17.
      assert(e_add e1' l3 b3 e2' l4 b4 ->* Expr (e_add x0 l3 b3 e2' l4 b4)).
      apply multi_red_add2;eauto.
      assert(e_add x0 l3 b3 e2' l4 b4 ->* Expr (e_add x0 l3 b3 x l4 b4)).
      apply multi_red_add;eauto.
      exists((e_add x0 l3 b3 x l4 b4)). split*. 
      unfold simpl_fill. eauto.
    + 
      inverts typ2. inverts ep1. inverts ep2.
      inverts H8. inverts H10.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
  -  inverts* red.
    + 
      inverts ep. 
      assert(epre (e_abs e) (e_abs e0)); eauto.
      forwards*: epre_lc H0.
      inverts typ2. inverts H. inverts H4.
      exists* ((e_anno (e_anno (e_abs e0) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 t_dyn)).
    + forwards*: epre_lc ep.
      inverts ep. inverts* H.
      exists(e_anno (e_anno (e_abs e0) l2 b2  (t_arrow t_dyn t_dyn)) l2 b2 t_dyn).
      splits*.
      exists(e_anno (e_anno (e_abs e0) l2 b2 (t_arrow C D)) l2 b2 (t_arrow C D)).
      splits*.
      apply ep_anno;eauto. 
    +
      destruct E; unfold simpl_fill in H0; inverts H0.
    +
      forwards*: Typing_regular_1 typ2. inverts H0. 
      forwards*: Typing_regular_1 typ1. inverts H0. 
      destruct(value_decidable (e_anno e2 l2 b2 B)); eauto.
      * inverts H0; try solve [inverts ep;exfalso; apply H6; eauto];
        try solve [exfalso; apply H6; eauto].
        inverts ep. inverts H11. inverts H8. inverts H4.
        exfalso; apply H6; eauto.
      *
       inverts typ1. inverts typ2. 
       forwards*: anno_chk H1. inverts H11.
       forwards*: anno_chk H8. inverts H11.
       forwards*: IHep H2. inverts H11. inverts H14.
       forwards*: multi_red_anno H11.
    + 
      inverts typ1. inverts typ2.
      forwards*: anno_chk H0. inverts H8. 
      forwards*: anno_chk H3. inverts H8.
      forwards*: val_prel ep. inverts H8. inverts H11. inverts H12.
      forwards*: value_lc H5.
      forwards*: epre_lc ep.
      assert(not (value (e_anno e2 l2 b2 B))).
      unfold not; intros nt; inverts* nt; try solve[
        inverts ep; try solve[inverts* H5];
        try solve[inverts* H22;inverts* H19;inverts* H5]
      ].
      forwards*: preservation_multi_step H8.
      forwards*: multi_red_anno B H8.
      forwards*: tdynamic_guarantee l2 b2 H13 H H6. 
      inverts H18. inverts H19.
      exists* (x2).
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
  - 
    inverts val.
    destruct dir.
    forwards*: Typing_chk typ1. inverts H0.
    forwards*: val_prel ep.
    inverts H0. inverts H2. inverts* H3.
    forwards*: val_prel ep.
    inverts H0. inverts H1. inverts* H2.
    inverts* ep.
    exists*.
    assert(epre (e_abs e) (e_abs e0)); eauto.
    forwards*: epre_lc H0.
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

