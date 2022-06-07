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

Theorem precise_type: forall e e' T T',
   epre e e' ->  
   Typing nil e Inf T ->
   Typing nil e' Inf T'->
   tpre T T'.
Proof.
    introv ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - forwards*: inference_unique Typ1 Typ2. subst.
      apply tpre_refl.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H2 H4.
      inverts* H.
Qed.


Lemma val_prel: forall e1 e2 dir B,
  Typing nil e2 dir B ->
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv typ2 ep vval1. gen e2 B.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto. 
  -
    inverts ep. inverts H4. inverts H6. inverts H3.
    inverts typ2. inverts H7. inverts H0.
    inverts H7. inverts H0. inverts H6.
    inverts H7. inverts H6. inverts H7.
    inverts H0. inverts H7. inverts H0. inverts H9.
    inverts H8. inverts H10. inverts H6. inverts H9. 
    assert(epre ((e_abs e)) ((e_abs e0))). eauto. 
    forwards*: epre_lc H0.
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


Lemma sval_ep_sval:forall e1 e2 dir  A,
 Typing nil e2 dir A ->
 sval e1 ->
 epre e1 e2 ->
 sval e2.
Proof.
  introv typ sval ep.
  inverts sval. inverts* ep.
  inverts H4. inverts* H2.
  inverts typ. inverts H6. inverts H3.  
  inverts H0. inverts H6. inverts H5.
  assert(epre (e_abs e) (e_abs e2)); eauto.
  forwards*: epre_lc H0. 
Qed.


Lemma ssval_ep_ssval:forall e1 e2 dir  A,
 Typing nil e2 dir A ->
 ssval e1 ->
 epre e1 e2 ->
 ssval e2.
Proof.
  introv typ sval ep.
  inverts sval. 
  forwards*: sval_ep_sval ep.
  inverts* H0.
  inverts* ep. 
Qed.


Lemma anno_chk: forall e t1 t2,
 [] ⊢ e_anno e t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
  forwards*: Typing_chk H4. 
Qed.


Lemma anno_anno: forall e e0 C C0 B0 A dir,
 Typing nil e0 dir A ->
 ssval e -> 
 sim (principal_type e) C ->
 tpre C B0 ->
 epre e e0 ->
 exists e2', TypedReduce (e_anno e0 C0) B0 (Expr e2') /\ epre (e_anno e C) e2'.
Proof.
  introv typ sval sim tp ep.
  forwards*: ssval_ep_ssval ep.
  inverts sval.
  -
   inverts ep. simpl in sim.
   inverts H5. inverts H. 
   inverts sim.
    + inverts* tp.
      exists*.
      assert(tpre (t_arrow C1 D) (t_arrow C D0)); eauto.
      forwards*: epre_sim H3 H.
      exists*.
    + inverts tp.
      exists*.
  -
    inverts ep. simpl in *.
    assert(tpre t_int t_int); eauto.
    forwards*: epre_sim sim H0 tp.
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
 value e1 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 A (Expr e1') ->
 exists e2', TypedReduce e2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val typ1 typ2 red. gen e2 B .
  inductions red; intros; eauto.
  - 
    forwards*: ano_ano_epre ep.
    lets(e3&t2&eq&ep1&tp1): H2. inverts eq.
    inverts typ2.
    forwards*: anno_chk H3. inverts H6. 
    forwards*: anno_anno tp ep1.
  -
   forwards*: ano_ano_epre ep.
    lets(e3&t2&eq&ep1&tp1): H0. inverts eq.
    inverts typ2.
    forwards*: anno_chk H1. inverts H4. 
    forwards*:sval_ep_sval ep1.
    inverts H4. inverts tp.
    exists*.
    exists*.
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



Lemma typlist_guarantee2: forall e1 e2 e2' e1' A1 A2 A3 A4 B1 B2 B3 B4 v',
 walue e2 ->
 lc_exp (e_abs e1) ->
 Typing nil e2 Chk A3 ->
 Typing nil e2' Chk B3 ->
 epre (e_abs e1) (e_abs e1') -> 
 tpre (t_arrow A1 A2) (t_arrow B1 B2) ->
 tpre (t_arrow A3 A4) (t_arrow B3 B4) ->
 epre e2 e2' ->
 TypeLists e2 [A3; A1] (Expr v') ->
 exists e2'0,
 e_app (e_anno (e_anno (e_abs e1') (t_arrow B1 B2)) (t_arrow B3 B4)) e2' ->* Expr e2'0 /\ epre (e_anno (e_anno (e_anno (e1 ^^ v') A2) t_dyn) A4) e2'0.
Proof.
  introv val lc typ1 typ2 ep1 tp1 tp2. intros ep2 tlist.
  inverts val.
  +
  forwards*: val_prel ep2.
  inverts tlist. 
  * inverts H7;try solve[inverts H10].
  inverts tp1. inverts tp2. 
  inverts ep1.
  forwards*:  TypedReduce_prv_value H5.
  forwards*: TypedReduce_preservation H5.
  forwards*: TypedReduce_nlam H5. 
  forwards*:  TypedReduce_prv_value H8.
  forwards*: TypedReduce_preservation H8. 
    forwards*: value_lc H13.
  forwards*: tdynamic_guarantee ep2 H9 typ1 typ2. inverts H16. inverts H17.
  forwards*:  TypedReduce_prv_value H16. forwards*: value_lc H17. 
  forwards*: TypedReduce_preservation H16.
  forwards*: TypedReduce_nlam H16. 
  assert(Typing nil x Chk t_dyn); eauto. 
  assert(Typing nil v2 Chk t_dyn); eauto. 
  forwards*: tdynamic_guarantee H18 H7. inverts H24. inverts H25.
  forwards*:  TypedReduce_prv_value H24. forwards*: value_lc H25.
  forwards*: epre_lc ep2.
  assert(epre (e_abs e1) (e_abs e1')); eauto.
  forwards*: epre_lc H29.
  exists. split. 
  apply star_one. apply Step_beta; eauto. 
  apply ep_anno; eauto.  apply ep_anno; eauto. apply ep_anno; eauto. 
  pick fresh xx.
  assert((e1' ^^ x0) = [xx ~> x0] (e1' ^ xx)).
  rewrite (subst_exp_intro xx); eauto.
  rewrite (subst_exp_intro xx); eauto.
  rewrite H31.
  forwards*: H4 xx.
  forwards*: epre_open H32 H26. 
  * inverts H.
  +
    inverts* tlist; try solve[inverts* H4].
    inverts* ep2; inverts* typ2; try solve[inverts* H4].
    assert(epre (e_abs e1) (e_abs e1')); eauto.
    assert(epre (e_abs e) (e_abs e2)); eauto.
    forwards*: epre_lc H0.
    forwards*: epre_lc H3.
    inverts* tp1.
    inverts* tp2.
    exists. split.
    apply star_one; eauto.
    apply Step_beta; eauto.
    forwards*: tp_not_int H10.
    apply ep_anno; eauto.  apply ep_anno; eauto. apply ep_anno; eauto.
    inverts ep1. 
    pick fresh xx.
    assert((e1' ^^ (e_anno (e_anno (e_abs e2) (t_arrow A B)) B1) ) = [xx ~> (e_anno (e_anno (e_abs e2) (t_arrow A B)) B1)] (e1' ^ xx)).
    rewrite (subst_exp_intro xx); eauto.
    rewrite (subst_exp_intro xx); eauto.
    rewrite H7.
    forwards*: H9 xx.
    assert(epre ( e_anno (e_anno (e_abs e) (t_arrow t1 t2)) A1) (e_anno (e_anno (e_abs e2) (t_arrow A B)) B1)).
    apply ep_anno; eauto.  
    forwards*: epre_open H8 H13. 
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
      inverts typ1. inverts typ2.
      inverts H. inverts H4.
      forwards*: Typing_chk H10. inverts H.
      forwards*: Typing_chk H9. inverts H.
      forwards*: IHep1 H4. inverts H. inverts H8.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H11. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_app.
      inverts H8.
      forwards*: val_prel ep1. 
      forwards*: epre_lc ep1.
      inverts* ep1. apply H.
      unfold simpl_fill. eauto.
    + inverts typ1. inverts typ2.  inverts H. inverts H5.
      inverts H11. forwards*: val_prel ep2. 
      inverts ep1.
      inverts H10. 
      assert(epre (e_abs e) (e_abs e0));eauto.
      forwards*: epre_lc H5.
      inverts H12. inverts H13.
      forwards*: tdynamic_guarantee ep2 H4. inverts H13. inverts H19.
      exists. split.
      apply star_one.
      apply Step_nbeta; eauto.
      apply ep_anno; eauto.
      pick fresh xx.
      assert((e0 ^^ x  = [xx ~> x] (e0 ^ xx))).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H19.
      forwards*: TypedReduce_prv_value H13.
      forwards*: TypedReduce_prv_value H4.
      forwards*: value_lc H21.
      forwards*: value_lc H22.
      forwards*: H8.
      forwards*: epre_open H25 H20.
    +
      inverts typ2. inverts H. 
      forwards*: ano_ano_epre ep1.
      lets(e3&t2&eq&epl&tpl): H. inverts eq. 
      inverts* tpl; try solve[inverts* H8].
      forwards*: anno_chk H8. inverts H5.
      forwards*: sval_ep_sval epl. inverts H5. 
      inverts epl. inverts H14.
      inverts H8.
      *
        assert(tpre (t_arrow A1 B1) (t_arrow A3 B)); eauto.
        assert(tpre (t_arrow A2 B2) (t_arrow A0 A)); eauto.
        inverts typ1. inverts H12. inverts H22.
        forwards*: typlist_guarantee2 H16 H5 H8 H4.
        forwards*: typlist_guarantee2 H16 H5 H8 H4.
      *
        assert(tpre (t_arrow A1 B1) (t_arrow A3 B)); eauto.
        assert(tpre (t_arrow A2 B2) (t_arrow A0 A)); eauto.
        inverts typ1. inverts H12. inverts H25.
        forwards*: typlist_guarantee2 H16 H5 H8 H4.
        forwards*: typlist_guarantee2 H16 H5 H8 H4.
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep1 H2. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_add2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H2. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_add.
      forwards*: val_prel ep1. apply H.
      unfold simpl_fill. eauto.
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
      inverts H8. inverts H7.
      exists*. split.
      apply star_one. apply Step_abs; eauto.
      apply ep_anno; eauto.  
    +
      destruct E; unfold simpl_fill in H0; inverts H0.
    +
      forwards*: Typing_regular_1 typ2. inverts H0. 
      forwards*: Typing_regular_1 typ1. inverts H0. 
      destruct(value_decidable (e_anno e2 B)); eauto.
      * inverts H0; try solve [inverts ep;exfalso; apply H4; eauto];
        try solve [exfalso; apply H4; eauto].
        inverts ep. inverts H9. inverts H8. inverts H5.
        exfalso; apply H4; eauto.
      *
       inverts typ1. inverts typ2. 
       forwards*: anno_chk H1. inverts H11.
       forwards*: anno_chk H8. inverts H11.
       forwards*: IHep H3. inverts H11. inverts H14.
       forwards*: multi_red_anno H11.
    + 
      inverts typ1. inverts typ2.
      forwards*: anno_chk H0. inverts H8. 
      forwards*: anno_chk H5. inverts H8. 
      forwards*: tdynamic_guarantee ep H H4. inverts H8. inverts H11.
      forwards*:val_prel ep.
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
    forwards*: val_prel ep.
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


