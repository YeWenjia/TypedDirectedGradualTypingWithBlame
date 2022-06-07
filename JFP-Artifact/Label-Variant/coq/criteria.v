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
      forwards*: IHep1 H5 H7.
      inverts* H.
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



Lemma val_prel: forall e1 e2 dir B,
  Typing nil e2 dir B ->
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv typ2 ep vval1. gen e2 B.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H5. eauto. 
  - inverts ep. inverts H6. inverts H8. inverts H7.
    inverts typ2. inverts H9. inverts H0.
    inverts H11. inverts H6. inverts H11.
    inverts H9. inverts H3. 
    inverts H0. inverts H11. inverts H0. inverts H13.
    inverts H8. inverts H13. inverts H12. inverts H6. 
    assert(epre ((e_abs e)) ((e_abs e0))). eauto. 
    forwards*: epre_lc H0.
Qed.


Lemma sval_ep_sval:forall e1 e2 dir  A,
 Typing nil e2 dir A ->
 sval e1 ->
 epre e1 e2 ->
 sval e2.
Proof.
  introv typ sval ep.
  inverts sval. inverts* ep.
  inverts H6. inverts* H5.
  inverts typ. inverts H8. inverts H3.  
  inverts H0. inverts H10. inverts H5.
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


Lemma anno_chk: forall e t1 t2 l b ,
 [] ⊢ e_anno e l b t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
  forwards*: Typing_chk H7. 
Qed.




Lemma anno_anno: forall e e0 C C0 B0 A dir l b l0 b0 l1 b1,
 Typing nil e0 dir A ->
 ssval e -> 
 sim (principal_type e) C ->
 tpre C B0 ->
 epre e e0 ->
 exists e2', TypedReduce (e_anno e0 l0 b0 C0) l b B0 (Expr e2') /\ epre (e_anno e l1 b1 C) e2'.
Proof.
  introv typ sval sim tp ep.
  forwards*: ssval_ep_ssval ep.
  inverts sval.
  -
   inverts ep. simpl in sim.
   inverts H7. inverts H. 
   inverts sim.
    + inverts* tp.
      exists*.
      assert(tpre (t_arrow C1 D) (t_arrow C D0)); eauto.
      forwards*: epre_sim H6 H.
      exists*.
    + inverts tp.
      exists*.
  -
    inverts ep. simpl in *.
    assert(tpre t_int t_int); eauto.
    forwards*: epre_sim sim H0 tp.
Qed.


Lemma ano_ano_epre: forall e t e2 l1 b1 ,
 epre (e_anno e l1 b1 t) e2 ->
 exists e3 t2 l2 b2, e2 = (e_anno e3 l2 b2 t2) /\ epre e e3 /\ tpre t t2.
Proof.
  introv ep.
  inverts* ep.
  exists*.
Qed.


Lemma tdynamic_guarantee: forall e1 e2 e1' A B l1 b1 l2 b2 A1 B1,
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 Typing nil e1 Chk A1 ->
 Typing nil e2 Chk B1 -> 
 TypedReduce e1 l1 b1 A (Expr e1') ->
 exists e2', TypedReduce e2 l2 b2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val typ1 typ2 red. gen e2 B l2 b2.
  inductions red; intros; eauto.
  - 
    forwards*: ano_ano_epre ep.
    lets(e3&t2&l3&b3&eq&ep1&tp1): H2. inverts eq.
    inverts typ2.
    forwards*: anno_chk H3. inverts H6. 
    forwards*: anno_anno tp ep1.
  -
   forwards*: ano_ano_epre ep.
    lets(e3&t2&l3&b3&eq&ep1&tp1): H0. inverts eq.
    inverts typ2.
    forwards*: anno_chk H1. inverts H4. 
    forwards*:sval_ep_sval ep1.
    inverts H4. inverts tp.
    exists*.
    exists*.
Qed.


Lemma typlist_guarantee3: forall e1 e2 e2' e1' A1 A2 A3 A4 B1 B2 B3 B4 v' l4 b4 l5 b5 l6 b6 l1 b1 l3 b3 l0 b0,
 walue e2 ->
 lc_exp (e_abs e1) ->
 Typing nil e2 Chk A3 ->
 Typing nil e2' Chk B3 ->
 epre (e_abs e1) (e_abs e1') -> 
 tpre (t_arrow A1 A2) (t_arrow B1 B2) ->
 tpre (t_arrow A3 A4) (t_arrow B3 B4) ->
 epre e2 e2' ->
 TypeLists e2 [t_typs A3 l1 (negb b1);t_typs t_dyn l3 (negb b3);t_typs A1 l3 (negb b3) ] (Expr v') ->
 exists e2'0,
 e_app (e_anno (e_anno (e_abs e1') l4 b4 (t_arrow B1 B2)) l5 b5 (t_arrow B3 B4)) l6 b6 e2' ->* Expr e2'0 /\ epre (e_anno (e_anno (e_anno (e1 ^^ v') l0 b0 A2) l3 b3 t_dyn) l3 b3 A4) e2'0.
Proof.
  introv val lc typ1 typ2 ep1 tp1 tp2. intros ep2 tlist.
  inverts val.
  +
  forwards*: val_prel ep2.
  inverts tlist. 
  * inverts H9. inverts H12; try solve[inverts H14].
  inverts tp1. inverts tp2. 
  inverts ep1.
  forwards*:  TypedReduce_prv_value H8.
  forwards*: TypedReduce_preservation H8.
  forwards*: TypedReduce_nlam H8. 
  forwards*:  TypedReduce_prv_value H11.
  forwards*: TypedReduce_preservation H11. 
  forwards*:  TypedReduce_prv_value H9.
    forwards*: value_lc H17.
  forwards*: tdynamic_guarantee ep2 H6 typ1 typ2. inverts H19. inverts H20.
  forwards*:  TypedReduce_prv_value H19. forwards*: value_lc H20. 
  forwards*: TypedReduce_preservation H19.
  forwards*: TypedReduce_nlam H19. 
  assert(Typing nil x Chk t_dyn); eauto. 
  assert(Typing nil v2 Chk t_dyn); eauto. 
  forwards*: tdynamic_guarantee H21 H26 H25. inverts H27. inverts H28.
  forwards*:  TypedReduce_prv_value H27. forwards*: value_lc H28.
  forwards*:  TypedReduce_preservation H27.
  forwards*: TypedReduce_nlam H11. 
  forwards*: TypedReduce_nlam H27. 
  assert(Typing nil x0 Chk B1); eauto. 
  assert(Typing nil v0 Chk A1); eauto. 
  forwards*: tdynamic_guarantee H29 H5 H35 H34. inverts H36. inverts H37.
  forwards*:  TypedReduce_prv_value H36. forwards*: value_lc H37.
  forwards*: epre_lc ep2.
  assert(epre (e_abs e1) (e_abs e1')); eauto.
  forwards*: epre_lc H41.
  exists. split. 
  apply star_one. apply Step_beta; eauto. 
  apply ep_anno; eauto.  apply ep_anno; eauto. apply ep_anno; eauto. 
  pick fresh xx.
  assert((e1' ^^ x1) = [xx ~> x1] (e1' ^ xx)).
  rewrite (subst_exp_intro xx); eauto.
  rewrite (subst_exp_intro xx); eauto.
  rewrite H43.
  forwards*: H3 xx.
  forwards*: epre_open H44 H38. 
  * inverts H.
  +
    inverts ep2.
    inverts tlist. inverts H9. inverts H12.
    inverts* H8.
    inverts H14.
    inverts typ2; try solve[inverts H3].
    inverts tp2.
    assert(epre (e_anno (e_anno (e_abs e) l1 (negb b1) (t_arrow t1 t2)) l3 (negb b3) t_dyn) (e_anno (e_anno (e_abs e2) l6 (negb b6) (t_arrow A B)) l5 (negb b5) t_dyn)).
    eauto.
    forwards*:  TypedReduce_prv_value H12.
    forwards*: TypedReduce_preservation H12.
     forwards*: value_lc H2.
     inverts tp1.
    forwards*: tdynamic_guarantee H0  H11 H12. 
    eapply Typ_sim; eauto.
    inverts H8. inverts H9.
    forwards*: epre_lc ep1.
    assert(epre (e_abs e) (e_abs e2)); eauto.
    forwards*: epre_lc H13.
    forwards*: TypedReduce_prv_value H8.
    forwards*: value_lc H16.
    exists. split. 
    apply star_one; eauto. 
    apply ep_anno; eauto.  apply ep_anno; eauto. apply ep_anno; eauto.
    inverts ep1. 
    pick fresh xx.
    assert((e1' ^^ x) = [xx ~> x] (e1' ^ xx)).
    rewrite (subst_exp_intro xx); eauto.
    rewrite (subst_exp_intro xx); eauto.
    rewrite H18.
    forwards*: H20 xx.
    forwards*: epre_open H19 H10. 
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
      forwards*: Typing_chk H13. inverts H.
      forwards*: Typing_chk H12. inverts H.
      forwards*: IHep1 H2. inverts H. inverts H8.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. inverts H. inverts H4. 
      forwards*: IHep2 H2. inverts H. inverts H4.
      exists. split. inverts H1. apply multi_red_app.
      inverts H8.
      forwards*: val_prel ep1. 
      forwards*: epre_lc ep1.
      inverts* ep1. apply H.
      unfold simpl_fill. eauto.
    + 
      inverts typ1. inverts typ2.  inverts H. inverts H3.
      inverts H14. forwards*: val_prel ep2. 
      inverts ep1.
      inverts H13. 
      assert(epre (e_abs e) (e_abs e0));eauto.
      forwards*: epre_lc H3.
      inverts H15. inverts H16.
      forwards*: tdynamic_guarantee ep2 H6. inverts H16. inverts H19.
      exists. split.
      apply star_one.
      apply Step_nbeta; eauto.
      apply ep_anno; eauto.
      pick fresh xx.
      assert((e0 ^^ x  = [xx ~> x] (e0 ^ xx))).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H19.
      forwards*: TypedReduce_prv_value H16.
      forwards*: TypedReduce_prv_value H6.
      forwards*: value_lc H21.
      forwards*: value_lc H22.
      forwards*: H8.
      forwards*: epre_open H25 H20.
    + 
      inverts typ2. inverts H. 
      forwards*: ano_ano_epre ep1.
      lets(e3&t2&ll1&bb1&eq&epl&tpl): H. inverts eq. 
      inverts* tpl; try solve[inverts* H11].
      forwards*: anno_chk H11. inverts H3.
      forwards*: sval_ep_sval epl. inverts H3. 
      inverts epl. inverts H13.
      inverts H11.
      *
        assert(tpre (t_arrow A1 B1) (t_arrow A3 B)); eauto.
        assert(tpre (t_arrow A2 B2) (t_arrow A0 A)); eauto.
        inverts typ1. inverts H11. inverts H25.
        forwards*: typlist_guarantee3 H20 H3 H10 H6.
        forwards*: typlist_guarantee3 H20 H3 H10 H6.
      *
        assert(tpre (t_arrow A1 B1) (t_arrow A3 B)); eauto.
        assert(tpre (t_arrow A2 B2) (t_arrow A0 A)); eauto.
        inverts typ1. inverts H11. inverts H28.
        forwards*: typlist_guarantee3 H20 H3 H10 H6.
        forwards*: typlist_guarantee3 H20 H3 H10 H6.
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
    + inverts typ2. inverts ep1. inverts ep2.
      inverts H10. inverts H8.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
  - inverts* red.
    + inverts ep. 
      assert(epre (e_abs e) (e_abs e0)); eauto.
      forwards*: epre_lc H0.
      inverts typ2. inverts H. inverts H4.
      inverts H12. inverts H7.
      exists*. split.
      apply star_one. apply Step_abs; eauto.
      apply ep_anno; eauto.  
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
    + inverts typ1. inverts typ2.
      forwards*: anno_chk H0. inverts H8. 
      forwards*: anno_chk H3. inverts H8. 
      forwards*: tdynamic_guarantee ep H H6. inverts H8. inverts H11.
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
 value m1 ->
 e1 ->* (Expr m1) ->
 exists m2, value m2 /\ e2 ->* (Expr m2) /\ epre m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  - forwards*: val_prel ep. 
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

