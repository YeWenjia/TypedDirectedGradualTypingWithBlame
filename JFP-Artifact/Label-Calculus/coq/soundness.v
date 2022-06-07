Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        rulesb_inf
        Infrastructure
        Infrastructure_b
        Deterministic
        Typing_b
        Type_Safety
        ttyping.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).

Lemma principle_if: forall v A t,
    value v -> ttyping nil v Inf2 A t -> principal_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.


Lemma value_valueb: forall e t A,
 ttyping nil e Inf2 A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ. 
    pick fresh x.
    forwards*: H2.
    forwards*: lc_lcb H. 
  - inverts typ.
    forwards*: value_lc H.
    forwards*: lc_lcb H8.  
    inverts* H8. 
    forwards*: IHvalue.
    forwards*: principle_if H5.
    rewrite H4 in H0. inverts H0.
    eapply valueb_fanno; eauto.
  - inverts typ.
    inverts* H8.
    forwards*: IHvalue.
    forwards*: principle_if H3.
    rewrite H2 in H.
    apply valueb_dyn; eauto.
Qed.

Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma fillb_cast: forall v A p b B,
  (trm_cast v A p b B) = (fillb (castCtxb A p b B )  v).
Proof.
  introv.
  eauto.
Qed.

Lemma Tred_soundness: forall v t v' p b A,
  ttyping nil (e_anno v p b A) Inf2 A t->
  value v ->
  TypedReduce v p b A (e_exp v') ->
  exists t', t ->* (t_term t') /\ ttyping nil v' Inf2 A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - inverts Typ.
    inverts H7. exists*.
    forwards*: principle_if H3.
  - inverts Typ.
    inverts H6.
    forwards*: principle_if H2.
  - inverts Typ.
    inverts H5.
    inverts H1.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply ttyp_lit; eauto.
  - inverts Typ.
    inverts H6.
    inverts H2.
    inverts H10.
    inverts val.
    exists. split.
    apply star_one.
    apply bStep_dd; eauto.
    apply valueb_dyn; eauto.
    forwards*: value_valueb H2.
    forwards*: principle_if H2.
    rewrite H0 in H3.
    auto.
    simpl.
    apply ttyp_anno; eauto.
  - inverts Typ.
    inverts H6.
    forwards*: principle_if H2.
    rewrite H0 in H.
    inverts* H.
    inverts H3.
    inverts H4.
    rewrite <- TEMP in H.
    rewrite <- TEMP in H1.
    exists. split.
    apply star_one.
    apply bStep_anyd; eauto.
    forwards*: value_valueb val.
    simpl.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    rewrite <- TEMP in H2. auto.
    rewrite <- TEMP in H1.
    exfalso. apply H1. reflexivity.
  - inverts Typ. inverts val.
    inverts H8. inverts H5. inverts H14.
    forwards*: principle_if H5.
    rewrite H1 in H4.
    rewrite H1 in H0.
    exists. split.
    eapply bstep_n.
    apply bStep_dyna; eauto.
    apply valueb_dyn; eauto.
    forwards*: value_valueb H5.
    inverts* H. inverts* H. inverts* H.
    rewrite fillb_cast.
    eapply bstep_n.
    apply do_stepb; eauto.
    inverts H. inverts H7. inverts* H8.
    inverts H0. rewrite <- TEMP in H4. inverts H4.
    apply bStep_vany; eauto.
    forwards*: value_valueb H5.
    rewrite <- TEMP in H4. inverts H4.
    apply bstep_refl.
    apply ttyp_anno; eauto.
    inverts H. inverts H7. inverts* H8.
    inverts H0. rewrite <- TEMP in H4. inverts H4.
    rewrite <- TEMP in H5.
    apply ttyp_sim; eauto. 
    rewrite <- TEMP in H4. inverts H4.
  - inverts Typ. inverts val.
    inverts H5.
    inverts H2. inverts H11.
    forwards*: principle_if H2.
    exists. split.
    apply star_one.
    rewrite H. rewrite H in H1.
    apply bStep_vany; eauto.
    forwards*: value_valueb H2.
    rewrite H. auto.
Qed.



Lemma soundness_mul_two: forall e t e' A dir ,
  ttyping nil e dir A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ ttyping nil e' dir A t' .
Proof.
  introv Typ Red. gen A t dir.
  inductions Red; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H8. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H3.
      eapply ttyp_app; eauto.
      inverts H0.
      forwards*: IHRed H10. inverts H0. inverts H3.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app x t2) l0 b0 A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app2; auto.
      inverts H.
      forwards*: lc_lcb H5. 
      apply bstep_refl.
      eapply ttyp_sim; eauto.
    + inverts Typ. 
      * inverts H.
      forwards*: value_valueb H1.
      forwards*: IHRed H9. 
      inverts H0. inverts H2.
      exists. split.
      forwards: multi_red_app H H0.
      apply H2.
      eapply ttyp_app; eauto.
      *
      inverts H. inverts H0. 
      forwards*: value_valueb H4.
      forwards*: IHRed H11. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      forwards: multi_red_app H H0.
      apply H3.
      eapply ttyp_sim; eauto.
    + inverts Typ. 
      * forwards*: IHRed H8. inverts H0. inverts H1.
        exists. split.
        apply H0.
        apply ttyp_anno; eauto.
      * inverts H0.
        forwards*: IHRed H10. inverts H0. inverts H3.
        exists. split.
        apply multi_red_cast.
        apply H0.
        apply ttyp_sim;eauto.
   - inverts* Typ.
    * inverts H10.
      assert(ttyping nil (e_anno v p (negb b) t_dyn) Inf2 t_dyn t2).
      apply ttyp_anno; auto. inverts H11.
      forwards*: value_valueb H5.
      forwards*: Tred_soundness H1.
      destruct H4. destruct H4.
      exists. split.
      apply star_trans with (b:= (trm_app (trm_abs t_dyn t) x)).
      apply multi_red_app; eauto. forwards*: lc_lcb H.
      apply star_one. 
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      forwards*: Tred_value H1.
      forwards*: value_valueb H7.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H6.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H8. auto.
      forwards*: TypedReduce_nlambda2 H1.
    * inverts H2. inverts H12.
      assert(ttyping nil (e_anno v p (negb b) t_dyn) Inf2 t_dyn t2).
      apply ttyp_anno; auto. inverts H13.
      forwards*: value_valueb H7.
      forwards*: Tred_soundness H1.
      destruct H6. destruct H6.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app (trm_abs t_dyn t) x) l0 b0 t_dyn A).
      apply multi_red_cast; eauto.
      apply multi_red_app; eauto. forwards*: lc_lcb H.
      apply star_trans with (b := trm_cast (t ^^' x) l0 b0 t_dyn A).
      apply multi_red_cast; auto.
      apply star_one. 
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      forwards*: Tred_value H1.
      forwards*: value_valueb H10.
      apply bstep_refl.
      apply ttyp_sim; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H8.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H10. auto.
      forwards*: TypedReduce_nlambda2 H1.
  - inverts* Typ.
    * inverts* H10. forwards*: lc_lcb H.
      inverts* H12.
      assert(ttyping nil (e_anno v l2 (negb b2) A1) Inf2 A1 t2).
      apply ttyp_anno; auto.
      inverts* H11.
      forwards*: value_lc H0. 
      forwards*: lc_lcb H4.
      exists*. split.
      apply star_one. 
      apply bStep_beta; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H10.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H6. inverts H1.
      apply ttyp_anno; eauto.
      inverts* H1.
      forwards*: value_valueb H6.
      forwards*: Tred_soundness H1.
      destruct H5. destruct H5.
      exists. split.
      apply star_trans with (b:= trm_app (trm_abs A1 t) x ).
      apply multi_red_app; eauto.  
      apply star_one. 
      apply bStep_beta; eauto. forwards*: value_valueb H7. 
      forwards*: Tred_value H1.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H10.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H8. auto.
      forwards*: TypedReduce_nlambda2 H1.
       inverts H13.
    * inverts* H2. inverts H12. forwards*: lc_lcb H.
      inverts* H14. 
      assert(ttyping nil (e_anno v l2 (negb b2) A2) Inf2 A2 t2).
      apply ttyp_anno; auto.
      inverts* H13.
      forwards*: value_lc H0. 
      forwards*: lc_lcb H6.
      exists. split.
      apply multi_red_cast.
      apply star_one. 
      apply bStep_beta; eauto.
      eapply ttyp_sim; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H12.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H8. inverts H1.
      apply ttyp_anno; eauto.
      inverts* H1. 
      forwards*: value_valueb H8.
      forwards*: Tred_soundness H1.
      destruct H7. destruct H7.
      exists. split.
      apply multi_red_cast.
      apply star_trans with (b:= trm_app (trm_abs A2 t) x ).
      apply multi_red_app; eauto.  
      apply star_one. 
      apply bStep_beta; eauto. forwards*: value_valueb H9. 
      forwards*: Tred_value H1.
      eapply ttyp_sim; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H12.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H10. auto.
      forwards*: TypedReduce_nlambda2 H1.
       inverts H15.
  - inverts Typ.
    assert (ttyping nil (e_anno v l b A0) Inf2 A0 t).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H2.
    assert (ttyping nil (e_anno v l b A1) Inf2 A1 t0).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H5. inverts H6.
    exists. split.
    apply multi_red_cast; eauto.
    apply ttyp_sim;eauto.
    forwards*: TypedReduce_nlambda2 H0.
  - inverts Typ. 
    * inverts H11. 
    assert(ttyping nil (e_anno v2 l2 (negb b2) A1) Inf2 A1 t2).
    apply ttyp_anno; auto. inverts H13.
    inverts H6.  inverts H15.
    forwards*: Tred_soundness H1.
    destruct H4. destruct H4.
    inverts H. forwards*: value_lc H8. forwards*: lc_lcb H.  
    exists. split.
    apply star_trans with (b:= (trm_app (trm_cast (trm_abs C t0) l1 b1 (t_arrow C D) (t_arrow A1 A0)) x)).
    apply multi_red_app; eauto.
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H5. 
    forwards*: Tred_value H1.
    inverts H9.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda2 H1.
    inverts H.
    forwards*: value_valueb H7.
    forwards*: Tred_soundness H1.
    destruct H4. destruct H4.
    forwards*: principle_if H6. rewrite H8 in H15. inverts H15.
    exists. split.
    apply star_trans with (b:= (trm_app (trm_cast (trm_cast t0 l0 b0 (t_arrow C0 D0) (t_arrow C D)) l1 b1 (t_arrow C D) (t_arrow A1 A0)) x)).
    apply multi_red_app; eauto.  
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H5. 
    forwards*: Tred_value H1.
    inverts H9.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda2 H1.
    * 
    inverts H3. inverts H13. inverts H15. inverts H7. 
    assert(ttyping nil (e_anno v2 l2 (negb b2) A2) Inf2 A2 t2).
    apply ttyp_anno; auto. 
    inverts H16.
    forwards*: Tred_soundness H1.
    destruct H6. destruct H6.
    inverts H. forwards*: value_lc H11. forwards*: lc_lcb H.  
    exists. split.
    apply multi_red_cast.
    apply star_trans with (b:= (trm_app (trm_cast (trm_abs C t0) l1 b1 (t_arrow C D) (t_arrow A2 A1)) x)).
    apply multi_red_app; eauto.
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H7. 
    forwards*: Tred_value H1.
    inverts H10.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda2 H1.
    inverts H.
    forwards*: value_valueb H9.
    forwards*: Tred_soundness H1.
    destruct H6. destruct H6.
    forwards*: principle_if H8. rewrite H11 in H17. inverts H17.
    exists. split.
    apply multi_red_cast.
    apply star_trans with (b:= (trm_app (trm_cast (trm_cast t0 l0 b0 (t_arrow C0 D0) (t_arrow C D)) l1 b1 (t_arrow C D) (t_arrow A2 A1)) x)).
    apply multi_red_app; eauto.  
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H7. 
    forwards*: Tred_value H1.
    inverts H10.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda2 H1.
Qed.
