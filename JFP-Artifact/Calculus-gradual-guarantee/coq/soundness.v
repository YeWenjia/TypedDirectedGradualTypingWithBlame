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
    value v -> ttyping nil v Inf A t -> principal_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.


Lemma value_valueb: forall e t A,
 ttyping nil e Inf A t -> value e ->
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
    forwards*: lc_lcb H3.  
    inverts* H3. 
    forwards*: IHvalue.
    forwards*: principle_if H4.
    rewrite H7 in H0. inverts H0.
    eapply valueb_fanno; eauto.
  - inverts typ.
    inverts* H3.
    forwards*: IHvalue.
    forwards*: principle_if H1.
    rewrite H5 in H.
    apply valueb_dyn; eauto.
Qed.



Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.

Lemma fillb_cast: forall v A B,
  (trm_cast v A B) = (fillb (castCtxb A B)  v).
Proof.
  introv.
  eauto.
Qed.




Lemma Tred_soundness: forall v t v' A,
  ttyping nil (e_anno v A) Inf A t->
  value v ->
  TypedReduce v A (e_exp v') ->
  exists t', t ->* (t_term t') /\ ttyping nil v' Inf A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - inverts Typ.
    inverts H3; try solve[inverts val].
    exists*.
    forwards*: principle_if H1.
  - inverts Typ.
    inverts H2.
    exists* (trm_cast (trm_abs t_dyn t0) (t_arrow t_dyn t_dyn) t_dyn).
    forwards*: principle_if H0.
  - inverts Typ.
    inverts H1.
    inverts H.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply ttyp_lit; eauto.
  - 
    inverts Typ. inverts H2.
    forwards*: value_valueb H0.
    inverts H0. inverts H6.
    exists* (trm_cast (trm_abs t_dyn t) (t_arrow t_dyn t_dyn) t_dyn).
    inverts val. forwards*: principle_if H0. rewrite H6 in *.
    exists((trm_cast t A t_dyn)).
    splits*. 
  - inverts Typ. inverts H2.
    exists.
    splits*.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    forwards*: principle_if H0.
    rewrite H2 in H.
    inverts* H.
    inverts H5.
    inverts H6.
    rewrite <- TEMP in H.
    rewrite <- TEMP in H4.
    exists. split.
    apply star_one.
    apply bStep_anyd; eauto.
    forwards*: value_valueb val.
    simpl.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    rewrite <- TEMP in H0. auto.
    unfold not; intros nt; inverts nt. inverts H2.
    rewrite <- TEMP in H4.
    exfalso. apply H4. reflexivity.
  -
    inverts Typ. inverts H. inverts H1.
    inverts H3.
    +
    inverts H2; try solve[inverts* H1]. 
    inverts* H1.
    inverts* H9;
    try solve[exfalso; apply H6; eauto];
    try solve[exfalso; apply H2; eauto];
    try solve[inverts* H1].
    destruct(eq_type A0); destruct(eq_type B); substs;
    try solve[exfalso; apply H; eauto].
    exists.
    splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; eauto.
    forwards*: value_valueb val.
    apply star_one.
    rewrite fillb_cast.
    apply do_stepb; eauto.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H1.
    simpl.
    apply ttyp_anno; eauto.
    eapply ttyp_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H1.
    exists.
    splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; eauto.
    forwards*: value_valueb val.
    apply star_one.
    rewrite fillb_cast.
    apply do_stepb; eauto.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H2.
    simpl.
    apply ttyp_anno; eauto.
    eapply ttyp_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H2.
    exists.
    splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; eauto.
    forwards*: value_valueb val.
    apply star_one.
    rewrite fillb_cast.
    apply do_stepb; eauto.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H9.
    simpl.
    apply ttyp_anno; eauto.
    eapply ttyp_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H9.

    +
    exfalso; apply H0; eauto.
  -
    inverts Typ. inverts* H1. inverts* H.
    inverts* H4.
    exists. splits.
    apply star_one.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H.
    apply ttyp_anno; eauto.
    exfalso; apply H3; eauto.
  - inverts Typ. inverts val.
    inverts H4. inverts H2. inverts H10.
    exfalso; apply H1; eauto.
    forwards*: principle_if H2.
    rewrite H10 in H0.
    rewrite H10 in H3.
    exists. split.
    eapply bstep_n.
    apply bStep_dyna; eauto.
    apply valueb_dyn; eauto.
    forwards*: value_valueb H5.
    inverts* H. inverts* H.
    inverts* H.
    rewrite fillb_cast.
    eapply bstep_n.
    apply do_stepb; eauto.
    inverts H. inverts H12. inverts* H13.
    inverts H0. rewrite <- TEMP in H3. inverts H3.
    apply bStep_vany; eauto.
    forwards*: value_valueb H5.
    rewrite <- TEMP in H3. inverts H3.
    apply bstep_refl.
    apply ttyp_anno; eauto.
    inverts H. inverts H12. inverts* H13.
    inverts H0. rewrite <- TEMP in H3. inverts H3.
    rewrite <- TEMP in H2.
    apply ttyp_sim; eauto. 
    rewrite <- TEMP in H3. inverts H3.
  - inverts Typ. inverts val.
    inverts H2.
    inverts H0. inverts H7.
    exfalso; apply H; eauto.
    forwards*: principle_if H0.
    exists. split.
    apply star_one.
    rewrite H7. rewrite H7 in H1.
    apply bStep_vany; eauto.
    forwards*: value_valueb H3.
    rewrite H7. auto.
Qed.



Theorem soundness_mul_two: forall e t e' A dir ,
  ttyping nil e dir A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ ttyping nil e' dir A t' .
Proof.
  introv Typ Red. gen A t dir.
  inductions Red; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H3. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H4.
      eapply ttyp_app; eauto.
      inverts H0.
      forwards*: IHRed H6. inverts H0. inverts H3.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app x t2) A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app2; auto.
      inverts H.
      forwards*: lc_lcb H5. 
      apply bstep_refl.
      apply ttyp_sim; eauto.
      unfold not; intros nt; inverts nt. inverts H3.
    + inverts Typ. 
      *
      inverts H.
      forwards*: value_valueb H1.
      forwards*: IHRed H7. inverts H0. inverts H2.
      exists. split.
      forwards: multi_red_app H H0.
      apply H2.
      eapply ttyp_app; eauto.
      *
      inverts H. inverts H0. 
      forwards*: value_valueb H4.
      forwards*: IHRed H7. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      forwards: multi_red_app H H0.
      apply H3.
      eapply ttyp_sim; eauto.
      unfold not; intros nt; inverts nt. inverts H3.
    + inverts Typ. 
      * forwards*: IHRed H6. inverts H0. inverts H1.
        exists. split.
        apply H0.
        apply ttyp_anno; eauto.
      * inverts H0.
        forwards*: IHRed H5. inverts H0. inverts H3.
        exists. split.
        apply multi_red_cast.
        apply H0.
        apply ttyp_sim;eauto.
        unfold not; intros nt; inverts nt. inverts H3.
  - inverts* Typ.
    * 
      inverts H1.
      forwards*: value_valueb H10.
      forwards*: value_valueb H11.
      inverts H10.
      exists. split.
      eapply star_trans.
      apply multi_red_cast.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply ttyp_sim; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H14.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H5. auto.
      unfold not; intros nt;inverts nt. inverts H5.
    *
      forwards*: value_valueb H7.
      forwards*: value_valueb H11.
      inverts H7.
      exists. split.
      eapply star_trans.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H12.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H6. auto.
  - 
    inverts* Typ.
    * 
      inverts* H1. 
      inverts* H10; try solve[exfalso; apply H5; eauto].
      forwards*: value_valueb H11.
      forwards*: lc_lcb H.
      inverts H14; try solve[exfalso; apply H9; eauto].
      exists. split.
      eapply star_trans.
      rewrite fillb_cast.
      apply star_one.
      apply do_stepb;auto. 
      unfold fillb.
      apply bstep_refl. 
      eapply ttyp_sim; eauto.
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H13.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H5. apply H11.
      unfold not; intros nt; inverts nt. inverts H5.
      exfalso; apply H10; exists*.
    *
      inverts H7. 
      inverts* H12; try solve[exfalso; apply H6; eauto].
      forwards*: value_valueb H11.
      forwards*: lc_lcb H.
      exists. split.
      eapply star_trans.
      apply star_one.
      apply bStep_beta;auto.
      apply bstep_refl. 
      apply ttyp_anno; eauto.
      pick fresh y.
      forwards*: H8.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply ttyping_c_subst_simpl; auto.
      apply H6. apply H11.
  - 
    inverts Typ. 
    * 
    inverts H0. inverts H9. inverts H13. inverts H0. 
    forwards*: value_valueb H10.
    inverts H3. 
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H3.
    unfold not ; intros nt ; inverts nt. inverts H3.
    * 
    inverts H6. inverts H11. 
    forwards*: value_valueb H10.
    inverts H0.
    inverts H1.  
    exists. split.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H0.
  - 
    inverts Typ. 
    * 
    inverts H0. inverts H9. inverts H13. inverts H0. 
    forwards*: value_valueb H10.
    inverts H3. 
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H3.
    unfold not ; intros nt ; inverts nt. inverts H3.
    * 
    inverts H6. inverts H11. 
    forwards*: value_valueb H10.
    inverts H0.
    inverts H1.  
    exists. split.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H0.
  - inverts Typ. inverts H4. inverts H1. inverts H7.
  - inverts Typ.
    assert (ttyping nil (e_anno v A0) Inf A0 t).
    eauto.
    forwards*: Tred_soundness H2.
    inverts H2.
    assert (ttyping nil (e_anno v A1) Inf A1 t0).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H5. inverts H6.
    exists. split.
    apply multi_red_cast; eauto.
    apply ttyp_sim;eauto.
    forwards*: TypedReduce_nlambda2 H0.
  - 
    inverts Typ.
    +
    inverts H. inverts H8. inverts* H9.
    exists. splits.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_addl; eauto. 
    apply ttyp_sim; eauto.
    +
    inverts H5. inverts H9. 
    exists. splits.
    apply star_one. 
    apply bStep_addl; eauto. 
    apply ttyp_lit; eauto.
  - 
    inverts Typ. 
    * 
    inverts H1. inverts H10. inverts H14. 
    forwards*: value_valueb H1.
    forwards*: value_valueb H11.
    inverts H1. inverts H4. 
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H1.
    unfold not ; intros nt ; inverts nt. inverts H1.
    * 
    inverts H7. inverts H12. 
    forwards*: value_valueb H1.
    forwards*: value_valueb H11.
    inverts H1.
    inverts H2.  
    exists. split.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    unfold not ; intros nt ; inverts nt. inverts H1.
  -
    inverts Typ.
    +
    forwards*: principle_if H6. rewrite H3 in H1. inverts H1.
    assert(ttyping nil (e_anno v2 A) Inf A t2).
    apply ttyp_anno; auto. 
    forwards*: Tred_soundness H2.
    destruct H4. destruct H4.
    forwards*:  TypedReduce_walue2 H2.
    forwards*: value_valueb H6.
    exists. splits.
    apply multi_red_app; eauto.
    eapply ttyp_appv; eauto.
    +
    inverts H3.
    forwards*: principle_if H9. rewrite H3 in H1. inverts H1.
    forwards*: value_valueb H9.
    assert(ttyping nil (e_anno v2 A) Inf A t2).
    apply ttyp_anno; auto. 
    forwards*: Tred_soundness H2.
    destruct H7. destruct H7.
    forwards*:  TypedReduce_walue2 H2.
    exists. splits.
    apply multi_red_cast.
    apply multi_red_app; eauto.
    eapply ttyp_sim; eauto.
    unfold not ; intros nt ; inverts nt. inverts H12.
  -
    inverts Typ. 
    +
    inverts H. inverts H8. inverts H9.
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_add; eauto.
    eapply ttyp_sim; eauto.
    +
    inverts H5. inverts H9. 
    exists. split.
    apply star_one. 
    apply bStep_add; eauto.
    eapply ttyp_addl; eauto.
Qed. 




Theorem soundness: forall e t v1 A dir ,
  ttyping nil e dir A t->
  e ->** (e_exp v1) ->
  value v1 ->
  exists t', t ->* (t_term t') /\ ttyping nil v1 dir A t' .
Proof.
  introv typ red val. gen dir A t.
  inductions red;intros.
  -
  forwards*: value_lc val.
  -
  destruct dir.
  forwards*: soundness_mul_two H.
  inverts H0. inverts H1.
  forwards*: IHred H2.
  inverts* H1. 
  forwards*: soundness_mul_two H.
  inverts H0. inverts H1.
  forwards*: IHred H2.
  inverts* H1. 
Qed.