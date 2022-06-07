Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        rulesb_inf
        Infrastructure
        Infrastructure_b
        Typing_b
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

Lemma eq_type: forall A,
 (A = t_dyn) \/ ~(A = t_dyn).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H].
Qed.

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma principle_if: forall v A t,
 value v -> ttyping nil v Inf2 A t -> principal_type v = A.
Proof.
  introv H typ.
  inductions H; inverts* typ; eauto.
Qed.



Lemma fillb_cast: forall v p b A B,
  (trm_cast v p b A B) = (fillb (castCtxb p b A B)  v).
Proof.
  introv.
  eauto.
Qed.

Lemma value_valueb: forall e t A,
 ttyping nil e Inf2 A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ. 
    forwards*: lc_lcb H.
  - inverts typ.
    inverts* H8. 
    forwards*: value_lc H.
    forwards*: lc_lcb H1.
    inverts H6.
    forwards*: IHvalue.
    inverts H; inverts H3. inverts H0.
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


Lemma Tred_blame_soundness: forall v t p b A,
  ttyping nil (e_anno v p b A) Inf2 A t->
  value v ->
  TypedReduce v p b A (e_blame p b) ->
  t ->* (t_blame p b) .
Proof.
  introv Typ val Red.
  inductions Red; intros. 
  inverts Typ. inverts H7. inverts H3. inverts H11.
  inverts val.
  forwards*: principle_if H3.
  inductions A.
  - inverts* H4.
    + rewrite <- H5 in H.
      exfalso. apply H.
      eauto.
    + eapply bstep_b.
      apply bStep_vanyp; eauto.
      rewrite H0 in H5. inverts* H5.
      rewrite H0 in H5. inverts H5.
      unfold not; intros nt; inverts nt. 
      forwards*: value_valueb H3.
  - inverts* H4.
    + 
      destruct (eq_type A1).
      destruct (eq_type A2).
      subst.
       eapply bstep_b.
      apply bStep_vanyp; eauto.
      rewrite <- H5; eauto.  rewrite <- H5.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H3.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply valueb_dyn; eauto.
      forwards*: value_valueb H3.
      rewrite H0 in H5. inverts* H5. 
      unfold not; intros n; inverts n.
      unfold not; intros n; inverts* n.
      rewrite fillb_cast.
      apply bstep_b.
      apply blame_stepb; eauto.
      apply bStep_vanyp; eauto.
      rewrite H0 in H5.  inverts* H5.
      rewrite H0 in H5.  inverts* H5.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H3.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply valueb_dyn; eauto.
      forwards*: value_valueb H8.
      rewrite H0 in H5.  inverts* H5.
      unfold not; intros n; inverts n.
      unfold not; intros n; inverts* n.
      rewrite fillb_cast.
      apply bstep_b.
      apply blame_stepb; eauto.
      apply bStep_vanyp; eauto.
      rewrite H0 in H5.  inverts* H5.
      rewrite H0 in H5.  inverts* H5.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H3.
    + rewrite H0 in H5. inverts H5.
      rewrite <- TEMP in H.
      exfalso. apply H.
      eauto.
  - 
      exfalso; apply H;
      eauto.
Qed.

Lemma Soundness_blame_two: forall e t dir p b A,
  ttyping nil e dir A t->
  step e (e_blame p b) ->
  t ->* (t_blame p b).
Proof.
  introv Typ J. gen A dir t.
  inductions J; intros.
  - destruct E; unfold fill in *.
    + inverts* Typ.
      * forwards*: IHJ H8. 
      apply multi_blame_app2; eauto.
      inverts H.
      forwards*: lc_lcb H2.
      * inverts H0.
      forwards*: IHJ H10.
      apply multi_blame_cast; eauto.
      apply multi_blame_app2; eauto.
      inverts H.
      forwards*: lc_lcb H4.
    + 
      inverts Typ.
      *
      forwards*: IHJ H9. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H2. 
      *
      inverts H0. 
      forwards*: IHJ H11.
      apply multi_blame_cast; eauto.
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H4. 
    + inverts Typ. 
      forwards*: IHJ H8.
      inverts H0. 
      forwards*: IHJ H10.
      apply multi_blame_cast; eauto.
  - inverts Typ. 
    * inverts H10.  
    assert (ttyping nil (e_anno v2 p (negb b2) A1) Inf2 A1 t2).
    apply ttyp_anno; eauto.  
    forwards*: Tred_blame_soundness H1.
    apply multi_blame_app; eauto.
    inverts H.
    inverts H12. 
    forwards*: value_lc H6.
    forwards*: lc_lcb H.
    inverts H9.
    forwards*: value_valueb H5.
    forwards*: principle_if H5.
    rewrite H in H10.
    inverts H10.
    * inverts H2. inverts H12.
     assert (ttyping nil (e_anno v2 p (negb b2) A2) Inf2 A2 t2).
     apply ttyp_anno; eauto.  
    forwards*: Tred_blame_soundness H1.
    apply multi_blame_cast; eauto.
    apply multi_blame_app; eauto.
    inverts* H14. inverts H.
    forwards*: value_lc H8.
    forwards*: lc_lcb H.
    inverts* H11. inverts H.
    forwards*: value_valueb H8.
    inverts H. 
    forwards*: principle_if H8. rewrite H in H14. inverts H14.
  - inverts Typ. 
    * 
    assert (ttyping nil (e_anno v l b0 A0) Inf2 A0 t).
    eauto.
    lets H0': H0.
    inverts H0'.
    forwards*: Tred_blame_soundness H0.
    * inverts H2.
    assert (ttyping nil (e_anno v l b0 A1) Inf2 A1 t0).
    eauto.
    apply multi_blame_cast; eauto.
    lets H0': H0.
    inverts H0'.
    forwards*: Tred_blame_soundness H0.
Qed.
