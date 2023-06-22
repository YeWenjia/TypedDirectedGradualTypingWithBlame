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

(* Ltac size_ind_auto :=
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
 value v -> ttyping nil v Inf A t -> dynamic_type v = A.
Proof.
  introv H typ.
  inductions H; inverts* typ; eauto.
Qed.



Lemma fillb_cast: forall v A B,
  (trm_cast v A B) = (fillb (castCtxb A B)  v).
Proof.
  introv.
  eauto.
Qed.

Lemma value_valueb: forall e t A,
 ttyping nil e Inf A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ. 
    forwards*: lc_lcb H.
  - inverts typ.
    inverts* H3. 
    forwards*: value_lc H.
    forwards*: lc_lcb H1.
    inverts H2.
    forwards*: IHvalue.
    inverts H; inverts H1. inverts H0.
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


Theorem Tred_blame_soundness: forall v t A,
  ttyping nil (e_anno v A) Inf A t->
  value v ->
  TypedReduce v A e_blame ->
  t ->* t_blame.
Proof.
  introv Typ val Red.
  inductions Red; intros. 
  inverts Typ. inverts H2. inverts H0. inverts H6.
  --
  simpl in *.
  destruct A.
  eapply bstep_b.
  apply bStep_vanyp; eauto.
  unfold not; intros nt; inverts* nt.
  forwards*: value_valueb val. inverts* H2.
  exfalso; apply H; eauto.
  exfalso; apply H; eauto.
  --
  inverts val.
  forwards*: principle_if H0.
  inductions A.
  - inverts* H7.
    + rewrite <- H10 in H.
      exfalso. apply H.
      eauto.
    + eapply bstep_b.
      apply bStep_vanyp; eauto.
      rewrite <- H10 in H6. inverts* H6.
      rewrite <- H10 in H6. inverts H6.
      unfold not; intros nt; inverts nt. 
      forwards*: value_valueb H8.
  - inverts* H7.
    + 
      destruct (eq_type A1).
      destruct (eq_type A2).
      subst.
       eapply bstep_b.
      apply bStep_vanyp; eauto.
      rewrite <- H10; eauto.  rewrite <- H10.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H8.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply valueb_dyn; eauto.
      forwards*: value_valueb H0.
      rewrite <- H10 in H6. inverts* H6. 
      unfold not; intros n; inverts n.
      unfold not; intros n; inverts* n.
      rewrite fillb_cast.
      apply bstep_b.
      apply Step_blameb; eauto.
      apply bStep_vanyp; eauto.
      rewrite <- H10 in H6.  inverts* H6.
      rewrite <- H10 in H6.  inverts* H6.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H0.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply valueb_dyn; eauto.
      forwards*: value_valueb H8.
      rewrite <- H10 in H6.  inverts* H6.
      unfold not; intros n; inverts n.
      unfold not; intros n; inverts* n.
      rewrite fillb_cast.
      apply bstep_b.
      apply Step_blameb; eauto.
      apply bStep_vanyp; eauto.
      rewrite <- H10 in H6.  inverts* H6.
      rewrite <- H10 in H6.  inverts* H6.
      unfold not; intros n; inverts n.
      forwards*: value_valueb H0.
    + rewrite <- H10 in H.
      exfalso. apply H.
      eauto.
  - 
      exfalso; apply H;
      eauto.
Qed.


Lemma Soundness_blame_two: forall e t dir A,
  ttyping nil e dir A t->
  step e e_blame ->
  t ->* t_blame.
Proof.
  introv Typ J. gen A dir t.
  inductions J; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      * forwards*: IHJ H3. 
      apply multi_blame_app2; eauto.
      inverts H.
      forwards*: lc_lcb H2.
      * inverts H0.
       forwards*: IHJ H6.
       apply multi_blame_cast; eauto.
      apply multi_blame_app2; eauto.
      inverts H.
      forwards*: lc_lcb H4.
      forwards*: IHJ H6.
      apply multi_blame_cast; eauto.
      apply multi_blame_app2; eauto.
      inverts H.
      forwards*: lc_lcb H4.
      apply multi_blame_cast; eauto.
      *
      inverts H.
      forwards*: lc_lcb H1.
      forwards*: IHJ H3. 
      apply multi_blame_app2; eauto.
      apply multi_blame_cast; eauto.
    + inverts Typ.
      * 
      forwards*: IHJ H7. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H3.
      * inverts H0.
      forwards*: IHJ H7.
      apply multi_blame_cast; eauto.
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H5.
      inverts H.
      forwards* h1: principle_if H6.
      rewrite h1 in H3.
      inverts H3.
      *
      inverts H.
      forwards* h1: principle_if H3.
      rewrite h1 in H1.
      inverts H1.
    + inverts Typ. 
      forwards*: IHJ H6.
      inverts H0. 
      forwards*: IHJ H5.
      apply multi_blame_cast; eauto.
  - inverts Typ.
    + inverts H5. 
      assert (ttyping nil (e_anno v2 A1) Inf A1 t2); eauto.
      forwards*: Tred_blame_soundness H0.
      apply multi_blame_app; eauto.
      inverts H.
      inverts H10. 
      forwards*: value_lc H6.
      forwards*: lc_lcb H.
      inverts H4.
      forwards*: value_valueb H.
      forwards*: principle_if H.
      rewrite H4 in H8.
      inverts H8.
    + inverts H2. inverts H8. 
      assert (ttyping nil (e_anno v2 A2) Inf A2 t2); eauto.
      forwards*: Tred_blame_soundness H0.
      apply multi_blame_cast; eauto.
      apply multi_blame_app; eauto.
      inverts H.
      inverts H12. 
      forwards*: value_lc H8.
      forwards*: lc_lcb H.
      inverts H6.
      forwards*: value_valueb H.
      forwards*: principle_if H.
      rewrite H6 in H11.
      inverts H11.
      inverts H8.
    +
      inverts H5.
  - inverts Typ. 
    * 
    assert (ttyping nil (e_anno v A0) Inf A0 t).
    eauto.
    forwards*: Tred_blame_soundness H0.
    * inverts H2.
    assert (ttyping nil (e_anno v A1) Inf A1 t0).
    eauto.
    forwards*: Tred_blame_soundness H0.
    apply multi_blame_cast; eauto.
  - inverts Typ. inverts H4. inverts H8. 
    assert (ttyping nil (e_anno v1 t_int) Inf t_int (trm_cast t A t_int)).
    eauto.
    forwards*: Tred_blame_soundness H0.
    apply multi_blame_app; eauto.
    inverts H1. inverts H7. 
    assert (ttyping nil (e_anno v1 t_int) Inf t_int t2).
    eauto.
    forwards*: Tred_blame_soundness H0.
    apply multi_blame_cast; eauto.
    apply multi_blame_app; eauto.
    inverts H7.
    +
      inverts H4.
  - inverts Typ.
    * inverts H4. inverts H8.
    assert (ttyping nil (e_anno v2 t_int) Inf t_int (trm_cast t A t_int)).
    eauto.
    forwards*: Tred_blame_soundness H0.
    apply multi_blame_app; eauto.
    * inverts H1.
    inverts H7. 
    assert (ttyping nil (e_anno v2 t_int) Inf t_int t2).
    eauto.
    forwards*: Tred_blame_soundness H0.
    apply multi_blame_cast; eauto.
    apply multi_blame_app; eauto.
    inverts H7.
    *
    inverts H4.
Qed.  *)





