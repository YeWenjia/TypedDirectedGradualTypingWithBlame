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
        soundness
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
 value v -> ttyping nil v Inf A t -> principal_type v = A.
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
  inverts Typ. inverts H2. 
  inverts H0. inverts H6;
  simpl in *.
  -
    destruct A.
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros nt; inverts* nt.
    forwards*: value_valueb val. inverts* H2.
    exfalso; apply H; eauto.
    exfalso; apply H; eauto.
  -
     inverts val.
    forwards*: principle_if H0.
    inverts H8; simpl in *;try solve[inverts* H7]; 
    try solve[exfalso; apply H5; eauto];subst*.
    *
    forwards*: value_valueb H0.
    inductions A; try solve[exfalso; apply H; auto].
    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros n; inverts n.
    eapply bstep_nb.
    apply bStep_dyna; eauto. 
    unfold not; intros n; inverts* n.
    unfold not; intros n; inverts* n.
    rewrite fillb_cast.
    apply bstep_b.
    apply blame_stepb; eauto.
    apply bStep_vanyp; eauto.
    unfold not; intros n; inverts* n.
    eapply bstep_nb.
    apply bStep_dyna; eauto.
    unfold not; intros n; inverts* n.
    unfold not; intros n; inverts* n.
    rewrite fillb_cast.
    apply bstep_b.
    apply blame_stepb; eauto.
    apply bStep_vanyp; eauto.
    unfold not; intros n; inverts* n.
    *
    inverts* H7.
    forwards*: value_valueb H0.
    inductions A; try solve[exfalso; apply H; auto].
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros n; inverts n.
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
      forwards*: value_valueb H4.
    + inverts Typ. 
      forwards*: IHJ H6.
      inverts H0. 
      forwards*: IHJ H5.
      apply multi_blame_cast; eauto.
  - inverts Typ.
    + 
      forwards*: principle_if H6.
      rewrite H3 in *. inverts H1.
      assert (ttyping nil (e_anno v2 A) Inf A t2); eauto.
      forwards*: Tred_blame_soundness H1.
      apply multi_blame_app; eauto.
      forwards*: value_valueb H.
    + inverts H3.
       forwards*: principle_if H9.
      rewrite H3 in *. inverts H1.
      assert (ttyping nil (e_anno v2 A) Inf A t2); eauto.
      forwards*: Tred_blame_soundness H2.
      apply multi_blame_cast; eauto.
      apply multi_blame_app; eauto.
      forwards*: value_valueb H.
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
Qed. 



Theorem soundness: forall e t A dir ,
  ttyping nil e dir A t->
  e ->** e_blame ->
  t ->* t_blame.
Proof.
  introv typ red. gen dir A t.
  inductions red;intros.
  -
  forwards*: soundness_mul_two H.
  inverts H0. inverts H1. 
  forwards*: IHred H2.
  -
  forwards*: Soundness_blame_two typ H.
Qed.





