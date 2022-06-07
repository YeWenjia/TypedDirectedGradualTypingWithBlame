Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


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

Lemma Tred_value: forall v v'  p b A,
  value v->
  TypedReduce v p b A (e_exp v') ->
  value v'.
Proof.
  introv Val Red.
  inductions Red; eauto.
  - apply value_dyn; eauto.
    inverts H.
    inverts H1.
    inverts Val; inverts* H2.
    eapply value_fanno; eauto.
    reflexivity.
  - inverts Val.
    inverts H.
    inverts H2.
    inverts* H4.
    inverts* H0.
    rewrite <- H4 in H3.
    inverts H3.
  - inverts* Val.
Qed.



Lemma TypedReduce_sim: forall v A r B p b,
    value v -> TypedReduce v p b A r -> Typing nil v Inf B -> sim B A.
Proof with auto.
  introv Val Red Typ.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  forwards*: principle_inf Typ.
  rewrite H1 in H0.
  rewrite H0.
  auto.
Qed.


Lemma TypedReduce_preservation: forall v A v' p b,
    value v -> TypedReduce v p b A (e_exp v') -> Typing nil v Chk A -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  lets Typ: Typ'.
  inductions Red; intros;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  + inverts Typ. inverts* H0.
  + inverts Typ.
    inverts Val; inverts H. inverts H4.
    inverts H5. inverts H2. inverts H0. 
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    inverts H0. 
    apply Typ_anno; eauto.
  + inverts* Typ. inverts H1. inverts H10. 
    inverts Val.  
    forwards*: principle_inf H1.
    rewrite H6 in H0.
    apply Typ_anno; eauto.
  + inverts* Typ. inverts H. inverts H8.
    inverts Val.
    forwards*: principle_inf H.
    rewrite H4. auto.
Qed.


Lemma TypedReduce_nlambda: forall v A v' p b ,
    value v -> Typing nil v Chk A -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
 - inverts typ. inverts H. inverts* H8.
Qed.


Lemma TypedReduce_nlambda2: forall v t A v' p b,
    value v -> ttyping nil v (Chk2 p b) A t -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
 - inverts typ. inverts H1. inverts* H9.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (e_exp e') ->
    Typing nil e' dir A.
Proof.
  introv Typ Red. gen A dir.
  inductions Red; intros.
  - inductions E; unfold fill in *.
  + inverts Typ.
    forwards*: IHRed H7.
    inverts H0.
    forwards*: IHRed H9.
  + inverts Typ.
    forwards*: IHRed H8.
    inverts H0.
    forwards*: IHRed H10.
  + inverts Typ.
    forwards*: IHRed H7.
    inverts H0.
    forwards*: IHRed H9.
  - inverts Typ.
    + 
    inverts H9.
    pick fresh y.
    apply Typ_anno.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    inverts H10.
    forwards*: TypedReduce_preservation H1.
    forwards*: TypedReduce_nlambda H1.
    +
    inverts H2. 
    inverts H11. 
    pick fresh x.
    eapply Typ_sim; eauto.
    apply Typ_anno; eauto.
    rewrite (subst_exp_intro x); eauto.
    eapply typing_c_subst_simpl; eauto.
    inverts* H12.
    forwards*: TypedReduce_preservation H1.
    forwards*: TypedReduce_nlambda H1.
  - 
    inverts Typ.
    + inverts* H9. inverts H4.
      forwards*: TypedReduce_preservation H1.
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypedReduce_nlambda H1.
      inverts H5.
    + inverts* H2. inverts H11. inverts H6.
      forwards*: TypedReduce_preservation H1.
      eapply Typ_sim; eauto.
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypedReduce_nlambda H1.
      inverts H7.
  - inverts Typ. inverts H9.
    exfalso; apply H1; eauto.
    eapply value_fanno; eauto. reflexivity.
    forwards*: TypedReduce_preservation H0.
    inverts H2. inverts H11.
    exfalso; apply H1; eauto.
    eapply value_fanno; eauto. reflexivity.
    forwards*: TypedReduce_preservation H0.
    eapply Typ_sim; eauto.
    forwards*: TypedReduce_nlambda H0.
  - inverts Typ. inverts H10. inverts H5. inverts H3.
    forwards*: TypedReduce_preservation H1.
    apply Typ_anno; auto. inverts H4. apply Typ_sim with (A:=D);eauto.
    eapply Typ_app; eauto. 
    eapply Typ_sim; eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda H1.
    inverts H3. inverts H12. inverts H7. inverts H3. inverts H6.
    eapply Typ_sim;eauto.  eapply Typ_anno;eauto. eapply Typ_sim;eauto.
    eapply Typ_app; eauto.  
    forwards*: TypedReduce_preservation H1.
    eapply Typ_sim;eauto. apply BA_AB; auto.
    forwards*: TypedReduce_nlambda H1.
Qed. 



Theorem preservation_multi_step : forall t t' dir  T,
    Typing nil t dir T ->
    t ->** (e_exp t') ->
    Typing nil t' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
Qed.


Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto.
    right.
    unfold not; 
    intros.
    inverts* H.
  - inductions A; eauto.
    right.
    unfold not; 
    intros.
    inverts* H.
    forwards*: IHB1 A1.
    forwards*: IHB2 A2.
    destruct H.
    destruct H0.
    left.
    eauto.
    right.
    unfold not; 
    intros.
    inverts* H1.
    destruct H0.
    right.
    unfold not; 
    intros.
    inverts* H1.
    right.
    unfold not; 
    intros.
    inverts* H1.
Qed.



Lemma TypedReduce_progress: forall v p b A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v p b A r.
Proof.
  introv Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
  - inverts Typ.
    exists*.
    inverts H2. 
  - inverts Typ.
    inverts H0.
    inductions A0; inverts H1; eauto.
    destruct (eq_type A).
    destruct (eq_type B).
    subst*.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H3.
    split.
    unfold not; intros H3;
    inverts* H3.
    eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H1.
    split.
    unfold not; intros H3;
    inverts* H3.
    eauto.
  - inverts Typ.
    inverts H0.
    inverts H9.
    inductions A; eauto.
    +
    inverts* Val; inverts* H.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_blame; eauto.
    unfold not; intros nt; inverts nt.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    +
    inverts* Val; inverts* H.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H. inverts H4.
    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H8.
    split.
    unfold not; intros;
    inverts* H8.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H7.
    split.
    unfold not; intros;
    inverts* H7.
    eauto.
    simpl. eauto.
    +
    exists.
    apply TReduce_dd; eauto.
    apply value_lc; auto. 
Qed.

Lemma dyn_decidable: forall A,
 (A = t_dyn) \/ not(A = t_dyn).
Proof.
  introv.
  inductions A; try solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*].
Qed.


Lemma value_decidable: forall e,
  lc_exp e -> value e \/ not(value e).
Proof.
  introv lc.
  inductions lc; try solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*].
  inverts IHlc.
  - inductions H; try solve[right; unfold not; intros nt; inverts* nt];
   try solve[left*].
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
   try solve[left*].
   right; unfold not; intros nt; inverts* nt.
   inverts* H5.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
   try solve[left*].
   left. eapply value_fanno; eauto. reflexivity.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    destruct(dyn_decidable A0);destruct(dyn_decidable B);subst*;
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H5];
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
    try solve[left*].
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    right; unfold not; intros nt; inverts* nt. inverts* H7.
    right; unfold not; intros nt; inverts* nt. inverts* H3.
  - inductions lc; try solve[exfalso; apply H; auto];
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
Qed.


Theorem progress : forall e dir T,
    Typing nil e dir T ->
    value e \/ (exists r, step e r).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].    
  - Case "var".
    inverts* H0.
  - right. inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts* Val1; inverts* H2 ].
    + forwards*: TypedReduce_progress p (negb b) Typ2.
      inverts* H.
      inductions x.
      exists*.
      inverts* H0.
      exfalso. apply H8; eauto.
    + inverts* Val1. inverts H3; inverts H8.
      * forwards*: TypedReduce_progress p (negb b) Typ2.
          destruct H2.
          inductions x.
          exists.
          apply Step_beta; eauto.
          exists. apply Step_betap; eauto.
          eapply value_fanno; eauto. reflexivity.
          inverts* H2.
      * forwards*: TypedReduce_progress p (negb b) Typ2.
          destruct H3.
          inductions x.
          exists. apply Step_abeta; eauto.
          exists. apply Step_betap; eauto.
          eapply value_fanno; eauto. reflexivity.
          inverts* H3.
    +  inductions e2'.
      assert(fill ((appCtxR e1 p b )) e2 = e_app e1 p b e2); eauto.
      rewrite <- H.
      exists. apply do_step; eauto.
      assert(fill ((appCtxR e1  p b )) e2 = e_app e1 p b e2); eauto.
      rewrite <- H.
      exists. apply blame_step; eauto.
    + 
      inductions e1'.
      assert(fill ((appCtxL e2 p b )) e1 = e_app e1 p b e2); eauto.
      rewrite <- H.
      exists. apply do_step; eauto.
      assert(fill ((appCtxL e2 p b )) e1 = e_app e1 p b e2); eauto.
      rewrite <- H.
      exists. apply blame_step; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress Typ.
      inverts* H.
      destruct(value_decidable (e_anno e p b A)); eauto.
    + right.
      inductions t'.
      * 
        assert(fill ((annoCtx p b A)) e = e_anno e p b A); eauto.
        rewrite <- H.
        exists. apply do_step; eauto.
      *
        assert(fill ((annoCtx p b A)) e = e_anno e p b A); eauto.
        rewrite <- H.
        exists. apply blame_step; eauto.
  - forwards*: IHTyp Typ.
Qed.