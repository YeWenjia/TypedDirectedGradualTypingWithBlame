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



Lemma value_group: forall v,
 value v ->
 walue v \/ (exists e', v = (e_abs e')) .
Proof.
  introv val.
  inductions val; try solve[left*];eauto.
  - left.
    inverts* IHval.
    inverts* H0.
  - inverts* IHval. inverts* H0.
Qed.


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


Lemma type_decidable: forall (A:typ) (B:typ),
 (A = B) \/ ~(A = B).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H];
  try solve[inductions B; 
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros nt; 
  inverts* nt]].
  inductions B; 
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros nt; 
  inverts* nt].
  forwards* eq1 :  IHA1 B1.
  forwards* eq2 :  IHA2 B2.
  inverts* eq1; inverts eq2;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros nt; 
  inverts* nt].
Qed.


Lemma Tred_value: forall v v' A,
  value v->
  TypedReduce v A (e_exp v') ->
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
    eapply value_fanno; eauto.
    reflexivity.
    eapply value_fanno; eauto.
    reflexivity.
  - inverts Val. inverts* H2.
    inverts H. inverts H2. inverts* H4.
    eapply value_fanno; eauto. reflexivity.
  - inverts Val. inverts* H1.
  - inverts Val.
    inverts H.
    inverts H5.
    inverts* H6.
    inverts* H0.
    rewrite <- H6 in H3.
    inverts H3.
  - inverts* Val.
Qed.



Lemma TypedReduce_sim: forall v A r B,
    value v -> TypedReduce v A r -> Typing nil v Inf B -> sim B A.
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

Lemma TypedReduce_preservation: forall v A v',
    value v -> TypedReduce v A (e_exp v') -> Typing nil v Chk A -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  lets Typ: Typ'.
  inductions Red; intros;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  + inverts Typ. inverts* H0.
  + inverts Typ; try solve[inverts* H].
    inverts Val; inverts H. inverts H4.
    inverts H5. 
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H.
    apply Typ_anno; eauto. inverts H0.
    eapply Typ_sim; eauto. inverts H0.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H.
    apply Typ_anno; eauto. inverts H0.
    eapply Typ_sim; eauto.
  +
    apply Typ_anno; eauto.
    inverts H. inverts H1.
    inverts Typ. inverts H1.
    apply BA_AB in H2.
    inverts H7.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); auto;
    try solve[unfold not; intros nt; inverts* nt; inverts H1].
    apply Typ_anno; eauto.
    inverts H1.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); auto;
    try solve[unfold not; intros nt; inverts* nt; inverts H1].
    apply Typ_anno; eauto.
  + apply Typ_anno; eauto.
    inverts Typ. inverts H.
    inverts* H4.
    eapply Typ_sim; eauto;
    try solve[unfold not; intros nt; inverts* nt; inverts H].
    exfalso; apply H3; eauto.
  +
    apply Typ_anno; eauto.
    inverts Typ. inverts H2. inverts* H7.
    eapply Typ_sim; eauto.
    inverts Val.
    forwards*: principle_inf H2.
    rewrite H7 in H0; auto.
  + inverts* Typ. inverts H0. inverts* H5. 
    inverts Val.  
    forwards*: principle_inf H0.
    rewrite H5 in *; auto.
Qed.






Lemma TypedReduce_nlambda: forall v A v',
    value v -> Typing nil v Chk A -> TypedReduce v A (e_exp v') -> not(exists e', v' = (e_abs e')).
Proof with auto.
 introv val typ red.
 inductions red; try solve[unfold not; intros nt ; inverts nt; inverts H1];
 try solve[unfold not; intros nt ; inverts nt; inverts H0];
 try solve[unfold not; intros nt ; inverts nt; inverts H].
 -
   inverts val. 
   unfold not; intros nt ; inverts nt. inverts H2.
 - 
  destruct(lambda_decidable v').
   inverts* H0. 
   inverts typ. inverts H1. inverts* H6.
Qed.

Lemma TypedReduce_nlambda2: forall v t A v',
    value v -> ttyping nil v Chk A t -> TypedReduce v A (e_exp v') -> not(exists e', v' = (e_abs e')).
Proof with auto.
 introv val typ red.
 inductions red; try solve[unfold not; intros nt ; inverts nt; inverts H1];
 try solve[unfold not; intros nt ; inverts nt; inverts H0];
 try solve[unfold not; intros nt ; inverts nt; inverts H].
 - unfold not; intros nt ; inverts nt. inverts H2.
 - unfold not; intros nt ; inverts nt. 
   apply H; eauto.
Qed.



Lemma TypedReduce_walue: forall v A v',
    value v -> Typing nil v Chk A -> TypedReduce v A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: TypedReduce_nlambda red.
Qed.



Lemma TypedReduce_walue2: forall v A v' t,
    value v -> ttyping nil v Chk A t -> TypedReduce v A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: TypedReduce_nlambda2 red.
Qed.



Lemma walue_nlam:forall v,
 walue v ->
 not(exists e', v = (e_abs e')) .
Proof.
  introv val.
  inductions val; try solve[unfold not; intros nt ; inverts nt; inverts H0];
  try solve[unfold not; intros nt ; inverts nt; inverts H].
Qed.

Hint Resolve walue_nlam: core.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (e_exp e') ->
    Typing nil e' dir A.
Proof.
  introv Typ Red. gen A dir.
  inductions Red; intros.
  - inductions E; unfold fill in *.
  + inverts Typ.
    forwards*: IHRed H4.
    inverts H0.
    forwards*: IHRed H7.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H3.
  + inverts Typ.
    forwards*: IHRed H7.
    inverts H0.
    forwards*: IHRed H8.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H3.
  + inverts Typ.
    forwards*: IHRed H5.
    inverts H0.
    forwards*: IHRed H5.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H3.
  - inverts Typ.
    + 
    inverts H1. inverts H10.
    pick fresh y.
    eapply Typ_sim; eauto.
    apply Typ_anno.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    unfold not; intros nt; inverts nt. inverts H1.
    +
    inverts H7. 
    pick fresh x.
    apply Typ_anno; eauto.
    rewrite (subst_exp_intro x); eauto.
    eapply typing_c_subst_simpl; eauto.
  - 
    inverts Typ.
    + inverts* H1. inverts H10. inverts* H12.
      eapply Typ_sim; eauto.
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
      unfold not; intros nt; inverts nt. inverts H1.
      exfalso. apply H5. exists*.
    + inverts* H7. inverts H9. 
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
      exfalso. apply H6. exists*.
  - inverts Typ. 
    + inverts H0. inverts H9.
      inverts H11. inverts H0. inverts H3. 
      eapply Typ_sim; eauto.
      apply  Typ_anno; eauto.
      apply Typ_sim with (A := (t_arrow t_int t_int)); eauto.
      eapply Typ_app with (A := (t_arrow t_int (t_arrow t_int t_int))) (A1 := t_int); eauto.
      eapply Typ_sim; eauto.
      apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H0.
      unfold not; intros nt; inverts nt. inverts H0.
    + inverts H6. inverts H8.
      inverts H0. inverts H1. 
      apply  Typ_anno; eauto.
      apply Typ_sim with (A := (t_arrow t_int t_int)); eauto.
      eapply Typ_app with (A := (t_arrow t_int (t_arrow t_int t_int))) (A1 := t_int); eauto.
      eapply Typ_sim; eauto.
      apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H0.
  - inverts Typ. 
    + inverts H0. inverts H9.
      inverts H11. inverts H0. inverts H3. 
      eapply Typ_sim; eauto.
      apply  Typ_anno; eauto.
      apply Typ_sim with (A := t_int); eauto.
      apply Typ_app with (A := ((t_arrow t_int t_int))) (A1 := t_int).
      apply pa_abs; eauto.
      apply Typ_addl; eauto.
      eapply Typ_sim; eauto. apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H0.
      unfold not; intros nt; inverts nt. inverts H0.
    + inverts H6. inverts H8.
      inverts H0. inverts H1. 
      apply  Typ_anno; eauto.
      apply Typ_sim with (A := t_int); eauto.
      apply Typ_app with (A := ((t_arrow t_int t_int))) (A1 := t_int).
      apply pa_abs; eauto.
      apply Typ_addl; eauto.
      eapply Typ_sim; eauto. apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H0.
  -
    inverts Typ. 
    +
    inverts H5. inverts* H3.
    eapply Typ_app; auto.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H1.
    auto.
    +
    inverts H1. inverts H8. inverts H6.
    eapply Typ_sim; eauto.
    eapply Typ_app; auto.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H1.
    auto.
    unfold not; intros nt; inverts nt. inverts H1.
  - inverts Typ. 
    forwards*: TypedReduce_preservation H0.
    inverts H2. 
    forwards*: TypedReduce_preservation H0.
    eapply Typ_sim; eauto.
    forwards*: TypedReduce_nlambda H0.
  - inverts Typ. inverts H. inverts H8.
    eapply Typ_sim;eauto.
    inverts* H5.
  - inverts Typ. 
    + inverts H1. inverts H10. inverts H12. inverts H1. inverts H4.
      eapply Typ_sim; eauto.
      apply Typ_anno;eauto. 
      apply Typ_sim with (A:= B); eauto.
      apply Typ_app with (A := (t_arrow A B)) (A1 := A); eauto.
      apply Typ_sim with (A := A2); eauto.
      apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H1. 
      unfold not; intros nt; inverts nt. inverts H1.
    + inverts H7. inverts H9. inverts H1. inverts H2. 
      apply Typ_anno;eauto. 
      apply Typ_sim with (A:= B); eauto.
      apply Typ_app with (A := (t_arrow A B)) (A1 := A); eauto.
      apply Typ_sim with (A := A1); eauto.
      apply BA_AB; auto.
      unfold not; intros nt; inverts nt. inverts H1.
  -
    inverts Typ.
    +
    forwards*: principle_inf H7.
    rewrite H3 in *. inverts H1.
    inverts H5.
    forwards*: TypedReduce_preservation H2.
    forwards*: TypedReduce_walue H2.
    +
    inverts H3.
    forwards*: principle_inf H10.
    rewrite H3 in *. inverts H1.
    inverts H8.
    forwards*: TypedReduce_preservation H2.
    forwards*: TypedReduce_walue H2.
    eapply Typ_sim; eauto.
    unfold not; intros nt; inverts nt. inverts H7.
  -
    inverts Typ. 
    + inverts H. inverts* H8.
    + inverts* H5.
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


Lemma TypedReduce_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - inverts Typ.
    exists*.
    exists*.
    exfalso. apply H2. exists*.
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
    inverts H5.
    inductions A; eauto.
    exists.
    apply TReduce_blame; eauto.
    unfold not; intros.
    inverts H3.

    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_absd; eauto.
    exists.
    apply TReduce_adyn; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H5.
    split.
    unfold not; intros.
    inverts* H5.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_adyn; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H4.
    split.
    unfold not; intros.
    inverts* H4.
    eauto.

    inductions A; eauto.
    inverts* Val; inverts* H.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_blame; eauto.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    inverts* Val; inverts* H.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    destruct (eq_type A1);
    try solve[ exists;
    apply TReduce_adyn; eauto;
    unfold FLike;
    split;
    unfold not; intros;
    inverts* H7;
    split;
    unfold not; intros;
    inverts* H7;
    eauto].
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_adyn; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H7.
    split.
    unfold not; intros;
    inverts* H7.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H6.
    split.
    unfold not; intros;
    inverts* H6.
    eauto.
    simpl. eauto.
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
    unfold not; intros.
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
    unfold not; intros.
    inverts* H7.
    eauto.
    simpl. eauto.
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
   inverts* H3.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
   try solve[left*].
   left. eapply value_fanno; eauto. reflexivity.
   right; unfold not; intros nt; inverts* nt. inverts* H0.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
   try solve[left*].
   left. eapply value_fanno; eauto. reflexivity.
   right; unfold not; intros nt; inverts* nt. inverts* H0.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
     try solve[left*].
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    destruct(dyn_decidable A0);destruct(dyn_decidable B);subst*;
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
    try solve[left*].
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    right; unfold not; intros nt; inverts* nt. inverts* H5.
    right; unfold not; intros nt; inverts* nt. inverts* H2.
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
    +
    inverts H.
    forwards*: principle_inf Typ1.
    forwards*: TypedReduce_progress Typ2.
    inverts H0.
    inductions x;
    exists*.
    inverts Val1; inverts* Typ1.
    +  inductions e2'.
        assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
        rewrite <- H0.
        exists. apply do_step; eauto.
        assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
        rewrite <- H0.
        exists. apply blame_step; eauto.
    + inductions e1'.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply do_step; eauto.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply blame_step; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress Typ.
      inverts* H.
      destruct(value_decidable (e_anno e A)); eauto. 
    + right.
      induction t'.
      * 
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply do_step; eauto.
      *
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply blame_step; eauto.
  - forwards*: IHTyp Typ.
  - inverts H0;inverts* Typ1; try solve[inverts H1;inverts* Typ2].
    inverts H2; inverts* H3.
Qed.

