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


Lemma Cast_value: forall v v' A,
  value v->
  Cast v A (e_exp v') ->
  value v'.
Proof.
  introv Val Red.
  inductions Red; eauto.
  - 
    apply value_dyn; eauto.
    inverts H.
    inverts H1.
    inverts Val; inverts* H2; try solve[ eapply value_fanno; eauto;
    reflexivity].
  - 
    inverts Val. inverts* H2.
    +
    inverts H. inverts H2. inverts* H5.
    rewrite <- H4 in *. inverts H0.
    +
    inverts H. inverts H2. inverts* H5.
  - inverts* Val.
Qed.



Lemma Cast_sim: forall v A r B,
    value v -> Cast v A r -> Typing nil v Inf B -> sim B A.
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


Lemma Cast_preservation: forall v A v',
    value v -> Cast v A (e_exp v') -> Typing nil v Chk A -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  lets Typ: Typ'.
  inductions Red; intros;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  -
    inverts Typ. inverts* H0.
  - 
    apply Typ_anno; eauto.
    inverts Typ. 
    forwards* h1: principle_inf H0.
    rewrite h1 in *; auto.
    inverts H. inverts H3.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); auto.
    apply Typ_anno; eauto.
  -
   inverts* Typ. inverts H1. inverts* H5.
   inverts Val.
   forwards* h1: principle_inf H1.
   rewrite h1 in *; auto.
   apply Typ_anno; eauto.
  -
    inverts Val.
    inverts Typ. inverts H.
    inverts H5.
    forwards* h1: principle_inf H.
    rewrite h1 in *; auto.
Qed.



Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (e_exp e') ->
    Typing nil e' dir A.
Proof.
  introv Typ Red. gen A dir.
  inductions Red; intros.
  - 
    inductions E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H4.
      inverts H0.
      forwards*: IHRed H6.
    + inverts Typ.
      forwards*: IHRed H7.
      inverts H0.
      forwards*: IHRed H7.
    + inverts Typ.
      forwards*: IHRed H5.
      inverts H0.
      forwards*: IHRed H4.
  - 
    inverts Typ.
    + 
    inverts H6. inverts H4.
    pick fresh y.
    apply Typ_anno.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: Cast_preservation H1.
    +
    inverts H2. 
    inverts H8. inverts H6. 
    pick fresh x.
    eapply Typ_sim; eauto.
    apply Typ_anno; eauto.
    rewrite (subst_exp_intro x); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: Cast_preservation H1.
  - 
    inverts Typ. 
    + 
    inverts H7.
    forwards*: Cast_preservation H0.
    +
    inverts H2. 
    forwards*: Cast_preservation H0.
  - inverts Typ. 
    +
    inverts H5. inverts H3.
    forwards*: Cast_preservation H0.
    +
    inverts H1. inverts H7. inverts H5. 
    eapply Typ_sim;eauto.
  - 
    inverts Typ. 
    +
    inverts H5. inverts H3.
    forwards*: Cast_preservation H0.
    +
    inverts H1. inverts H7. inverts H5.
    eapply Typ_sim; eauto.
  - 
    inverts Typ. 
    +
    inverts H7. inverts H5.
    forwards* h1: Cast_preservation H0.
    inverts H6. 
    forwards* h2: principle_inf H3.
    rewrite H2 in *. inverts h2.
    inverts H4.
    eapply Typ_anno; auto.
    eapply Typ_sim with (A := B); auto.
    eapply Typ_app; eauto.
    +
    inverts H3. inverts H9. inverts H7.
    forwards* h1: Cast_preservation H0.
    inverts H6. 
    forwards* h2: principle_inf H3.
    rewrite H2 in *. inverts h2.
    inverts H5.
    eapply Typ_sim with (A := A1); auto.
    eapply Typ_anno; auto.
    eapply Typ_sim with (A := B); auto.
    eapply Typ_app; eauto.
  -
    inverts Typ.
    +
    inverts H4. inverts* H2.
    +
    inverts H0. inverts H6.
    inverts H4.
    eapply Typ_sim;eauto.
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


Lemma Cast_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, Cast v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - 
    inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
  - 
    inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply Cast_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - 
    inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply Cast_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - 
    inverts Typ.
    inverts H0.
    inductions A; inverts H1; eauto.
    destruct (eq_type t1).
    destruct (eq_type t2).
    subst*.
    exists.
    apply Cast_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H2.
    split.
    unfold not; intros H3;
    inverts* H3.
    eauto.
    exists.
    apply Cast_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H1.
    split.
    unfold not; intros H3;
    inverts* H3.
    eauto.
  - 
    inverts Typ.
    inverts H0.
    inverts H4.
    forwards* h1: principle_inf H0.
    rewrite h1 in *.
    inverts H. 
    inverts H1.
    +
    exists. 
    eapply Cast_abs with (C := A) (D := B); simpl; eauto.
    +
    destruct (eq_type A).
    destruct (eq_type B).
    *
    subst.
    exists.
    apply Cast_v; eauto.
    *
    exists.
    apply Cast_anyd; eauto.
    unfold FLike; simpl in *.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    *
    exists.
    apply Cast_anyd; eauto.
    unfold FLike; simpl in *.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
  -
    inverts Val; simpl in *; inverts* H.   
    + 
    inductions A; eauto.
    *
    exists*.
    eapply Cast_vany; eauto.
    * 
    exists.
    apply Cast_blame; eauto.
    unfold not; intros nt.
    inverts nt.
    +
    inductions A; eauto.
    *
    exists.
    apply Cast_blame; eauto.
    unfold not; intros nt.
    inverts nt.
    *
    destruct (eq_type A1).
    destruct (eq_type A2).
    --
    subst.
    exists.
    apply Cast_vany; eauto.
    --
    exists.
    apply Cast_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    --
    exists.
    apply Cast_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    +
    inductions A; eauto.
    *
    exists.
    apply Cast_blame; eauto.
    unfold not; intros nt.
    inverts nt.
    *
    destruct (eq_type A1).
    destruct (eq_type A2).
    --
    subst.
    exists.
    apply Cast_vany; eauto.
    --
    exists.
    apply Cast_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    --
    exists.
    apply Cast_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    *
    forwards*: value_lc H0.
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
  - 
    inductions H; try solve[right; unfold not; intros nt; inverts* nt];
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
      left. eapply value_fanno; eauto. reflexivity.
      destruct(dyn_decidable t1);destruct(dyn_decidable t2);subst*;
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H2];
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
      try solve[left*].
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
      try solve[left*].
      *
      left. eapply value_fanno; eauto. reflexivity.
      *
      destruct(dyn_decidable A0);destruct(dyn_decidable B);subst*;
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
      try solve[left*].
    +
    right; unfold not; intros nt; inverts* nt; inverts* H3. inverts H4.
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
  - (* app *)
    right. inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts* Val1; inverts* H3 ];
    try solve[inverts* H]; inverts* H.
    + forwards*: Cast_progress Typ2.
      inverts* H.
      inductions x; try solve[exists*].
      exists. 
      eapply Step_betap; simpl in *;auto.
    + 
      forwards*: Cast_progress Typ2.
      inverts H.
      inductions x.
      *
      inverts Typ2.
      inverts* Val2; try solve [inverts* H; inverts H4].
      inverts* H1. 
      -- 
      inverts H9. inverts H7.
      inverts H9. 
      -- 
      inverts H6; inverts* H9.
      exists. eapply Step_add; eauto.
      apply Cast_vany; eauto.
      *
      exists.
      eapply Step_betap; simpl in *;auto.
    + 
      forwards*: Cast_progress Typ2.
      inverts H.
      inductions x.
      *
      inverts Typ2.
      inverts* Val2; try solve [inverts* H; inverts H4].
      inverts* H1. 
      -- 
      inverts H9. inverts H7.
      inverts H9. 
      -- 
      inverts H6; inverts* H9.
      exists. eapply Step_addl; eauto.
      apply Cast_vany; eauto.
      *
      exists.
      eapply Step_betap; simpl in *;auto.
    +
      forwards*: Cast_progress Typ2.
      inverts H.
      inverts Val1.
      inductions x; try solve[exists*].
      *
      exists.
      eapply Step_betap; simpl in *;eauto.
    + 
      inverts* H.
      *
      forwards*: principle_inf Typ1.
       inductions e2'.
       assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
       rewrite <- H0.
       exists. apply Step_eval; eauto.
       assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
       rewrite <- H0.
       exists. apply Step_blame; eauto.
       *
       inverts Val1;inverts* Typ1.
    + inductions e1'.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply Step_eval; eauto.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply Step_blame; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: Cast_progress Typ.
      inverts* H.
      destruct(value_decidable (e_anno e A)); eauto. 
    + right.
      induction t'.
      * 
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply Step_eval; eauto.
      *
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply Step_blame; eauto.
  - forwards*: IHTyp Typ.
Qed.
