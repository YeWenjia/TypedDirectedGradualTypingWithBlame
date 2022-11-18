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


Lemma sval_decidable: forall s,
 lc_exp s -> sval s \/ not (sval s).
Proof.
  introv lc.
  inductions lc; 
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  inverts IHlc.
  inverts* H;right; unfold not; intros nt; inverts nt.
  inductions lc;
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  inductions A;
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
Qed.


Lemma ssval_decidable: forall s,
 lc_exp s -> ssval s \/ not (ssval s).
Proof.
  introv lc.
  inductions lc; 
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  inverts IHlc.
  inverts* H;right; unfold not; intros nt; inverts nt.
  inductions lc;
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  inductions A;
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  inverts IHlc1;
  try solve[try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*]];
  try solve[inverts IHlc2;
  try solve[try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*]]
  ];
  try solve[
  inverts IHlc2;
  try solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*]].
Qed.


Lemma value_decidable: forall v,
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc. inductions v; eauto;
  try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. 
    forwards*: ssval_decidable H0.
    inverts* H;
      try solve [right; unfold not; intros nt; inverts* nt];
      inductions v; eauto;
      try solve[left*].
Qed.



Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B (Expr v2) -> TypedReduce v B (Expr v2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  inductions Red1;
    introv Red2;try solve[inverts Val];eauto.
  - inverts* Red2. 
Qed.


Lemma TypedReduce_transr : forall v v1 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B Blame -> TypedReduce v B Blame.
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B.
  inductions Red1;
    introv Red2; try solve[inverts Val];eauto.
  - inverts* Red2. 
Qed.


Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red; try solve[inverts Val];eauto.
Qed.


Lemma principle_inf2: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.


Lemma principle_inf4: forall v A,
  ssval v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
  inverts* Typ; simpl in *.
  forwards*: IHVal1.
  forwards*: IHVal2.
  rewrite H.
  rewrite H0.
  auto.
Qed.


Lemma TypedReduce_nlam: forall v A v',
    walue v -> TypedReduce v A (Expr v') -> nlam v'.
Proof with auto.
 introv val red.
 inductions red; eauto.
Qed.


Lemma TypeLists_preservation3: forall v A1 A2 v',
 value v -> TypeLists v (cons A2 (cons t_dyn (cons A1 nil))) (Expr v') 
     -> Typing nil v Chk A2 -> Typing nil v' Inf A1.
Proof with auto.
  introv Val Red Typ.
  lets Red': Red.
  inductions Red; 
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  - inverts Val.
    +
    inverts Red.
    inverts H8.
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_nlam H0.
    forwards*: TypedReduce_preservation H6.
    forwards*: TypedReduce_prv_value H6.
    forwards*: TypedReduce_nlam H6.
    forwards*: TypedReduce_preservation H9.
    inverts H11.
Qed.

Lemma TypeLists_preservation2: forall v A1 A2 v',
 walue v -> TypeLists v (cons A2 (cons A1 nil)) (Expr v') 
     -> Typing nil v Chk A2 -> Typing nil v' Inf A1.
Proof with auto.
  introv Val Red Typ.
  lets Red': Red.
  inductions Red; 
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  - inverts Val.
    +
    inverts Red.
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_nlam H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_preservation H6.
    inverts H8.
    +
    inverts H0.
Qed.


Lemma step_nlam: forall e e',
 nlam e ->
 step e (Expr e') ->
 nlam e'.
Proof.
  introv nlam red.
  inductions red;eauto.
  - destruct E; unfold simpl_fill; eauto.
  -  forwards*: TypedReduce_nlam H0.
Qed.


Lemma TypeLists_nlam: forall v A1 A2 v',
 walue v -> TypeLists v (cons A2 (cons A1 nil)) (Expr v') 
     -> nlam v'.
Proof with auto.
 introv wal tlist.
 inverts* wal.
 -
   inverts* tlist. inverts H6; try solve[inverts* H9].
   forwards*: TypedReduce_nlam H4.
   forwards*: TypedReduce_prv_value H4.
   forwards*: TypedReduce_nlam H7.
 -
   inverts* tlist; try solve[inverts* H4].
Qed.

Lemma principle_inf3: forall w A,
 walue w ->
 Typing nil w Inf A ->
 principal_type w = A.
Proof.
  introv wal typ.
  inductions wal; try solve[inverts* typ].
  forwards*: principle_inf2 typ.
Qed.


Lemma ssval_nlam: forall ss,
  ssval ss ->
  nlam ss.
Proof.
  introv sval.
  inductions sval; eauto.
Qed.

Hint Resolve ssval_nlam: core. 



Lemma erase_pvalue: forall e,
 walue e ->
 ssval (erase e).
Proof.
  introv wal.
  forwards* lc:walue_lc wal.
  inverts* wal; simpl in *; eauto.
  inverts* H.
Qed.


Lemma erase_prv: forall e A,
Typing nil e Chk A -> 
 walue e ->
 sim (principal_type (erase e)) (principal_type e).
Proof.
  introv typ wal.
  inverts* wal; simpl in *; eauto.
  -
  inverts* H; simpl in *.
  inverts typ. inverts H.
  inverts H5; try solve[inverts H0].
  forwards*: principle_inf4 H.
  rewrite H5; auto.
Qed.


Lemma erase_prv2: forall e A,
walue e ->
Typing nil e Inf A -> 
exists B, Typing nil (erase e) Inf B.
Proof.
  introv wal typ.
  inverts* wal; simpl in *; eauto.
  -
  inverts* H; simpl in *.
  inverts typ. inverts* H2.
  inverts* H0.
  -
  inverts* typ.
Qed.



Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (Expr e') ->
    Typing nil e' dir A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J]; introv J.
  - inverts J.
    apply Typ_anno; eauto.
    destruct E; unfold simpl_fill in H0; inverts H0.
  - inverts H0.
  - inverts J.
    destruct E; unfold simpl_fill in H2; inverts H2.
  - inverts J.
    destruct E; unfold simpl_fill in *; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H0.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + forwards*: principle_inf3 Typ1.
      rewrite H0 in *.
      forwards*: pattern_abs_uniq H H5.
      inverts* H1.
      eapply Typ_app;eauto.
      eapply Typ_sim;eauto.
      apply sim_refl.
    + inverts Typ1. 
      forwards*: pattern_abs_uniq H H6.
      inverts H0.
      eapply Typ_anno.
      inverts H2. inverts H0. 
      inverts H9; try solve[inverts H8].
      inverts H10.
      inverts H6. 
      inverts H1. inverts H.
      pick fresh x. forwards*: H2 x.
      rewrite (subst_exp_intro x); eauto.
      eapply Typ_sim; eauto.
      eapply Typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_preservation2 H5.
      forwards*: TypeLists_nlam H5.
      pick fresh x. forwards*: H2 x.
      rewrite (subst_exp_intro x); eauto.
      eapply Typ_sim with (A:= A2); eauto.
      eapply Typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_preservation2 H5.
      forwards*: TypeLists_nlam H5.
    +
      inverts Typ1. inverts H.
      forwards*: TypedReduce_preservation H5.
      pick fresh x. forwards*: H2 x.
      rewrite (subst_exp_intro x); eauto.
      eapply Typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypedReduce_nlam H5.
  - Case "typing_anno".
    inverts* J.
    + inverts* Typ. inverts* H3.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       apply sim_refl.
      inverts* H2.
    + inverts* Typ. inverts* H3.
      inverts H2. 
    + destruct E; unfold simpl_fill in *; inverts H.
    + eapply TypedReduce_preservation; eauto.
  - inverts* J.
    destruct E; unfold simpl_fill in *; inverts H.
    forwards*: IHTyp1 Typ1.
    forwards*: IHTyp2 Typ2.
  -
    forwards*: IHTyp J.
    forwards*: step_nlam J.
  -
    inverts* J.
    +
    forwards* h1: principle_inf3 Typ1.
    forwards* h2: principle_inf3 Typ2.
    rewrite h1 in *. rewrite h2 in *.
    eapply Typ_anno; eauto.
    rewrite <- h1 in *. rewrite <- h2 in *.
    forwards* h5: Typing_chk Typ1. inverts h5.
    forwards* h6: Typing_chk Typ2. inverts h6.
    forwards* h3: erase_prv H2.
    forwards* h33: erase_prv H3.
    forwards* h7: erase_prv2 Typ1.
    forwards* h8: erase_prv2 Typ2.
    inverts h7. inverts h8.
    forwards* h9: erase_pvalue H2.
    forwards* h10: erase_pvalue H3.
    forwards* h11: principle_inf4 H1.
    forwards* h12: principle_inf4 H4.
    rewrite h11 in *.
    rewrite h12 in *.
    eapply Typ_sim;eauto.
    +
    destruct E; unfold simpl_fill in *; inverts H.
    forwards*: IHTyp1 Typ1.
    forwards*: IHTyp2 Typ2.
  -
    inverts* J.
    +
    destruct E; unfold simpl_fill in *; inverts H0.
    forwards*: IHTyp Typ.
    +
    inverts Typ.
    forwards*: pattern_pro_uniq H H3. inverts* H0.
    inverts H4. inverts* H0.
    inverts H1; inverts H3.
    *
    inverts H2.
    inverts* H1.
    *
    inverts H2.
    inverts* H1.
  -
    inverts* J.
    +
    destruct E; unfold simpl_fill in *; inverts H0.
    forwards*: IHTyp Typ.
    +
    inverts Typ.
    forwards*: pattern_pro_uniq H H3. inverts* H0.
    inverts H4. inverts* H0.
    inverts H1; inverts H3.
    *
    inverts H2.
    inverts* H1.
    *
    inverts H2.
    inverts* H1.
Qed.


Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (Expr e') ->
    Typing nil e' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ.
  lets*: preservation Typ.
Qed.



Lemma TypedReduce_Progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  destruct (sim_decidable (principal_type s) A0); eauto.
Qed.


Lemma TypedReduce_progress: forall v A B,
    value v -> Typing [] v Chk B -> exists r, TypedReduce v A r.
Proof.
  introv Val Typ. gen A B.
  inductions Val; intros. 
  destruct (sim_decidable (principal_type s) A0); eauto.
Qed.


Lemma int_decidable: forall A,
 (A = t_int) \/ not(A = t_int).
Proof.
  introv.
  inductions A; try solve[right; unfold not; intros nt; inverts* nt];eauto.
Qed.



Lemma abs_nlam: forall e,
 nlam (e_abs e) ->
 False .
Proof.
  introv nt.
  inverts* nt.
Qed.

Theorem progress : forall e dir T,
    Typing nil e dir T ->
    walue e \/ (exists r, step e r).
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
      inverts Val1; try solve[inverts Typ1].
      inverts* Val2;
      try solve[forwards*: principle_inf2 Typ1].
      *
        forwards* h1: Typing_chk Typ1. inverts h1.
        forwards*: TypedReduce_progress e1 (t_arrow t_dyn t_dyn).
        inverts H5.
        destruct x0; eauto.
        inverts H0.
        inverts H6.
        inverts H11; inverts H12.
        inverts Typ1. inverts H8. inverts H6.
        inverts H14; try solve[inverts H12].
        inverts H15.
        forwards*: TypedReduce_progress A1 Typ2. inverts* H6.
        destruct x0; eauto.
        forwards*: TypedReduce_preservation H12.
        forwards*: TypedReduce_prv_value H12.
        forwards*: value_lc H14.
        forwards* h2: Typing_chk H6. inverts h2.
        forwards*: TypedReduce_progress e0 A4. inverts H17.
        destruct x1; eauto.
        exists. eapply Step_beta; eauto.
        exists. eapply Step_betap; eauto.
      *
      inverts* Typ1. inverts H.
      inverts* Val2.
      forwards*: TypedReduce_progress e2 t_dyn. inverts* H1.
      destruct x; eauto.
      inverts* H4.
      exists. eapply Step_absr; simpl;eauto.
    +
      rewrite sfill_appr.  
      destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
    + 
      rewrite sfill_appl. 
      destruct e1'. 
      * exists.
      apply do_step; eauto.
      * 
      exists. apply blame_step; eauto.
  -  Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      inverts Val.
      forwards*: TypedReduce_progress H.
      inverts H1.
      right. 
      exists. apply Step_annov; eauto.
      inverts* Typ; try solve[inverts* H3];
      try solve[inverts H4].
      inverts* H4.
    + assert (lc_exp (e_anno e A)); eauto.
      forwards*: value_decidable H. inverts H1.
      left. auto.
      right. inductions t'. 
      exists. apply Step_anno; eauto. 
      exists. apply Step_annob; eauto.
  - right. inverts Lc. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts Val1 ].
    + inverts H0.
    + 
      inverts Typ2; try solve[inverts H5].
      inverts Val2; try solve[inverts H4;inverts H5];
      inverts Val1; try solve[inverts H;inverts H0].
      forwards* h1: TypedReduce_progress e1 t_int.
      inverts h1. destruct x; eauto.
      inverts H8; inverts H9.
      inverts H15; inverts* H16.
      forwards*: TypedReduce_progress e2 t_int.
      inverts H8. destruct x; eauto.
      inverts H9.
      inverts H12; inverts* H16.
    + 
      inverts Val1; try solve[inverts Typ1; inverts H0].
      rewrite sfill_addr.  destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
      inverts Typ1. inverts H5.
      inverts H4.
    + rewrite sfill_addl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  - 
    forwards*: IHTyp Typ.
  -
    inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    +
    inverts* Val1.
    right.
    rewrite sfill_pror. destruct e2'. 
    exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
    right.
    rewrite sfill_pror. destruct e2'. 
    exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
    +
    right.
    rewrite sfill_prol. destruct e1'. 
    exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
  -
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    +
    inverts Val; try solve[inverts Typ;inverts H].
    inverts H0.
    forwards*: TypedReduce_progress (e_anno s A0) (t_pro t_dyn t_dyn).
    inverts H0.
    destruct x; eauto.
    inverts H3; inverts H8;inverts* H9.
    inverts* Typ.
    inverts* Typ.
    +
    right.
    rewrite sfill_l. destruct t'. exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
  -
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    +
    inverts* Val; try solve[inverts Typ;inverts H].
    inverts H0.
    forwards*: TypedReduce_progress (e_anno s A0) (t_pro t_dyn t_dyn).
    inverts H0.
    destruct x; eauto.
    inverts H3; inverts H8;inverts* H9.
    inverts* Typ.
    inverts* Typ.
    +
    right.
    rewrite sfill_r. destruct t'. exists.
    apply do_step; eauto. exists. apply blame_step; eauto.
Qed.
    
      