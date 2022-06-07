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


Lemma value_decidable: forall v,
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc. inductions v; eauto;
  try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. forwards*: IHv. inverts H.
    + inverts H1;try solve [right; unfold not; intros nt; inverts nt].
    + inductions v; eauto;
      try solve [right; unfold not; intros nt; inverts nt].
      inductions v; eauto;
      try solve[left*];
      try solve [right; unfold not; intros nt; inverts nt].
      inductions A;
      try solve[invert H0;left*];
      try solve [right; unfold not; intros nt; inverts nt]. 
Qed.



Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B (Expr v2) -> TypedReduce v B (Expr v2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
Qed.


Lemma TypedReduce_transr : forall v v1 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B Blame -> TypedReduce v B Blame.
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
Qed.


Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red; eauto.
  - inverts* Val.
  - inverts Val; inverts* H.
Qed.


Lemma principle_inf2: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

Lemma TypedReduce_preservation: forall v A v' B,
    value v -> TypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  + destruct(lambda_decidable e).
    *
      apply Typ_anno; eauto.
      inverts Typ. inverts H3. inverts H8; try solve[inverts H2].
      eapply Typ_sim; eauto.
      forwards*: principle_inf H3. 
      rewrite H8 in H1; auto.
      forwards*: principle_inf H11. 
      rewrite H3 in H1; auto.
      eapply Typ_sim; eauto.
    *
      inverts* Val; try solve[exfalso; apply H2; auto].
  +
    inverts H.
    inverts Typ. inverts* H. 
    inverts* H5. inverts* H.
    destruct(sim_decidable (t_arrow A0 B1) (t_arrow C D)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto. 
    inverts H10.
    inverts H8.
    destruct(sim_decidable (t_arrow A0 B1) (t_arrow C D)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto. 
    inverts H11.
Qed.


Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma TypedReduce_nlam: forall v A v',
    value v -> TypedReduce v A (Expr v') -> nlam v'.
Proof with auto.
 introv val red.
 inductions red; eauto.
Qed.


Lemma TypeLists_preservation3: forall v A1 A2 v',
 walue v -> TypeLists v (cons A2 (cons t_dyn (cons A1 nil))) (Expr v') 
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
    +
    inverts* H0.
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
    inverts* H0.
  -
    destruct A1; try solve[exfalso; apply H; eauto].
    destruct(sim_decidable (t_arrow t1 t2) (t_arrow A1_1 A1_2)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto.
    eapply Typ_anno; eauto.
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
    destruct E; unfold simpl_fill in H1; inverts H1.
  - inverts* J.
    destruct E; unfold simpl_fill in H1; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + inverts Typ1.
      eapply Typ_anno.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H6.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypedReduce_preservation H4.
      forwards*: TypedReduce_nlam H4.
    +
      inverts Typ1. 
      *
       inverts H6. inverts H; try solve[inverts H10].
       forwards*: TypeLists_preservation2 H4.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       inverts H7; try solve[inverts H8].
       pick fresh x.
      rewrite (subst_exp_intro x); eauto.
       forwards*: H10.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_nlam H4.
      * 
      inverts H10;try solve[inverts* H7]. inverts H1; try solve[inverts H5].
      forwards*: TypeLists_preservation2 H4.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       pick fresh x.
      rewrite (subst_exp_intro x); eauto.
       forwards*: H7.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_nlam H4.
  - Case "typing_anno".
    inverts* J.
    + apply Typ_anno. eapply Typ_sim; eauto. apply sim_refl.
    + destruct E; unfold simpl_fill in *; inverts H.
    + eapply TypedReduce_preservation; eauto.
  - inverts* J.
    destruct E; unfold simpl_fill in *; inverts H.
    forwards*: IHTyp1 Typ1.
    forwards*: IHTyp2 Typ2.
  - inverts H0.
    inverts* J.
    destruct E; unfold simpl_fill in H0; inverts H0.
    exfalso; apply H6; eauto.
    inverts H4.
  - forwards*: step_nlam J.
Qed.

Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (Expr e') ->
    Typing nil e' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ.
Qed.

Lemma sfill_appl : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addl : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addr : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma TypedReduce_Progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ. inverts H. inverts H4. inverts H. 
    destruct (sim_decidable t_int  A0).
    exists.
    apply TReduce_sim; eauto.  
    exists.
    apply TReduce_i; eauto.
    inverts H5.
  -
    destruct A0;try solve[exists*].
Qed.


Lemma TypedReduce_progress: forall v A B,
    value v -> Typing [] v Chk B -> exists r, TypedReduce v A r.
Proof.
  introv Val Typ. gen A B.
  inductions Val; intros. 
  - inverts Typ. inverts H. inverts H4. inverts H. 
    destruct (sim_decidable t_int  A0).
    exists*. exists*.
    inverts H5.
  -
    destruct A0;try solve[exists*].
Qed.


Lemma vval_dec: forall v,
  value v -> 
  (vvalue v) \/ ~(vvalue v).
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma int_decidable: forall A,
 (A = t_int) \/ not(A = t_int).
Proof.
  introv.
  inductions A; try solve[right; unfold not; intros nt; inverts* nt];eauto.
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
      inverts Val1.
      *
        inverts Val2. inverts H; inverts Typ1;
        try solve[inverts H4;inverts H;inverts H3];
        try solve[inverts H8].
        forwards*: TypedReduce_progress A Typ2. inverts* H.
        destruct x; eauto.
        forwards*: TypedReduce_preservation H4.
        forwards*: TypedReduce_prv_value H4.
        forwards*: value_nlam H6.
        forwards*: value_lc H6.
        forwards*: TypedReduce_progress e0 A0. inverts H9.
        destruct x; eauto.
        forwards*: TypedReduce_prv_value H10.
        forwards*: value_lc H9.
        exists*. exists*.

        forwards*: TypedReduce_progress A Typ2. inverts* H.
        destruct x; eauto.
        forwards*: TypedReduce_preservation H4.
        forwards*: TypedReduce_prv_value H4.
        forwards*: value_nlam H5.
        forwards*: value_lc H5.
        forwards*: TypedReduce_progress e0 A0. inverts H12.
        destruct x; eauto.
        forwards*: TypedReduce_preservation H13.
        forwards*: TypedReduce_prv_value H13.
        forwards*: value_lc H14.
        forwards*: value_nlam H14.
        exists*. exists*.

        inverts H; inverts Typ1; try solve[inverts H4;inverts H;inverts H3];
        try solve[inverts H8];
        inverts* Typ2; try solve[inverts H5]; try solve[inverts* H6].
        destruct(int_decidable A0); try solve[inverts* H].
        exists*.
        destruct(int_decidable A0); try solve[inverts* H].
        exists*.
      *
        inverts Typ1. inverts Val2; try solve[inverts* Typ2;inverts H5].
        forwards*: TypedReduce_progress t_dyn Typ2. inverts* H3.
        destruct x; eauto.
        inverts* H4.
    +
      inverts Val1; try solve[inverts Typ1]. 
      rewrite sfill_appr.  
      destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
      rewrite sfill_appr.  
      destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
    + 
      rewrite sfill_appl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  -  Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      inverts Val.
      forwards*: TypedReduce_progress H.
      inverts H1.
      right. 
      exists. apply Step_annov; eauto.
      inverts* Typ; try solve[inverts H3]. 
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
    + inverts Typ2.
      inverts Val2; try solve[inverts H3].
      inverts Val1; try solve[inverts H6].
      inverts H7; inverts H; inverts H0;
      inverts H8; inverts H4; inverts H5;try solve[exists*].
      inverts H3. inverts H6.
    + inverts Val1; try solve[inverts Typ1; inverts H0].
      rewrite sfill_addr.  destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
      inverts Typ1. inverts H4.
    + rewrite sfill_addl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  - inverts* H0.
  - 
    forwards*: IHTyp Typ.
Qed.
    
      