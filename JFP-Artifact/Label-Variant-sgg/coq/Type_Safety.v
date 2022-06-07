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

Lemma TypedReduce_trans : forall v v1 v2 A B l1 b1 l2 b2,
    value v -> TypedReduce v l1 b1 A (Expr v1) -> TypedReduce v1 l2 b2 B (Expr v2) -> TypedReduce v l2 b2 B (Expr v2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
Qed.


Lemma TypedReduce_transr : forall v v1  A B l1 b1 l2 b2,
    value v -> TypedReduce v l1 b1 A (Expr v1) -> TypedReduce v1 l2 b2 B (Blame l2 b2) -> TypedReduce v l2 b2 B (Blame l2 b2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
Qed.

Lemma TypedReduce_prv_value: forall v A v' l b,
    value v -> TypedReduce v l b A (Expr v') -> value v'.
Proof.
  introv Val Red.
  inductions Red; try solve[inverts* Val];eauto.
Qed.



Lemma principle_inf2: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

Lemma TypedReduce_preservation: forall v A v' B l b,
    value v -> TypedReduce v l b A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
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
      inverts Typ. inverts H3. inverts H12; try solve[inverts H2].
      eapply Typ_sim; eauto.
      forwards*: principle_inf H3. 
      rewrite H8 in H1; auto.
      forwards*: principle_inf H14. 
      rewrite H3 in H1; auto.
      eapply Typ_sim; eauto.
    *
      inverts* Val; try solve[exfalso; apply H2; auto].
  +
    inverts Typ.
    inverts Lc. inverts H3. 
    inverts* H. 
    inverts* H9. inverts* H.
    destruct(sim_decidable (t_arrow A1 A2) (t_arrow C D)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto. 
    inverts H13.
    inverts H11.
    destruct(sim_decidable (t_arrow A1 A2) (t_arrow C D)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto. 
    inverts H14.
Qed.


Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma TypedReduce_nlam: forall v A v' l b ,
    value v -> TypedReduce v l b A (Expr v') -> nlam v'.
Proof with auto.
 introv val red.
 inductions red; eauto.
Qed.

Lemma TypeLists_preservation3: forall v A1 A2 v' l1 b1 l2 b2 l3 b3,
walue v -> TypeLists v (cons (t_typs A2 l1 b1) (cons (t_typs t_dyn l2 b2) (cons (t_typs A1 l3 b3) nil))) (Expr v') 
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
  inverts H10.
  forwards*: TypedReduce_preservation H0.
  forwards*: TypedReduce_prv_value H0.
  forwards*: TypedReduce_nlam H0.
  forwards*: TypedReduce_preservation H9.
  forwards*: TypedReduce_prv_value H9.
  forwards*: TypedReduce_nlam H9.
  forwards*: TypedReduce_preservation H11.
  inverts H13.
  +
  inverts* H0.
Qed.

Lemma TypeLists_preservation2: forall v A1 A2 v' B l1 b1 l2 b2,
value v -> TypeLists v (cons (t_typs A2 l1 b1) (cons (t_typs A1 l2 b2) nil)) (Expr v') 
     -> Typing nil v Chk B -> Typing nil v' Inf A1.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  - inverts Red.
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_nlam H0.
    forwards*: TypedReduce_preservation H7.
    inverts H9.
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


Lemma principle_inf3: forall w A,
 walue w ->
 Typing nil w Inf A ->
 principal_type w = A.
Proof.
  introv wal typ.
  inductions wal; try solve[inverts* typ].
  forwards*: principle_inf2 typ.
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
    destruct E; unfold simpl_fill in H2; inverts H2.
  - inverts* J.
    destruct E; unfold simpl_fill in H1; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H0.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + forwards*: principle_inf3 Typ1.
      rewrite H0 in H6.
      inverts H6.
      inverts* H.
      eapply Typ_app;eauto.
      eapply Typ_sim;eauto.
      apply sim_refl.
    + inverts Typ1. inverts H.
      eapply Typ_anno.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H2.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypedReduce_preservation H7.
      forwards*: TypedReduce_nlam H7. 
    + inverts Typ1. 
      *
       inverts H9. inverts H0; inverts H.
       inverts H12; try solve[inverts H4].
       forwards*: TypeLists_preservation2 H7.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       inverts H5.
       pick fresh x.
      rewrite (subst_exp_intro x); eauto.
       forwards*: H0.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_nlam H7.
      inverts H14.
      * 
      inverts H. 
      inverts H12;try solve[inverts* H14].
      inverts H9; try solve[inverts* H1].
      inverts H2.
      forwards*: TypeLists_preservation2 H7.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       eapply Typ_sim; eauto.
       eapply Typ_anno; eauto.
       pick fresh x.
      rewrite (subst_exp_intro x); eauto.
       forwards*: H0.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_nlam H7.
    + inverts Typ1. inverts* H.
  - Case "typing_anno".
    inverts* J.
    + inverts* Typ. inverts* H3.
    inverts* H2.
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
    exfalso; apply H8; eauto.
    inverts H7.
  - forwards*: step_nlam J.
Qed.


Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (Expr e') ->
    Typing nil e' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
Qed.

Lemma sfill_appl : forall e1 e2 l b,
  (e_app e1 l b e2) = (simpl_fill (sappCtxL e2 l b) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2 l b,
  (e_app e1 l b e2) = (simpl_fill (sappCtxR e1 l b) e2).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addl : forall e1 e2 l1 b1 l2 b2,
  (e_add e1 l1 b1 e2 l2 b2) = (simpl_fill (saddCtxL l1 b1 e2 l2 b2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addr : forall e1 e2 l1 b1 l2 b2,
  (e_add e1 l1 b1 e2 l2 b2) = (simpl_fill (saddCtxR l1 b1 e1 l2 b2 ) e2).
Proof.
  intros. eauto.
Qed.

Lemma TypedReduce_progress: forall v B A l b,
    value v -> Typing [] v Chk B -> exists r, TypedReduce v l b A r.
Proof.
  introv Val Typ. gen A B.
  inductions Val; intros. 
  - inverts Typ. inverts H. inverts H8. inverts H. 
    destruct (sim_decidable t_int  A0).
    exists.
    apply TReduce_sim; eauto.  
    exists.
    apply TReduce_i; eauto.
    inverts H8.
  -
    destruct A0;try solve[exists*].
Qed.



Lemma blame_same_label: forall v l1 b1 l2 b2 A,
 TypedReduce v l1 b1 A (Blame l2 b2) ->
 l1 = l2 /\ b1 = b2.
Proof.
  introv red.
  inverts* red.
Qed.



Theorem progress : forall e dir T,
    Typing nil e dir T ->
    walue e \/ (exists r, step e r).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right].
  - right. 
    exists*. 
  - Case "var".
    inverts* H0.
  - right. inverts Lc. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    +
      inverts H.
      inverts Val1.
      *
        inverts Val2. inverts H; inverts Typ1;
        try solve[inverts H8;inverts H;inverts H1];
        try solve[inverts H10].

        forwards*: TypedReduce_progress e2 A1 A1 l (negb b). inverts* H.
        destruct x; eauto; try solve[inverts* H3].
        forwards*: TypedReduce_preservation H3.
        forwards*: TypedReduce_prv_value H3.
        forwards*: value_nlam H4.
        forwards*: value_lc H4.
        forwards*: Typing_chk H. inverts H8.
        forwards*: TypedReduce_progress e0 x A l2 (negb b2). inverts H8.
        destruct x0; eauto.
        forwards*: blame_same_label H11.
        inverts* H8. 

        forwards*: TypedReduce_progress e2 A1 A1 l (negb b). inverts* H.
        destruct x; eauto; try solve[inverts* H3].
        forwards*: TypedReduce_preservation H3.
        forwards*: TypedReduce_prv_value H3.
        forwards*: value_nlam H4.
        forwards*: value_lc H4.
        forwards*: Typing_chk H. inverts H8.
        forwards*: TypedReduce_progress e0 x A l2 (negb b2). inverts H8.
        destruct x0; eauto.
        forwards*: blame_same_label H14.
        inverts* H8. 

        forwards*: principle_inf2 Typ1.
      *
        inverts Typ1. inverts Val2; try solve[inverts* Typ2;inverts H5].
        forwards*: TypedReduce_progress t_dyn t_dyn l (negb b) Typ2. inverts* H1.
        destruct x; eauto.
        inverts* H3.
        inverts* H3.
        assert(principal_type (e_abs e) = (t_arrow t_dyn t_dyn ));eauto.
      * inverts Typ1; inverts Val1; try solve[inverts H0]; try solve[inverts H3].
        exists*.
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
      inverts* H4. 
    + assert (lc_exp (e_anno e l b A)); eauto.
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
     inverts Typ2;
      inverts Val2; try solve[inverts H4];
      inverts Val1; try solve[inverts H6];
      try solve[inverts H5].
      inverts H8; inverts H; inverts H0;
      inverts H7; inverts H4; inverts H5;try solve[exists*].
      inverts H2. 
    + inverts Val1; try solve[inverts Typ1; inverts H0].
      rewrite sfill_addr.  destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
      inverts Typ1; try solve[inverts* H4];
      try solve[inverts H0;inverts* H2].
    + rewrite sfill_addl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  - inverts* H0.
  - forwards*: IHTyp Typ.
Qed.
