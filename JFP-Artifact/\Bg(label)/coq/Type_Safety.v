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
 walue v \/ (exists e' l b, v = (e_abs e' l b)) .
Proof.
  introv val.
  inductions val; try solve[left*];eauto.
  - left.
    inverts* IHval.
    inverts* H0. inverts H1. inverts* H0.
  - inverts* IHval. inverts* H0.
    inverts* H1. inverts* H0.
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
    eapply value_fanno; eauto.
    reflexivity.
    eapply value_fanno; eauto.
    reflexivity.
  - inverts Val. inverts* H2.
    inverts H. inverts H1. inverts* H2.
    eapply value_fanno; eauto. reflexivity.
  - inverts Val. inverts* H1.
  - inverts Val.
    inverts H.
    inverts H3.
    inverts* H5.
    inverts* H0.
    rewrite <- H5 in H4.
    inverts H4.
  -
    invert* Val.
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


Lemma abs_nlam: forall e l b,
 nlam(e_abs e l b) ->
 False.
Proof.
  introv nt;inverts nt.
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
  + inverts Typ; try solve[inverts* H].
    inverts Val; inverts* H. inverts H4.
    inverts H5.  inverts H0.
    apply Typ_anno; eauto.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); eauto.
    apply Typ_anno; eauto.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); eauto.
    apply Typ_anno; eauto.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); eauto.
  +
    apply Typ_anno; eauto.
    inverts H. inverts H1.
    inverts Typ. inverts H1.
    inverts H11.
    apply Typ_sim with (A:= (t_arrow t_dyn t_dyn)); auto;
    try solve[unfold not; intros nt; inverts* nt; inverts H1].
    apply Typ_anno; eauto.
    apply BA_AB; auto.
    inverts H6.
  + apply Typ_anno; eauto.
    inverts Typ. inverts H.
    inverts* H8; try solve[forwards*: abs_nlam].
  +
    apply Typ_anno; eauto.
    inverts Typ. inverts H2. inverts* H11;try solve[forwards*: abs_nlam].
    eapply Typ_sim; eauto.
    inverts Val.
    forwards*: principle_inf H2.
    rewrite H7 in H0; auto.
  + inverts* Typ. inverts H0. inverts* H9.
    inverts Val.  
    forwards*: principle_inf H0.
    rewrite H5 in *; auto.
Qed.


Lemma TypedReduce_nlambda: forall v A v' p b ,
    value v -> Typing nil v Chk A -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
Qed.


(* Lemma TypedReduce_nlambda2: forall v t A B v' p b,
    value v -> typing nil v (Chk2 p b B) A t -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
Qed. *)

Lemma TypedReduce_nlambda2: forall v t A v' p b,
    value v -> typing nil v (Chk3 p b) A t -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
Qed.



Lemma TypedReduce_walue: forall v A v' l b ,
    value v -> Typing nil v Chk A -> TypedReduce v l b A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: TypedReduce_nlambda red.
 inverts* H1. inverts H2. inverts* H1.
 inverts* H0.
Qed.


Lemma walue_nlam: forall v,
 walue v ->
 nlam v.
Proof.
  introv wal.
  inverts* wal.
Qed.

Lemma walue_nlam2:forall v,
 walue v ->
 not(exists e' l b, v = (e_abs e' l b)) .
Proof.
  introv val.
  inductions val; try solve[unfold not; intros nt ; inverts nt; inverts H0;inverts H1;
  inverts H0];
  try solve[unfold not; intros nt ; inverts nt; inverts H;inverts H0;inverts H].
Qed.


Hint Resolve walue_nlam walue_nlam2:core.




(* Lemma TypedReduce_walue2: forall v A B v' t p b,
    value v -> typing nil v (Chk2 p b B) A t -> TypedReduce v p b A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: TypedReduce_nlambda2 red.
 inverts* H1. inverts H0.
Qed. *)


Lemma TypedReduce_walue2: forall v A v' t p b,
    value v -> typing nil v (Chk3 p b) A t -> TypedReduce v p b A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: TypedReduce_nlambda2 red.
 inverts* H1. inverts H2. inverts H1. inverts H0.
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
    forwards*: IHRed H8.
    inverts H0.
    forwards*: IHRed H10.
  + inverts Typ.
    forwards*: IHRed H9.
    inverts H0.
    forwards*: IHRed H11.
  + inverts Typ.
    forwards*: IHRed H7.
    inverts H0.
    forwards*: IHRed H9.
  + inverts Typ. 
    inverts H0.
    forwards*: IHRed H5.
    forwards*: IHRed H2.
  + 
    inverts Typ. 
    inverts H0.
    forwards*: IHRed H7.
    forwards*: step_not_nlam Red.
    forwards*: IHRed H4.
    forwards*: step_not_nlam Red.
  - 
    inverts Typ.
    + inverts* H1. inverts H6. inverts* H5; try solve[forwards*: abs_nlam]. 
      eapply Typ_sim; eauto.
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
    + inverts* H3. inverts H4;try solve[forwards*: abs_nlam]. 
      apply Typ_anno; eauto.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply typing_c_subst_simpl; eauto.
  - inverts Typ. 
    forwards*: TypedReduce_preservation H0.
    inverts H2. 
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_nlambda H0.
  - inverts Typ. 
    + inverts H3. inverts H8. inverts H7;try solve[forwards*: abs_nlam].
      inverts H;try solve[forwards*: abs_nlam]. 
      eapply Typ_sim; eauto.
      apply Typ_anno;eauto.
      forwards*: principle_inf H3. rewrite H in *. subst.
      inverts H6. 
      apply Typ_sim with (A:= D); eauto.
    + inverts H5. inverts H6; try solve[forwards*: abs_nlam]. inverts H;
      try solve[forwards*: abs_nlam]. 
       forwards*: principle_inf H3. rewrite H in *. subst.
       inverts H4.
      apply Typ_anno;eauto. 
  -
    inverts Typ.
    +
    forwards*: principle_inf H11.
    rewrite H3 in *. inverts H1.
    inverts H10.
    forwards*: TypedReduce_preservation H2.
    forwards*: TypedReduce_walue H2.
    +
    inverts H3.
    forwards*: principle_inf H13.
    rewrite H3 in *. inverts H1.
    inverts H10.
    forwards*: TypedReduce_preservation H2.
    forwards*: TypedReduce_walue H2.
  -
    inverts Typ. 
    + inverts H. inverts* H9.
      inverts* H8.
    + inverts* H1. inverts* H11.
      inverts* H8.
      apply Typ_sim with (A:=t_dyn); eauto.
  -
    inverts Typ.
    + 
    inverts H. inverts* H4.
    +
    inverts* H1.
  -
     inverts Typ.
    + 
    inverts H. inverts* H4.
    +
    inverts* H1.
  -
    inverts Typ. 
    +
    inverts* H1. inverts* H6.
    eapply Typ_sim;eauto.
    eapply Typ_anno;eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    +
    inverts H3.
    eapply Typ_anno;eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
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


Theorem preservation_multi_step2 : forall t t' dir  T,
    Typing nil t dir T ->
    ssteps t (e_exp t') ->
    Typing nil t' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
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
    apply BA_AB in H.
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
    apply BA_AB in H5; auto.
    right.
    unfold not; 
    intros.
    inverts* H1.
Qed.




Lemma value_tred_keep: forall v r A l b,
Typing nil v Chk A ->
value (e_anno v l b A) ->
TypedReduce v l b A r ->
r = (e_exp (e_anno v l b A)).
Proof.
 introv typ val red.
 inverts* val; simpl in *.
 -
 inverts* typ; simpl in *; subst.
 inverts* H4.
 inverts* red.
 forwards*: principle_inf H.
 rewrite <- H3 in *.
 subst*.
 rewrite <- H4 in *.
 inverts* red; try solve[simpl in *; inverts* H].
 -
 inverts* red; simpl in *; inverts* H1.
 rewrite <- H2 in *. inverts* H. inverts* H1.
 inverts* H3.
 rewrite <- H2 in *. inverts* H. 
Qed.


Lemma value_tred_keep2: forall v r A l b,
value (e_anno v l b A) ->
TypedReduce v l b A r ->
r = (e_exp (e_anno v l b A)).
Proof.
 introv val red.
 inverts* val; simpl in *.
 -
 inverts* red; try solve[inverts H4].
 -
 inverts* red; try solve[inverts H1].
 forwards*: flike_not_ground H.
Qed.

Lemma TypedReduce_progress: forall v p b A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v p b A r.
Proof.
  introv Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
  - inverts* Typ;try solve[forwards*:abs_nlam].
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
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt;
    inverts* nt.
    eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt;
    inverts* nt.
    eauto.
  - inverts Typ.
    inverts H0.
    inverts H9;try solve[forwards*:abs_nlam].
    inductions A; eauto.
    exists.
    apply TReduce_blame; eauto.
    unfold not; intros nt.
    inverts* nt.

    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_absd; eauto.
    exists.
    apply TReduce_adyn; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_adyn; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.

    inductions A; eauto.
    inverts* Val; inverts* H.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_blame; eauto.
    unfold not;intros nt;inverts* nt.
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
    inverts H0.
    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
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
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros nt.
    inverts* nt.
    split.
    unfold not; intros nt.
    inverts* nt.
    eauto.
    simpl. eauto.
  -
    inverts Typ. inverts H. inverts H0.
    +
     exists. apply TReduce_abs with (C := t_int) (D := t_arrow t_int t_int); eauto.
    +
    exists.
    eapply TReduce_anyd; eauto.
    simpl; unfold FLike. splits*.
    unfold not; intros nt;inverts nt.
    unfold not; intros nt;inverts nt.
  -
     inverts Typ. inverts H. inverts H0.
     +
     exists. apply TReduce_abs with (C := t_int) (D := t_int); eauto.
     +
     exists.
     eapply TReduce_anyd; eauto.
     simpl; unfold FLike. splits*.
     unfold not; intros nt;inverts nt.
     unfold not; intros nt;inverts nt.
Qed.



(* 
Definition typing_typing G dir e A  := 
   match dir with 
    | Chk2 l b B => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma typing_typing: forall G dir e  A t,
 typing G e dir A t ->
 typing_typing G dir e A.
Proof.
  introv typ.
  inductions typ; unfold typing_typing in *; intros; eauto.
  eapply Typ_app; eauto.
  inverts* IHtyp2.
  eapply Typ_app; eauto.
  inverts* IHtyp2. 
Qed. *)






Definition Typing_typing G dir e A  := 
   match dir with 
    | Chk3 l b => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma typing_typing: forall G dir e  A t,
 typing G e dir A t ->
 Typing_typing G dir e A.
Proof.
  introv typ.
  inductions typ; unfold Typing_typing in *; intros; eauto.
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
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    right; unfold not; intros nt; inverts* nt. inverts* H1.
    +
    inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    right; unfold not; intros nt; inverts* nt. inverts* H1.
  - inductions lc; try solve[exfalso; apply H; auto];
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
Qed.



Theorem Progress : forall e dir T,
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
    forwards*: TypedReduce_progress l b Typ2.
    inverts H0.
    inductions x; try solve[inverts* H1].
    inverts Val1; inverts* Typ1.
    + 
    inverts H.
    *
    forwards*: principle_inf Typ1. 
    inductions e2'.
    assert(fill ((appCtxR e1 l b )) e2 = e_app e1 l b e2); eauto.
    rewrite <- H0.
    exists. apply do_step; eauto.
    assert(fill ((appCtxR e1  l b )) e2 = e_app e1 l b e2); eauto.
    rewrite <- H0.
    exists. apply blame_step; eauto.
    *
    inverts Val1;inverts* Typ1.
  + 
    inductions e1'.
    assert(fill ((appCtxL e2 l b )) e1 = e_app e1 l b e2); eauto.
    rewrite <- H0.
    exists. apply do_step; eauto.
    assert(fill ((appCtxL e2 l b )) e1 = e_app e1 l b e2); eauto.
    rewrite <- H0.
    exists. apply blame_step; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress p b Typ.
      inverts* H.
      destruct(value_decidable (e_anno e p b A)); eauto. 
    + right.
      induction t'.
      * 
        assert(fill ((annoCtx p b A)) e = e_anno e p b A); eauto.
        rewrite <- H.
        exists. apply do_step; eauto.
      *
        assert(fill ((annoCtx p b A)) e = e_anno e p b A); eauto.
        rewrite <- H.
        exists. apply blame_step; eauto.
  - forwards*: IHTyp Typ.
  - 
    right. inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    +
    forwards* h1: value_group Val2.
    inverts h1; try solve[inverts H0;forwards*: abs_nlam].
    inverts Val1;inverts* Typ1;try solve[inverts H0;inverts* Typ2].
    forwards* h2: value_group H1.
    inverts* h2.
    inverts* H5. inverts H6. inverts* H5.
    inverts* H0. inverts* H1. inverts* H0.
    inverts* H.   
    + 
    inductions e2'.
    assert(fill ((appvCtxR e1 )) e2 = e_appv e1 e2); eauto.
    rewrite <- H0.
    exists. apply do_step; eauto.
    assert(fill ((appvCtxR e1 )) e2 = e_appv e1 e2); eauto.
    rewrite <- H0.
    exists. apply blame_step; eauto.
    +
    inductions e1'.
    assert(fill ((appvCtxL e2 )) e1 = e_appv e1 e2); eauto.
    rewrite <- H0.
    exists. apply do_step; eauto.
    assert(fill ((appvCtxL e2 )) e1 = e_appv e1 e2); eauto.
    rewrite <- H0.
    exists. apply blame_step; eauto.
Qed.



Lemma value_value: forall v1 A dir v2,
 value v1 ->
 atyping nil v1 dir A v2 ->
 value v2.
Proof.
  introv val typ.
  lets typ': typ.
  inductions typ; try solve[inverts* val];
  try solve[forwards*: atyping_regular_1 typ'].
  inverts* val.
  -
  inverts* typ.
  forwards* h1: atyping_inf H.
  rewrite h1 in *. subst.
  forwards* h2: atyping_inf2 H.
  -
  inverts* typ.
  forwards* h1: atyping_inf H.
  rewrite h1 in *. subst.
  forwards* h2: atyping_inf2 H.
  rewrite <- h2 in *; eauto.
Qed.



Lemma walue_walue: forall v1 A dir v2,
 walue v1 ->
 atyping nil v1 dir A v2 ->
 walue v2.
Proof.
  introv val typ.
  lets typ': typ.
  inductions typ; try solve[inverts* val];
  try solve[forwards*: atyping_regular_1 typ'].
  forwards*: value_value typ'.
  forwards*: value_group H.
  inverts* H0. inverts* H1. inverts H0.
  inverts* H1. inverts H0.
Qed.





Lemma pty_pty: forall v1 A dir v2,
 atyping nil v1 dir A v2 ->
 principal_type v1 =  principal_type v2.
Proof.
  introv typ.
  inductions typ;eauto.
Qed.


Lemma value_value2: forall v1 A dir v2,
 value v2 ->
 atyping nil v1 dir A v2 ->
 value v1.
Proof.
  introv val typ.
  lets typ': typ.
  inductions typ; try solve[inverts* val];
  try solve[forwards*: atyping_regular_1r typ'].
  inverts* val.
  -
  inverts* typ.
  forwards* h1: atyping_inf2 H.
  rewrite h1 in *. subst.
  forwards* h2: atyping_inf H.
  -
  inverts* typ.
  forwards* h1: atyping_inf2 H.
  rewrite h1 in *. subst.
  forwards* h2: atyping_inf H.
  rewrite <- h2 in *; eauto.
Qed.


Lemma walue_walue2: forall v1 A dir v2,
 walue v2 ->
 atyping nil v1 dir A v2 ->
 walue v1.
Proof.
  introv val typ.
  lets typ': typ.
  inductions typ; try solve[inverts* val];
  try solve[forwards*: atyping_regular_1 typ'].
  forwards*: value_value2 typ'.
  forwards*: value_group H.
  inverts* H0. inverts* H1. inverts H0.
  inverts* H1. inverts H0.
Qed.


Lemma TypedReduce_equal: forall v1 v2 v1' v2' l b A,
 value v1 ->
 atyping nil v1 Chk A v2 ->
 TypedReduce v1 l b A (e_exp v1') ->
 TypedReduce v2 l b A (e_exp v2') ->
 atyping nil v1' Inf A v2'.
Proof.
  introv val typ red1 red2. 
  inductions red1; intros;eauto;
  try solve[inverts* typ;inverts* H;inverts* red2].
  -
  inverts typ; try solve[forwards*: abs_nlam];
  try solve[inverts* red2].
  forwards* h2: value_value H1.
  forwards* h1: atyping_inf2 H1.
  forwards* h3: atyping_inf H1.
  rewrite h3 in *. subst*.
  inverts* red2; try solve[inverts h1].
  -
  forwards* h2: value_value typ.
  inverts typ; try solve[forwards*: abs_nlam];
  try solve[inverts* red2].
  inverts* red2; simpl in *; inverts* H5.
  forwards* h1: atyping_inf2 H0.
  forwards* h3: atyping_inf H0.
  rewrite h3 in *. subst*.
  inverts* red2; try solve[inverts H].
  forwards*: flike_not_ground H7.
  -
  inverts typ. inverts* H0.
  lets red2': red2.
  inverts* red2; simpl in *; try solve[inverts* H6];
  try solve[inverts* H8]; try solve[inverts* H9].
  inverts H10; try solve[forwards*: abs_nlam].
  inverts val.
  forwards* h2: value_value H0.
  forwards* h1: atyping_inf2 H0.
  rewrite h1 in *. subst.
  forwards* h3: atyping_inf H0.
  rewrite h3 in *. inverts H9.
  -
  inverts typ; simpl in *.
  inverts* H.
  forwards* h2: value_value H0.
  forwards* h1: atyping_inf2 H0.
  forwards* h3: atyping_inf H0.
  rewrite h3 in *.
  rewrite <- h1 in *.
  inverts* red2; simpl in *; try solve[inverts* H].
  forwards*: flike_not_ground H.
  -
  forwards* h2: value_value typ.
  inverts typ. inverts* H0.
  inverts* H10; try solve[forwards*: abs_nlam].
  inverts* red2; simpl in *; try solve[inverts* H9];
  try solve[inverts* H];
  try solve[forwards*: abs_nlam].
  eapply atyp_anno;eauto.
  eapply atyp_sim;eauto.
  inverts H. inverts* H3.
  inverts* H5.
  -
  forwards* h2: value_value typ.
  inverts typ. inverts* H.
  inverts* H9; try solve[forwards*: abs_nlam].
  inverts* red2; simpl in *; try solve[inverts* H9];
  try solve[inverts* H10];
  try solve[inverts* H];
  try solve[forwards*: abs_nlam].
  -
  forwards* h2: value_value typ.
  inverts typ. inverts* H2.
  inverts* H12; try solve[forwards*: abs_nlam].
  inverts* red2; simpl in *; try solve[inverts* H8];
  try solve[inverts* H13];
  try solve[inverts* H];
  try solve[inverts* H2; try solve[forwards*: abs_nlam]];
  try solve[forwards*: abs_nlam].
  inverts val.
  forwards* h3: atyping_inf H2.
  rewrite h3 in *; eauto.
  inverts h2.
  forwards*: flike_not_ground H.
  -
  forwards* h2: value_value typ.
  inverts typ. inverts* H0.
  inverts* H10; try solve[forwards*: abs_nlam].
  inverts val.
  forwards* h3: atyping_inf H0.
  inverts* red2; simpl in *; try solve[inverts* H12];
  try solve[inverts* H13];
  try solve[inverts* H];
  try solve[inverts* H2; try solve[forwards*: abs_nlam]];
  try solve[forwards*: abs_nlam].
  rewrite <- H13 in *. inverts H7.
  forwards*: flike_not_ground H13.
  inverts H0;  try solve[forwards*: abs_nlam].
  forwards*: flike_not_ground H14.
  subst*.
  rewrite H13 in *; eauto.
Qed.


Lemma atyping_typing: forall G e1 e2 dir A,
 atyping G e1 dir A e2 ->
 Typing G e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
  assert(nlam t).
  inductions typ; try solve[forwards*: abs_nlam];eauto.
  eapply Typ_sim;eauto.
Qed.


Lemma atyping_typing2: forall G e1 e2 dir A,
 atyping G e1 dir A e2 ->
 Typing G e1 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



Lemma TypedReduce_blame: forall v1 v2 l b A,
 value v1 ->
 atyping nil v1 Chk A v2 ->
 TypedReduce v1 l b A (e_blame l b) ->
 TypedReduce v2 l b A (e_blame l b).
Proof.
  introv val typ red. 
  inductions red; intros;eauto;
  try solve[inverts* typ;inverts* H;inverts* red2].
  forwards*: value_value typ.
  inverts* typ. inverts H1.
  inverts* H11.
  inverts val. inverts H0.
  forwards* h1: atyping_inf H1.
  forwards* h2: atyping_inf2 H1.
  rewrite <- h1 in *.
  rewrite <- h2 in *; eauto.
Qed.


Lemma TypedReduce_blame2: forall v1 v2 l b A,
 value v1 ->
 atyping nil v1 Chk A v2 ->
 TypedReduce v2 l b A (e_blame l b) ->
 TypedReduce v1 l b A (e_blame l b).
Proof.
  introv val typ red. 
  inductions red; intros;eauto;
  try solve[inverts* typ;inverts* H;inverts* red2].
  forwards*: value_value typ.
  inverts* typ. inverts H1.
  inverts* H9.
  inverts val. inverts H0.
  forwards* h1: atyping_inf H1.
  forwards* h2: atyping_inf2 H1.
  rewrite <- h2 in *.
  rewrite <- h1 in *; eauto.
Qed.

Lemma atyping_chk: forall G e1 e2 A,
 atyping G e1 Inf A e2 ->
 atyping G e1 Chk A e2.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



Lemma more_steps: forall v1 v2 v3 v4 v4' A1 A2 l b,
  value v2 ->
  value v4 ->
  atyping [] v1 Inf (t_arrow A1 A2) v2 ->
  atyping [] v3 Chk A1 v4 ->
  TypedReduce v4 l b A1 (e_exp v4') ->
  exists e2 e1,
  step (e_appv v2 v4') (e_exp e2) /\
  sstep (e_app v1 l b v3) (e_exp e1) /\
  atyping [] e1 Inf A2 e2. 
Proof.
  introv val2 val4 typ1 typ2 red.
  forwards* h1: value_value2 typ1.
  forwards* h2: value_value2 typ2.
  inverts h1;inverts typ1.
  -
    forwards* h3: atyping_typing2 typ2.
    forwards* h4: TypedReduce_progress l b h3.
    inverts h4. destruct x.
    +
    forwards* h5: TypedReduce_equal H0 red.
    forwards* h7: atyping_typing typ2.
    forwards* h6: TypedReduce_walue red.
    exists. splits.
    apply Step_nbeta; auto.
    apply sStep_nbeta; eauto.
    eapply atyp_anno; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    assert((e1 ^^ v4') = 
    [y ~> v4'] (e1 ^^ e_var_f y)).
    rewrite (subst_exp_intro y); eauto.
    rewrite H1.
    forwards*: H7 y.
    eapply atyping_c_subst_simpl; eauto.
    forwards* : TypedReduce_nlambda H0.
    +
    forwards* h7: atyping_typing typ2.
    forwards* h8: atyping_typing2 typ2.
    lets red': H0.
    inverts* red'.
    forwards*: TypedReduce_blame H0.
    forwards*: TypedReduce_unique red H1.
    congruence.
  -
    forwards* h3: atyping_typing2 typ2.
    forwards* h4: TypedReduce_progress l b h3.
    inverts h4. destruct x.
    +
    forwards* h5: TypedReduce_equal H1 red.
    forwards* h7: atyping_typing typ2.
    forwards* h6: TypedReduce_walue red.
    inverts val2.
    forwards* h8: value_group H4. inverts h8.
    *
    forwards* h9: walue_walue2 H9.
    inverts H9; try solve[inverts h9].
    forwards* h10:atyping_inf H3.
    forwards* h11:atyping_inf2 H3.
    rewrite <- H0 in *. subst. inverts H5.
    exists. splits.
    eapply Step_abeta; eauto.
    eapply sStep_abeta; eauto.
    eapply atyp_anno; eauto.
    eapply atyp_sim with (A:= D); eauto.
    apply atyp_appv; eauto.
    eapply atyp_sim; eauto.
    forwards*: TypedReduce_nlambda H1.
    *
    inverts H2.
    inverts H9; try solve[inverts* H2;forwards*: abs_nlam].
    exists. splits.
    apply Step_beta; eauto.
    eapply sStep_beta; eauto.
    eapply atyp_anno; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    assert((x ^^ v4') = 
    [y ~> v4'] (x ^^ e_var_f y)).
    rewrite (subst_exp_intro y); eauto.
    inverts H3. inverts H5. inverts H3.
    rewrite H2.
    forwards*: H10 y.
    eapply atyping_c_subst_simpl; eauto.
    forwards* : TypedReduce_nlambda H1.
    inverts H3. inverts H7. inverts H2.
    inverts H6.
    +
    forwards* h7: atyping_typing typ2.
    forwards* h8: atyping_typing2 typ2.
    lets red': H1.
    inverts* red'.
    forwards*: TypedReduce_blame H1.
    forwards*: TypedReduce_unique red H2.
    congruence.
  -
    forwards* h3: atyping_typing2 typ2.
    forwards* h4: TypedReduce_progress l b h3.
    inverts h4. destruct x.
    +
    forwards* h5: TypedReduce_equal H red.
    forwards* h7: atyping_typing typ2.
    forwards* h6: TypedReduce_walue red.
    forwards* h8: Tred_value red.
    forwards* h9: Tred_value H.
    inverts h9;inverts h5.
    exists. splits.
    eapply Step_add; eauto.
    eapply sStep_add; eauto.
    eapply atyp_addl; eauto.
    +
    forwards* h7: atyping_typing typ2.
    forwards* h8: atyping_typing2 typ2.
    lets red': H.
    inverts* red'.
    forwards*: TypedReduce_blame H.
    forwards*: TypedReduce_unique red H0.
    congruence.
  -
    forwards* h3: atyping_typing2 typ2.
    forwards* h4: TypedReduce_progress l b h3.
    inverts h4. destruct x.
    +
    forwards* h5: TypedReduce_equal H red.
    forwards* h7: atyping_typing typ2.
    forwards* h6: TypedReduce_walue red.
    forwards* h8: Tred_value red.
    forwards* h9: Tred_value H.
    inverts h9;inverts h5.
    exists. splits.
    eapply Step_addl; eauto.
    eapply sStep_addl; eauto.
    eapply atyp_lit; eauto.
    +
    forwards* h7: atyping_typing typ2.
    forwards* h8: atyping_typing2 typ2.
    lets red': H.
    inverts* red'.
    forwards*: TypedReduce_blame H.
    forwards*: TypedReduce_unique red H0.
    congruence.
Qed.



Lemma step_sstep:forall e1 e2 e2' A,
 atyping nil e1 Chk A e2 ->
 step e2 (e_exp e2') ->
 (exists e1', sstep e1 (e_exp e1') /\ atyping nil e1' Chk A e2') \/ 
 (exists e22 e1', step e2' (e_exp e22) /\ sstep e1 (e_exp e1') /\ atyping nil e1' Chk A e22).
Proof.
  introv typ red. gen e1 A.
  inductions red; intros; eauto.
  -
    destruct E; unfold fill in *; inverts* typ.
    +
      inverts H0. inverts H.
      forwards* lc1: atyping_regular_1r H12.
      forwards* h2:atyping_chk H11.
      forwards* h3: IHred h2.
      forwards* lc2: atyping_regular_1 H11.
      inverts h2; try solve[forwards*: step_not_value red].
      forwards* h4: ainference_unique H11 H. subst.
      forwards* h5: atyping_typing H.
      forwards* h6: preservation red.
      inverts h3.
      ++
      lets(ee1&rred1&ttyp1):H5.
      forwards*: step_not_nlam red.
      inverts ttyp1; try solve[forwards*: abs_nlam].
      forwards* h7: atyping_typing H7.
      forwards* h8: inference_unique h6 h7. subst.
      left.
      exists. splits.
      rewrite fill_appl.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
      ++
      lets(ee1&ee2&rred1&rred2&ttyp1):H5.
      forwards*: step_not_nlam rred1.
      inverts ttyp1; try solve[forwards*: abs_nlam].
      forwards* h7: atyping_typing H7.
      forwards* h9: preservation rred1.
      forwards* h8: inference_unique h9 h7. subst.
      right.
      exists. splits.
      rewrite fill_appl.
      apply do_step; eauto.
      rewrite fill_appl.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
    +
      inverts H0. inverts H.
      forwards* h1: value_value2 H11.
      forwards* h2: atyping_inf2 H11.
      forwards* h3: atyping_inf H11.
      rewrite h2 in *. subst. inverts H10.
      forwards* h4: IHred H12.
      inverts h4.
      *
      lets(ee1&rred1&ttyp1):H.
      left.
      exists. splits.
      rewrite fill_appr.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
      *
      lets(ee1&ee2&rred1&rred2&ttyp1):H.
      right.
      exists. splits.
      rewrite fill_appr.
      apply do_step; eauto.
      rewrite fill_appr.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
    +
      inverts H0. inverts H.
      forwards* h4: IHred H8.
      inverts h4.
      *
      lets(ee1&rred1&ttyp1):H.
      left.
      exists. splits.
      rewrite fill_anno.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
      *
      lets(ee1&ee2&rred1&rred2&ttyp1):H.
      right.
      exists. splits.
      rewrite fill_anno.
      apply do_step; eauto.
      rewrite fill_anno.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
    +
      inverts H0. inverts H.
      forwards* lc1: atyping_regular_1r H9.
      forwards* h1:atyping_chk H7.
      forwards* h2: IHred h1.
      forwards* lc2: atyping_regular_1 H9.
      forwards* h3: atyping_typing H7.   
      inverts h2.
      *
      lets(ee1&rred1&ttyp1):H.
      forwards*: step_not_nlam red.
      inverts ttyp1; try solve[forwards*: abs_nlam].
      forwards* h4: atyping_typing H4.
      forwards* h5: preservation red.
      forwards* h6: inference_unique h4 h5. subst. inverts H5.   
      left.
      exists. splits.
      rewrite fill_appl.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
      *
      lets(ee1&ee2&rred1&rred2&ttyp1):H.
      forwards*: step_not_nlam rred1.
      inverts ttyp1; try solve[forwards*: abs_nlam].
      forwards* h4: atyping_typing H4.
      forwards* h5: preservation red.
      forwards* h6: preservation rred1.
      forwards* h7: inference_unique h4 h6. subst. inverts H5.   
      right.
      exists. splits.
      rewrite fill_appv.
      apply do_step; eauto.
      rewrite fill_appl.
      apply sdo_step; eauto.
      unfold fill.
      eapply atyp_sim; eauto.
    +
    inverts H0. inverts H.
    forwards* h1: value_value2 H7.
    inverts red.
    *
    destruct E; unfold fill in *;inverts* H.
    forwards* h2: IHred (e_anno e0 l0 b A1).
    inverts h2.
    ++
    forwards* lc1: atyping_regular_1r H9.
    lets(ee1&rred1&ttyp1):H.
    destruct(value_decidable e4); auto.
    forwards* h3: value_value H9.
    forwards*: step_not_value H5.
    inverts* rred1.
    destruct E; unfold fill in *;inverts* H6.
    forwards* h4: atyping_inf H7.
    inverts ttyp1. inverts H6.
    left.
    exists. splits.
    rewrite fill_appr.
    apply sdo_step; eauto.
    unfold fill.
    eapply atyp_sim; eauto.
    ++
    lets(ee1&ee2&rred1&rred2&ttyp1):H.
    forwards* lc1: atyping_regular_1r H9.
    destruct(value_decidable e4); auto.
    forwards* h3: value_value H9.
    forwards*: step_not_value H5.
    inverts* rred2.
    destruct E; unfold fill in *;inverts* H6.
    forwards* h4: atyping_inf H7.
    inverts ttyp1. inverts H6.
    right.
    exists. splits.
    rewrite fill_appvr.
    apply do_step.
    eauto.
    apply rred1.
    rewrite fill_appr.
    apply sdo_step.
    eauto.
    apply H11.
    unfold fill.
    eapply atyp_sim; eauto.
    *
    forwards*: more_steps H7 H9 H10.
    lets(ee1&ee2&rred1&rred2&ttyp1):H.
    forwards* h10: step_not_nlam rred1.
    assert(nlam ee2).
    inverts* ttyp1; try solve[forwards*: abs_nlam].
    right. exists. splits.
    apply rred1.
    apply rred2.
    eapply atyp_sim; eauto. 
  -
  inverts typ. inverts H1.
  forwards* h1: walue_walue2 H0.
  forwards* h2: value_value2 H8.
  forwards* h3: atyping_typing2 H10.
  assert(value t2). inverts* H0.
  forwards* h5: value_value2 H10.
  forwards* h4: TypedReduce_progress l2 b h3.
  inverts* h4.
  forwards* h6: value_tred_keep2 H4. inverts h6.
  inverts H8. inverts h2. 
  inverts* H12; try solve[forwards*: abs_nlam];
  try solve[inverts* H5; try solve[forwards*: abs_nlam]].
  left.
  exists. splits.
  eapply sStep_beta; eauto.
  eapply atyp_sim; eauto.
  eapply atyp_anno; eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); eauto.
  assert((e ^^ e_anno t2 l2 b A) = 
  [y ~> e_anno t2 l2 b A] (e ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H5.
  forwards*: H14 y.
  eapply atyping_c_subst_simpl; eauto.
  -
  inverts typ.
  inverts H2.
  forwards*: value_value2 H10.
  forwards* h1: atyping_typing2 H10.
  forwards* h2: TypedReduce_progress l b h1.
  inverts h2.
  destruct x.
  +
  forwards* h3: TypedReduce_equal H5 H0.
  assert(atyping [] (e_anno e l b A) Inf A (e_anno v l b A)); eauto.
  left. exists.
  splits.
  eapply sStep_annov; eauto.
  unfold not;intros nt. 
  forwards*: value_value nt.
  forwards*: TypedReduce_nlambda H5.
  +
  forwards* h4: atyping_typing H10.
  lets red': H5.
  inverts H5.
  forwards*: TypedReduce_blame red'.
  forwards*: TypedReduce_unique H0 H5.
  congruence.
  -
  inverts typ. inverts H3.
  forwards* h1: value_value2 H10.
  forwards* h2: value_value2 H12.
  inverts* H1.
  inverts H10.
  inverts H11; try solve[inverts H0].
  forwards* h3: atyping_inf2 H3.
  rewrite h3 in *. subst. inverts H6.
  assert(value (e_anno t2 l0 b A)); auto.
  assert(value (e_anno e2 l0 b A)).
  forwards* h4: value_value2 H2.
  forwards* h5: atyping_typing2 H12.
  forwards* h6: TypedReduce_progress l0 b h5.
  inverts h6.
  forwards* h7: value_tred_keep H8.
  inverts h7.
  forwards* h8: walue_walue2 H.
  forwards* h9: walue_walue2 H0.
  forwards* h10: atyping_inf H3.
  left. exists.
  splits.
  eapply sStep_abeta; eauto.
  eapply atyp_sim; eauto.
  eapply atyp_anno; auto.
  eapply atyp_sim with (A := D); auto.
  eapply atyp_appv; auto.
  eapply atyp_sim; eauto.
  -
  inverts typ.
  inverts H3.
  forwards* h1: atyping_inf2 H14.
  rewrite h1 in *. subst. inverts H13.
  forwards*: more_steps H14 H15 H2.
  lets(ee1&ee2&rred1&rred2&ttyp1):H1.
  forwards* h10: step_not_nlam rred1.
  assert(nlam ee2).
  inverts* ttyp1; try solve[forwards*: abs_nlam].
  right. exists. splits.
  apply rred1.
  apply rred2.
  eapply atyp_sim; eauto. 
  -
  inverts typ. inverts* H1.
  forwards* h1: value_value2 H12.
  inverts* H12. inverts* H11.
  forwards*: atyping_regular_1r H13.
  left. exists. splits.
  eapply sStep_betad; eauto.
  eapply atyp_sim; eauto.
  -
  inverts typ. inverts H.
  -
  inverts typ. inverts H.
  -
  inverts typ. inverts H1.
  forwards* lc: atyping_regular_1r H8.
  inverts* H8.
  forwards* h1:walue_walue2 H0.
  assert(value t2).
  inverts* H0.
  forwards* h2: value_value2 H10.
  forwards* h3: atyping_typing2 H10.
  forwards* h5: TypedReduce_progress l1 b0 h3.
  inverts h5.
  forwards* h6: value_tred_keep2 H4.
  inverts h6.
  left. exists. splits.
  eapply sStep_nbeta; eauto.
  eapply atyp_sim; eauto.
  eapply atyp_anno; eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); eauto.
  assert((e ^^  e_anno t2 l1 b0 t_dyn) = 
  [y ~>  e_anno t2 l1 b0 t_dyn] (e ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H5.
  forwards*: H9 y.
  eapply atyping_c_subst_simpl; eauto.
Qed.



Lemma steps_ssteps_com:forall e1 e2 e2' A n1 n,
 atyping nil e1 Chk A e2 ->
 n < n1 ->
 sstep_sz e2 (e_exp e2') n ->
 value e2' ->
 exists e1', stepss e1 (e_exp e1') /\ value e1' /\ atyping nil e1' Chk A e2'.
Proof.
  introv typ sz red val. gen e1 A e2 e2' n.
  inductions n1; intros; try solve[omega].
  inverts* red.
  -
  forwards*: value_value2 typ.
  -
  forwards*: step_sstep H0.
  inverts H.
  +
  lets(ee1&rred1&ttyp1): H1.
  assert(n0 < n1). omega.
  forwards*: IHn1 H2.
  lets(ee2&rred2&vval1&ttyp2): H3.
  exists. splits. 
  eapply steps_n.
  apply rred1. apply rred2.
  auto.
  auto.
  +
  lets(ee1&ee2&rred1&rred2&ttyp1): H1.
  assert(n0 < n1). omega.
  inverts H2.
  *
  forwards*: step_not_value rred1.
  *
  forwards*: atyping_typing typ.
  forwards*: preservation H0.
  forwards* h1: step_unique rred1 H4.
  inverts h1.
  forwards*: IHn1 H6.
  omega.
  lets(ee3&rred3&vval3&ttyp3): H5.
  exists. splits.
  eapply steps_n; eauto.
  auto.
  auto.
Qed.


Lemma sstep_step:forall e1 e2 e1' A,
 atyping nil e1 Chk A e2 ->
 sstep e1 (e_exp e1') ->
 exists e2', ssteps e2 (e_exp e2') /\ atyping nil e1' Chk A e2' .
Proof.
  introv typ red. gen e2 A.
  inductions red; intros; eauto.
  - (*do step *)
  destruct E;unfold fill in *;inverts* typ.
    +
    inverts H0.
    *
    inverts H.
    forwards* h1: atyping_regular_1 H11.
    forwards* h2: atyping_chk H10.
    forwards* h3: IHred h2.
    lets (ee1&rred1&ttyp1): h3.
    forwards* h4: atyping_typing H10.
    forwards* h5: preservation_multi_step2 rred1.
    exists. splits.
    eapply smulti_rred_appv2;eauto.
    eapply atyp_sim;eauto.
    eapply atyp_appv;eauto.
    inverts ttyp1.
    inverts* h5.
    forwards* h6: atyping_typing H.
    forwards* h7: inference_unique h5 h6.
    subst*.
    *
    inverts H.
    forwards* h1: atyping_regular_1 H12.
    forwards* h2: atyping_chk H11.
    forwards* h3: IHred h2.
    lets (ee1&rred1&ttyp1): h3.
    forwards* h4: atyping_typing H11.
    forwards* h5: preservation_multi_step2 rred1.
    exists. splits.
    eapply smulti_rred_app2;eauto.
    eapply atyp_sim;eauto.
    eapply atyp_app;eauto.
    inverts ttyp1.
    inverts* h5.
    inverts* h5.
    forwards* h6: atyping_typing H.
    forwards* h7: inference_unique h5 h6.
    subst*.
    +
    inverts H0.
    *
    forwards* h1: IHred H11.
    lets (ee2&rred&ttyp): h1.
    inverts H.
    forwards* h2: value_value H10.
    exists. splits.
    apply smulti_rred_appv; auto.
    apply smulti_rred_anno;auto.
    apply rred.
    eapply atyp_sim; eauto.
    *
    forwards* h1: IHred H12.
    lets (ee2&rred&ttyp): h1.
    inverts H.
    forwards* h2: value_value H11.
    forwards* h3: atyping_inf2 H11.
    forwards* h4: atyping_inf H11.
    rewrite h4 in *. subst. inverts H7. 
    exists. splits.
    eapply smulti_rred_app.
    apply h3.
    auto.
    apply rred.
    eapply atyp_sim; eauto.
    +
    inverts H0.
    forwards* h1: IHred H10.
    lets (ee2&rred&ttyp): h1.
    exists. splits.
    apply smulti_rred_anno; auto.
    apply rred.
    eapply atyp_sim; eauto.
    +
    inverts* H0.
    +
    inverts* H0.
  - (* beta *)
  lets lc: atyping_regular_1 typ.
  inverts typ. inverts H2.
  +
  inverts H12.
  inverts H14; try solve[forwards*: abs_nlam].
  forwards* h1: value_value H13.
  destruct(value_decidable (e_anno t2 l2 b2 A2)); eauto.
  *
  assert(value (e_anno v l2 b2 A2)).
  eapply value_value2; eauto.
  forwards* h2: value_tred_keep2 H1.
  inverts h2.
  inverts lc. inverts H8.
  exists. splits.
  apply sstars_one.
  eapply Step_beta; eauto.
  forwards*: value_group H2. inverts* H6.
  inverts H8. inverts* H6. inverts H8. inverts H6.
  eapply atyp_sim;eauto.
  eapply atyp_anno;eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e_anno t2 l2 b2 A2) = [y ~> e_anno t2 l2 b2 A2] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H6.
  eapply atyping_c_subst_simpl; eauto.
  *
  forwards* h4: atyping_typing H13.
  forwards* h3:TypedReduce_progress l2 b2 h4. inverts h3.
  destruct x.
  ++
  forwards* h5: TypedReduce_equal H1 H5.
  inverts lc. inverts H8.
  forwards* h6: atyping_typing h5.
  forwards* h7: TypedReduce_walue H5.
  exists. splits.
  eapply sstars_trans.
  rewrite fill_appvr.
  apply sstars_one.
  apply do_step; simpl in *;eauto.
  (* apply Step_annov;simpl in *;eauto.
  unfold fill. *)
  apply sstars_one.
  eapply Step_beta; eauto.
  eapply atyp_sim;eauto.
  eapply atyp_anno;eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e0) = [y ~> e0] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H6.
  eapply atyping_c_subst_simpl; eauto.
  forwards*: TypedReduce_nlambda H1.
  forwards* h8: atyping_typing2 H13.
  ++
  lets red': H5.
  inverts H5.
  forwards* h2: TypedReduce_blame2 H13 red'.
  forwards* h3: atyping_typing2 H13.
  forwards* h5: TypedReduce_unique H1 h2.
  congruence. 
  +
  lets typ: H13.
  inverts H13. inverts H9.
  forwards* h2: value_value H14.
  inverts H12; try solve[forwards*: abs_nlam].
  forwards* h3: atyping_typing H14.
  forwards* h4: atyping_typing2 H14.
  forwards* h5: value_value typ. inverts h5.
  forwards* h6: TypedReduce_progress l2 b2 h3.
  inverts h6.
  destruct x.
  ++
  forwards* h7: TypedReduce_equal H1 H2.
  forwards* h8: TypedReduce_walue H2.
  exists. splits.
  eapply sstars_trans.
  apply sstars_one.
  eapply Step_equal; simpl in *;eauto.
  apply sstars_one.
  apply Step_beta;eauto.
  eapply atyp_sim;eauto.
  eapply atyp_anno; eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e0) = [y ~> e0] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H5.
  eapply atyping_c_subst_simpl; eauto.
  forwards*: TypedReduce_nlambda H1.
  ++
  lets red': H2.
  inverts H2.
  forwards* h10: TypedReduce_blame2 H14 red'.
  forwards* h11: atyping_typing2 H14.
  forwards* h12: TypedReduce_unique H1 h10.
  congruence.  
  -
  inverts typ. 
  assert(not (value e2)).
  unfold not;intros nt.
  forwards*: value_value2 H2.
  inverts* H2.
  forwards* h1:value_value H13.
  forwards* h4: atyping_typing H13.
  forwards* h3: TypedReduce_progress l b h4.
  inverts h3.
  destruct x.
  ++
  forwards* h5: TypedReduce_equal H0 H2.
  forwards* h6: atyping_typing2 H13.
  exists. splits.
  apply sstars_one.
  eapply Step_annov; eauto.
  forwards*: TypedReduce_nlambda H0.
  ++
  lets red': H2.
  inverts H2.
  forwards* h2: TypedReduce_blame2 H13 red'.
  forwards* h3: atyping_typing2 H13.
  forwards* h5: TypedReduce_unique H0 h2.
  congruence. 
  - (* abeta *)
  inverts typ.  inverts H4.
  +
  forwards* h1: value_value H15.
  forwards* h2: value_value H14.
  inverts H14.
  destruct(value_decidable (e_anno t2 l b A2)); auto.
  * 
  assert(value (e_anno v2 l b A2)).
  eapply value_value2; eauto.
  forwards* h3: value_tred_keep2 H3.
  inverts h3.
  forwards* h4: pty_pty H16.
  rewrite h4 in *.
  forwards* h8: atyping_typing2 H15.
  forwards* h7: TypedReduce_walue H3.
  forwards* h5: walue_walue h7.
  forwards* h6: walue_walue H0.
  forwards* h11: walue_walue H.
  inverts H16; try solve[inverts H0].
  forwards* h9: atyping_inf2 H8.
  forwards* h10: value_value H8.
  exists. splits.
  apply sstars_one.
  eapply Step_abeta.
  auto.
  auto.
  auto.
  apply H2.
  eapply atyp_sim. 
  eapply atyp_anno;eauto.
  eapply atyp_sim.
  rewrite h9 in *. subst.
  inverts H9.
  apply atyp_appv.
  apply H8.
  eapply atyp_sim; auto.
  rewrite h9 in *. subst.
  inverts H9.
  auto.
  eauto. auto.
  eauto. 
  *
  inverts h2.
  inverts H16; try solve[inverts H0].
  forwards* h3: atyping_inf H7.
  forwards* h4: atyping_inf2 H7.
  rewrite h3 in *. subst.
  rewrite h4 in *. inverts H13.
  inverts H8.
  forwards* h5: atyping_typing H15.
  forwards* h6: TypedReduce_progress l b h5.
  inverts h6.
  forwards* h7: walue_walue H.
  forwards* h8: walue_walue H0.
  forwards* h10: atyping_typing2 H15.
  forwards* h9: TypedReduce_walue H3.
  destruct x.
  --
  forwards* h11: TypedReduce_equal H3 H2.
  forwards* h12: walue_walue h9.
  exists. splits.
  eapply sstars_trans.
  apply smulti_rred_appv.
  auto.
  apply sstars_one.
  eapply Step_annov; eauto.
  apply sstars_one.
  eapply Step_abeta.
  auto. auto. auto.
  apply h4.
  apply atyp_sim with (A := A1); auto.
  eapply atyp_anno;eauto.
  --
  lets red': H2.
  inverts H2.
  forwards* h2: TypedReduce_blame2 H15 red'.
  forwards* h6: atyping_typing2 H15.
  forwards* h16: TypedReduce_unique H3 h2.
  congruence. 
  +
  inverts H15. inverts H11.
  forwards* h1: value_value H14.
  forwards* h2: value_value H16.
  forwards* h3: atyping_typing2 H16.
  forwards* h4: atyping_typing H16.
  forwards* h5: walue_walue H.
  forwards* h6: walue_walue H0.
  forwards* h7: pty_pty H14.
  rewrite h7 in *.
  forwards* h8: TypedReduce_progress l b h4.
  inverts h8. destruct x.
  *
  forwards* h9: TypedReduce_equal H3 H4.
  forwards* h10: TypedReduce_walue H4.
  inverts H14; try solve[inverts h6].
  forwards* h11: atyping_inf H7.
  rewrite h11 in *. subst.
  rewrite H2 in *.
  inverts H8.
  forwards*: TypedReduce_walue H3.
  exists. splits.
  eapply sstars_trans.
  eapply sstars_one.
  eapply Step_equal; simpl;eauto.
  eapply sstars_one.
  eapply Step_abeta; eauto.
  eapply atyp_sim; eauto.
  eapply atyp_anno.
  eapply atyp_sim with (A := D); auto.
  eapply atyp_appv;eauto.
  *
  lets red': H4.
  inverts H4.
  forwards* h10: TypedReduce_blame2 H16 red'.
  forwards* h11: TypedReduce_unique H3 h10.
  congruence. 
  - (* betad*)
  inverts typ. inverts* H1.
  +
  inverts* H11.
  +
  forwards* h1: value_value H12.
  inverts* H12. inverts* H8.
  inverts* h1.
  forwards* lc: atyping_regular_1 H13.
  exists. splits.
  apply sstep_refl;eauto.
  eapply atyp_sim; eauto.
  - (* add *)
  inverts typ. inverts H1.
  +
  inverts H11.
  forwards* h1: value_value H12.
  forwards* h2: atyping_typing H12.
  forwards* h3: TypedReduce_progress l b h2.
  inverts h3.
  destruct x.
  ++
  forwards* h4: TypedReduce_equal H0 H1.
  inverts* h4.
  exists. splits.
  eapply sstars_trans.
  apply smulti_rred_appv; eauto.
  apply sstars_one.
  eapply Step_annov; eauto.
  unfold not;intros nt. inverts nt.
  apply sstars_one.
  eapply Step_add;eauto.
  eapply atyp_sim;eauto.
  ++
  lets red': H1.
  inverts H1.
  forwards* h4: TypedReduce_blame2 H12 red'.
  forwards* h5: atyping_typing2 H12.
  forwards* h6: TypedReduce_unique H0 h4.
  congruence. 
  +
  inverts H12. inverts H8.
  forwards* h1: value_value H13.
  forwards* h2: atyping_typing H13.
  forwards* h3: TypedReduce_progress l b h2.
  inverts h3.
  destruct x.
  ++
  forwards* h4: TypedReduce_equal H0 H4.
  inverts* h4.
  exists. splits.
  eapply sstars_trans.
  rewrite fill_appr.
  apply sstars_one.
  eapply Step_equal; simpl in *;eauto.
  apply sstars_one.
  apply Step_add;eauto.
  eapply atyp_sim;eauto.
  ++
  lets red': H4.
  inverts H4.
  forwards* h4: TypedReduce_blame2 H13 red'.
  forwards* h5: atyping_typing2 H13.
  forwards* h6: TypedReduce_unique H0 h4.
  congruence.  
  - (* addli*)
  inverts typ. inverts H1.
  +
  inverts H11.
  forwards* h1: value_value H12.
  forwards* h2: atyping_typing H12.
  forwards* h3: TypedReduce_progress l b h2.
  inverts h3.
  destruct x.
  ++
  forwards* h4: TypedReduce_equal H0 H1.
  inverts* h4.
  exists. splits.
  eapply sstars_trans.
  rewrite fill_appvr.
  apply sstars_one.
  apply do_step; simpl in *;eauto.
  eapply Step_annov;simpl in *;eauto.
  unfold not;intros nt;inverts nt.
  simpl in *.
  eapply sstars_one.
  apply Step_addl;eauto.
  eapply atyp_sim;eauto.
  ++
  lets red': H1.
  inverts H1.
  forwards* h4: TypedReduce_blame2 H12 red'.
  forwards* h5: atyping_typing2 H12.
  forwards* h6: TypedReduce_unique H0 h4.
  congruence.  
  +
  inverts H12. inverts H8.
  forwards* h1: value_value H13.
  forwards* h2: atyping_typing H13.
  forwards* h3: TypedReduce_progress l b h2.
  inverts h3.
  destruct x.
  ++
  forwards* h4: TypedReduce_equal H0 H1.
  inverts* h4.
  exists. splits.
  eapply sstars_trans.
  rewrite fill_appr.
  apply sstars_one.
  eapply Step_equal; simpl in *;eauto.
  apply sstars_one.
  apply Step_addl;eauto.
  eapply atyp_sim;eauto.
  ++
  lets red': H1.
  inverts H1.
  forwards* h4: TypedReduce_blame2 H13 red'.
  forwards* h5: atyping_typing2 H13.
  forwards* h6: TypedReduce_unique H0 h4.
  congruence.  
  - (* nbeta *)
  lets lc: atyping_regular_1 typ.
  inverts typ. inverts H2.
  +
  inverts H12.
  forwards* h1: value_value H13.
  destruct(value_decidable (e_anno t2 l b t_dyn)); eauto.
  *
  assert(value (e_anno v l b t_dyn)).
  eapply value_value2; eauto.
  forwards* h2: value_tred_keep2 H1.
  inverts h2.
  inverts lc. inverts H9.
  exists. splits.
  apply sstars_one.
  eapply Step_nbeta; eauto.
  forwards*: value_group H2. inverts* H6.
  inverts H9.  inverts* H6. inverts H9. inverts H6.
  eapply atyp_sim;eauto.
  eapply atyp_anno;eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e_anno t2 l b t_dyn) = [y ~> e_anno t2 l b t_dyn] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H6.
  eapply atyping_c_subst_simpl; eauto.
  *
  forwards* h4: atyping_typing H13.
  forwards* h3:TypedReduce_progress l b h4. inverts h3.
  destruct x.
  ++
  forwards* h5: TypedReduce_equal H1 H5.
  inverts lc. inverts H9.
  forwards* h6: atyping_typing h5.
  forwards* h7: TypedReduce_walue H5.
  exists. splits.
  eapply sstars_trans.
  rewrite fill_appvr.
  apply sstars_one.
  apply do_step; simpl in *;auto.
  apply Step_annov;simpl in *;eauto.
  unfold fill.
  apply sstars_one.
  eapply Step_nbeta; eauto.
  eapply atyp_sim;eauto.
  eapply atyp_anno;eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e0) = [y ~> e0] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H6.
  eapply atyping_c_subst_simpl; eauto.
  forwards*: TypedReduce_nlambda H1.
  forwards* h8: atyping_typing2 H13.
  ++
  lets red': H5.
  inverts H5.
  forwards* h2: TypedReduce_blame2 H13 red'.
  forwards* h3: atyping_typing2 H13.
  forwards* h5: TypedReduce_unique H1 h2.
  congruence. 
  +
  lets typ': H13.
  inverts H13. inverts H9.
  forwards* h1: value_value H14.
  forwards* h2:atyping_typing H14.
  forwards* h3: TypedReduce_progress l b h2.
  inverts h3.
  forwards* h6: value_value typ'.
  destruct x.
  *
  forwards* h4: TypedReduce_equal H1 H2.
  forwards* h7: atyping_typing2 H14.
  forwards* h8: TypedReduce_walue H2.
  exists. splits.
  eapply sstars_trans.
  apply sstars_one.
  eapply Step_equal; simpl;eauto.
  apply sstars_one.
  eapply Step_nbeta; eauto.
  eapply atyp_sim;eauto.
  eapply atyp_anno;eauto.
  pick fresh y.
  rewrite (subst_exp_intro y); auto.
  assert((e1 ^^ e0) = [y ~> e0] (e1 ^^ e_var_f y)).
  rewrite (subst_exp_intro y); eauto.
  rewrite H5.
  eapply atyping_c_subst_simpl; eauto.
  forwards*: TypedReduce_nlambda H1.
  *
  lets red': H2.
  inverts H2.
  forwards* h4: TypedReduce_blame2 H14 red'.
  forwards* h5: atyping_typing2 H14.
  forwards* h8: TypedReduce_unique H1 h4.
  congruence. 
Qed.


Lemma ssteps_steps: forall e1  r,
 ssteps e1 r ->
 steps e1 r.
Proof.
  introv red.
  inductions red; eauto.
Qed.



Lemma step_steps:forall e1 e2 e1' A,
 atyping nil e1 Chk A e2 ->
 sstep e1 (e_exp e1') ->
 exists e2', steps e2 (e_exp e2') /\ atyping nil e1' Chk A e2' .
Proof.
  introv typ red.
  forwards*: sstep_step typ red.
  inverts H. inverts* H0.
  forwards*: ssteps_steps H.
Qed.



Lemma sstep_step_blame:forall e1 e2 l b A,
 atyping nil e1 Chk A e2 ->
 sstep e1 (e_blame l b) ->
 step e2  (e_blame l b) .
Proof.
  introv typ red. gen e2 A.
  inductions red; intros; eauto.
  - (*do step *)
    destruct E; unfold fill in *; inverts typ.
    +
    inverts H0. 
    * 
    inverts H.
    forwards* h1: atyping_regular_1 H11.
    forwards* h4: atyping_chk H10.
    forwards*: IHred h4.
    rewrite fill_appv.
    apply blame_step; eauto.
    *
    inverts H.
    forwards* h1: atyping_regular_1 H12.
    forwards* h4: atyping_chk H11.
    forwards*: IHred h4.
    rewrite fill_app.
    apply blame_step; eauto.
    +
    inverts H0. 
    * 
    inverts H.
    forwards* h1: value_value H10.
    forwards*: IHred H11.
    forwards* h2: atyping_inf H10.
    forwards* h3: atyping_inf2 H10.
    rewrite h2 in *. inverts H4.
    rewrite fill_appvr.
    rewrite fill_anno.
    apply blame_step; eauto.
    *
    inverts H.
    forwards* h1: value_value H11.
    forwards*: IHred H12.
    forwards* h2: atyping_inf H11.
    forwards* h3: atyping_inf2 H11.
    rewrite h2 in *. inverts H4.
    rewrite fill_appr.
    apply blame_step; eauto.
    +
    inverts H0. inverts H.
    forwards*: IHred H10.
    rewrite fill_anno.
    apply blame_step; eauto.
    +
    inverts* H0.
    +
    inverts* H0.
  -
    inverts typ.
    inverts H3.
    +
    forwards* h1: value_value H13.
    forwards* h2: value_value H14.
    forwards* h3: atyping_inf H13.
    forwards* h4: atyping_inf2 H13.
    rewrite h3 in *. inverts H1.
    forwards* h5: atyping_typing H14.
    forwards* h6: atyping_typing2 H14.
    forwards*: TypedReduce_progress l b h5.
    inverts H1.
    forwards* h7: TypedReduce_blame H2.
    forwards* h8: TypedReduce_unique H3 h7.
    subst.  
    rewrite fill_appvr.
    eapply blame_step; eauto.
    eapply Step_annov; eauto.
    unfold not; intros nt.
    forwards*: value_tred_keep2 nt.
    congruence.
    +
    forwards* h1: value_value H14.
    forwards* h2: value_value H15.
    forwards* h3: atyping_inf H14.
    forwards* h4: atyping_inf2 H14.
    rewrite h3 in *. inverts H1. inverts H10.
    forwards* h5: atyping_typing H15.
    forwards* h6: atyping_typing2 H15.
    forwards*: TypedReduce_progress l b h5.
    inverts H1.
    forwards* h7: TypedReduce_blame H2.
  -
    inverts typ.
    inverts H2.
    assert(not (value (e_anno t l0 b0 A1))).
    unfold not;intros nt.
    forwards*: value_value2 nt.
    forwards* h1: value_value H12.
    lets h2: H0.
    inverts* H0.
    forwards*: TypedReduce_blame h2.
Qed.



Lemma sstep_step_blame2:forall e1 e2 l b A,
 atyping nil e1 Chk A e2 ->
 step e2 (e_blame l b) ->
 sstep e1  (e_blame l b) .
Proof.
  introv typ red. gen e1 A.
  inductions red; intros; eauto.
  - (*do step *)
    destruct E; unfold fill in *; inverts typ.
    +
    inverts H0. inverts H.
    forwards* h1: atyping_regular_1r H12.
    forwards* h2: atyping_chk H11.
    forwards*: IHred.
    rewrite fill_appl.
    eapply sblame_step; eauto.
    +
    inverts H0. inverts H.
    forwards* h1: value_value2 H11.
    forwards* h2: atyping_chk H11.
    forwards*: IHred.
    forwards*: pty_pty H11.
    rewrite <- H0 in *. 
    rewrite fill_appr.
    eapply sblame_step; eauto.
    +
    inverts H0. inverts H.
    forwards*: IHred.
    rewrite fill_anno.
    eapply sblame_step; eauto.
    +
    inverts H0. inverts H.
    forwards* h1: atyping_regular_1r H7.
    forwards* h2: atyping_chk H7.
    forwards* h3: atyping_regular_1r H9.
    forwards*: IHred.
    rewrite fill_appl.
    eapply sblame_step; eauto.
    +
    inverts H0. 
    inverts H.
    forwards* h1: value_value2 H7.
    forwards*: IHred.
    forwards* h2: atyping_inf2 H7.
    forwards*: pty_pty H7.
    rewrite h2 in *.
    inverts* red.
    *
    destruct E; unfold fill in *;inverts* H4.
    inverts H.
    destruct E; unfold fill in *;inverts* H4.
    rewrite fill_appr.
    eapply sblame_step; eauto.
    lets red': H14.
    inverts* H14.
    *
    lets red': H12.
    inverts* H12.
    forwards* h7: value_value2 H9.
    forwards* h6: TypedReduce_blame2 H9 red'.
  -
    inverts typ.
    inverts H3.
    forwards*: value_value2 H14.
    forwards*: value_value2 H15.
    forwards* h1: atyping_inf H14.
    forwards* h2: atyping_inf2 H14.
    rewrite h2 in *. subst. inverts H13.
    eapply sStep_betap; eauto.
    forwards*: TypedReduce_blame2 H15 H2.
  -
   inverts typ.
    inverts H2.
    forwards*: value_value2 H10.
    lets red': H0.
    inverts* red'.
    forwards*: TypedReduce_blame2 H10 H0.
    assert(not(value (e_anno e l b A))).
     unfold not;intros nt.
     forwards*: value_value nt.
     eapply sStep_annov; eauto.
Qed.
