Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma TypedReduce_unique: forall v r1 r2 (A: typ),
    value v -> (exists B, Typing nil v Inf B) -> TypedReduce v A r1 -> TypedReduce v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
  - inverts* R2.
    inverts H2.
  - inverts* R2.
    inverts* H6.
Qed.


Lemma TypedReduce_prv_value2: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red;try solve[inverts* Val]; eauto.
Qed.

Lemma principle_inf: forall v A,
  ssval v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed. 




Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto. right. unfold not;  intros. inverts* H.
  - inductions A; eauto. right. unfold not; intros.
    inverts* H.
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H.  destruct H0. left.  eauto. right.
    unfold not; intros. inverts* H1. destruct H0.
    right. unfold not; intros. inverts* H1.
    right. unfold not; intros. inverts* H1.
Qed.


Lemma TypedReduce_preservation2: forall v A v' B,
    value v -> TypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red;try solve[inverts* Val]; introv Typ;
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
    inverts Typ. inverts* H. 
    inverts* H4. inverts* H.
    destruct(sim_decidable (t_arrow A1 A2) (t_arrow C D)).
    eapply Typ_anno; eauto.
    inverts Lc. inverts H5.
    eapply Typ_save; eauto. 
    inverts H9.
    inverts H7.
    destruct(sim_decidable (t_arrow A1 A2) (t_arrow C D)).
    eapply Typ_anno; eauto.
    eapply Typ_save; eauto. 
    inverts H10.
Qed.


Lemma value_nlam: forall v,
 value v ->
 nlam v.
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma  TypeLists_unique: forall v r1 r2 B (A: list typ),
    walue v -> Typing nil v Chk B ->  TypeLists v A r1 ->  TypeLists v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2 B.
  lets R1': R1.
  induction R1; introv R2 typ;
    try solve [inverts* R2].
  - inverts* typ; try solve[inverts H0]; try solve[inverts Val].
    inverts Val; try solve[inverts H3].
    inverts* R2;try solve[inverts H0;inverts* H7];
    try solve[inverts H0;inverts* H8].
    forwards*: TypedReduce_unique H0 H8.
    inverts H11.
    forwards*: TypedReduce_unique H0 H10. 
  - inverts Val.
    forwards*: value_nlam H1.
    inverts typ; try solve[inverts H2].
    inverts* R2.
    forwards*: TypedReduce_unique H0 H9. inverts H12.
    inverts* H0.
  - inverts Val.
    forwards*: value_nlam H1.
    inverts typ; try solve[inverts H1].
    inverts* R2. inverts* R1. 
    forwards*: TypedReduce_unique H0 H11. congruence. 
    forwards*: TypedReduce_unique H0 H10. inverts H6.
    forwards*: TypedReduce_prv_value2 H0.   
    forwards*: TypedReduce_preservation2 H0.
    forwards*: Typing_chk H7. inverts H9.
    forwards*: IHR1 R1 H12. 
    forwards*: TypedReduce_unique H0 H11. inverts H6.
    inverts* R2; try solve[inverts R1].
    inverts H0.
    inverts H7.
  - inverts Val.
    forwards*: value_nlam H1.
    inverts typ; try solve[inverts H0].
    inverts* R2.
    forwards*: TypedReduce_unique H0 H11. 
    forwards*: TypedReduce_unique H0 H10. inverts H6.
    inverts H0. 
Qed.


Lemma vval_val: forall v,
  vvalue v -> value v.
Proof.
  introv val.
  inductions val; eauto.
Qed.

Lemma sfill_eq: forall E0 e0 E e1 r1 r2,
  simpl_fill E0 e0 = simpl_fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  simpl_wf E ->
  simpl_wf E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold simpl_fill in *;  intros.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_walue red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_walue red2.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red2.
Qed.

Lemma principle_uniq: forall v A B,
 walue v ->
 principal_type v = A ->
 principal_type v = B ->
 A = B.
Proof.
  introv val typ1 typ2.
  inductions val; try solve[inverts* typ1; inverts typ2].
Qed.



Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2.
  - (* \x.e:a->b ---> \x.e:a->b:a->b *)
    inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2.
   
  - (* i ---> i:int *)
    inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - (* e1 e2 ---> e1' e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1];
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1].
    + forwards*: sfill_eq H0.             
      destruct H3. subst. inverts Typ; 
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      destruct E0; unfold simpl_fill in H3; inverts H3.
      forwards*: Typing_chk H8. inverts H3.
      forwards*: IHRed1 Red1 H2. congruence.
      forwards*: IHRed1 Red1 H2. congruence. 
      forwards*: IHRed1 Red1 H9. congruence.
      forwards*: IHRed1 Red1 H10. congruence.
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ;
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      destruct E0; unfold simpl_fill in H3; inverts H3.
      forwards*: Typing_chk H8. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      forwards*: IHRed1 Red1 H2. congruence.
      forwards*: IHRed1 Red1 H9. congruence.
      forwards*: IHRed1 Red1 H10. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_walue Red1.
      forwards*: step_not_walue Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      inverts Red1.
      destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_walue Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1. 
      forwards*: step_not_value Red1.
      forwards*: step_not_walue Red1.
  - (* e1 e2 ---> blame e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
     destruct H3. subst. inverts Typ; 
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      destruct E0; unfold simpl_fill in H3; inverts H3.
      forwards*: Typing_chk H8. inverts H3.
      forwards*: IHRed1 Red1 H2. congruence.
      forwards*: IHRed1 Red1 H2. congruence.
      forwards*: IHRed1 Red1 H9. congruence.
      forwards*: IHRed1 Red1 H10. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_walue Red1.
      forwards*: step_not_walue Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      inverts Red1.
      destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_walue Red1.
    + 
      destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      inverts H1.
      forwards*: step_not_value Red1.
      inverts* Red1.
      destruct E; unfold simpl_fill in H1; inverts* H1.
    +
      destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
  - (* e:a ---> e':a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence];
    try solve[forwards*: step_not_walue Red1].
    inverts Typ. inverts H0. forwards*: IHRed1 H2; congruence.
    inverts H8.
    exfalso; apply H4; eauto.
    inverts Typ. inverts H0. forwards*: IHRed1 H2; congruence.
    inverts H8.
    exfalso; apply H4; eauto.
  - (* e:a ---> blame:a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: step_not_walue Red1.
    forwards*: step_not_walue Red1.
    inverts Typ. inverts H0. forwards*: IHRed1 H2; congruence.
    inverts H8.
    exfalso; apply H4; eauto.
    inverts Typ. inverts H0. 
    forwards*: step_not_value Red1. 
    forwards*: step_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2;
    forwards*: step_not_walue H4];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence];
    try solve[inverts H7];
    try solve[inverts H5].
    forwards*: principle_uniq H0 H5.
    inverts* H2.
  - (* \x.e v *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2;
    forwards*: step_not_walue H4;
    forwards*: step_not_walue H4];
    try solve[inverts* H0].
    inverts Typ. inverts H2. inverts H10; try solve[inverts H5].
    inverts H12. inverts H13. inverts H8.
    inverts H1;inverts* H7.
    inverts H0; try solve[inverts H10].
    forwards*: TypedReduce_unique H1 H7. congruence.
    forwards*: TypedReduce_unique H1 H7. congruence.
  - (* \x.e:a1->b1:a2->b2 v ---> e[x->v']:b1:b2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2; simpl in *;
    forwards*: step_not_walue H4;
    forwards*: step_not_walue H4];
    try solve[inverts H0];
    inverts Typ. inverts H2.
    inverts H7. inverts H12. 
    forwards*: TypeLists_unique H1 H11. congruence.
    forwards*: TypeLists_unique H1 H11. congruence.
    inverts H2. inverts H12; try solve[inverts H0].
    forwards*: TypeLists_unique H1 H11. congruence.
    forwards*: TypeLists_unique H1 H11. congruence.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1; simpl in *;
    forwards*: step_not_walue H3;
    forwards*: step_not_walue H3];
    try solve[inverts H];
    try solve[inverts H4].
  - (* \x.e:a1->b1:a2->b2 v --> blame *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2; simpl in *;
    forwards*: step_not_walue H4;
    forwards*: step_not_walue H4];
    try solve[inverts H0];
    inverts Typ. 
    inverts H2;inverts H12; try solve[inverts H];
    forwards*: TypeLists_unique H1 H11;congruence.
  - (* v: a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1];
    try solve[inverts H];
    try solve[forwards*: step_not_value H3].    
    inverts* Typ. inverts* H1. inverts* H8; try solve[inverts H].
    forwards*:  TypedReduce_unique H0 H5.
    forwards*:  TypedReduce_unique H0 H5.
  - (* v1+v2-> blame+ v2*)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2;
    forwards*: step_not_value H4; forwards*: step_not_value H4].
    inverts* H1.
    exfalso. apply H5; eauto.
  - (* i+v2-> i+ blame*)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_value H3; forwards*: step_not_value H3].
    inverts* H0.
    exfalso. apply H4; eauto.
  - (* i:a + i: b *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H; inverts* H;
    forwards*: step_not_value H1; forwards*: step_not_value H1].
    inverts* H4.
    exfalso. apply H5; eauto.
    inverts* H4.
    exfalso. apply H2; eauto.
Qed.


