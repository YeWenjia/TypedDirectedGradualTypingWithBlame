Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  introv.
  induction* A.
Qed.

Lemma TypedReduce_unique: forall v r1 r2 p b (A: typ) B,
    value v -> Typing nil v Chk B -> TypedReduce v p b A r1 -> TypedReduce v p b A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2. 
  gen r2 B.
  lets R1': R1.
  inductions R1; introv R2 typ;
    try solve [inverts* R2].
  - inverts* R2.
    inverts* H0.
    inverts* H0.
    inverts* H0.
  - inverts* R2.
    inverts* H.
    inverts* Val; inverts* H0. inverts* H2. inverts H3.
    inverts H.  inverts H4.
    exfalso. apply H; auto.
    inverts* H0.
    inverts* H.
    inverts* H.
  - inverts* R2.
    inverts* H0.
    inverts H0. 
    exfalso; apply H1; auto.
    inverts H7. 
    exfalso; apply H0; auto.
    inverts Val. rewrite H6 in H2; inverts H2.
    exfalso.
    apply H7.
    eauto.
  - inverts* R2.
    inverts* Val; inverts* H0;
    inverts* H.
    inverts* H1. inverts H2.
    inverts* H. inverts H0.
    exfalso; apply H2; auto.
    inverts* H.
    exfalso.
    apply H0.
    eauto.
  - inverts* R2.
    inverts H2.
    inverts* H.
    inverts* H.
    inverts* H.
    inverts* Val.
    inverts* H3; inverts* H5;inverts* H.
    inverts* H3. 
    inverts* H4.
    inverts H2. inverts H2.  inverts H2.
    inverts H5.
    exfalso.
    apply H; auto.
    exfalso; apply H8.
    apply BA_AB.
    auto.
  - inverts* R2.
    inverts H4.
    inverts* H3.
    inverts* Val.
    rewrite <- H5 in H1.
    inverts* H1.
    inverts* H3.
    inverts* Val.
    inverts* H3; inverts* H1;inverts* H6.
    inverts* H0.
    inverts* H2.
    exfalso.
    apply H6.
    apply sim_refl.
  - inverts* R2.
    inverts* H1.
    inverts* H0.
    exfalso.
    apply H.
    eauto.
    exfalso.
    apply H.
    eauto.
    exfalso.
    apply H.
    apply BA_AB.
    auto.
    exfalso.
    apply H.
    apply sim_refl.
Qed.


Lemma fill_auxi: forall E1 E0 e0 e1 r2 r1,
 fill E0 e0 = fill E1 e1 ->
 wellformed E0 ->
 wellformed E1 ->
 step e0 r1 ->
 step e1 r2 ->
 (E1 = E0)/\ (e0 = e1).
Proof.
  introv eq wf1 wf2 red1 red2. gen E1 e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros. 
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red1.
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red2.
  - inductions E1; unfold fill in *; inverts* eq.    
Qed.

Lemma fill_typ: forall E e1 A,
 wellformed E ->
 Typing nil (fill E e1) Chk A ->
 exists B, Typing nil e1 Chk B.
Proof.
  introv wf Typ. gen e1 A. 
  inductions E; intros.
  - simpl in *.
    inverts Typ. inverts H. inverts H1.
    inverts wf.
    destruct(lambda_decidable e1). 
    exists*.
    inverts* H8.
  - unfold fill in *.
    inverts Typ.
    inverts H.
    inverts H1.
    inverts H9.
    exists*. exists*.
  - unfold fill in *.
    inverts Typ.
    inverts H1.
    inverts H. inverts H7.
    exists*. exists*.
Qed.


Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity].
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity].
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2.
  -  inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H4];
    try solve[inverts* H12];
    try solve[inverts* H0].
    inverts Typ.
    inverts H2.
    inverts H14. 
    forwards*: TypedReduce_unique H1 H9.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H4];
    try solve[inverts* H12];
    try solve[inverts* H0].
    inverts Typ.
    inverts H2.
    inverts H14. 
    forwards*: TypedReduce_unique H1 H13.
    congruence.
    inverts Typ.
    inverts H2.
    inverts H14. 
    forwards*: TypedReduce_unique H1 H13.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H4];
    try solve[inverts* H12];
    try solve[inverts* H0].
    inverts Typ.
    inverts H2.
    inverts H14. 
    forwards*: TypedReduce_unique H1 H13.
    congruence.
    inverts Typ.
    inverts H2.
    inverts H15. inverts H6. 
    forwards*: TypedReduce_unique H1 H13.
    congruence.
   - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H14. 
    forwards*: TypedReduce_unique H0 H8.
    forwards*: TypedReduce_unique H0 H8.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H3; inverts* H3;
    forwards*: step_not_value H5;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H5];
    try solve[inverts H0];
    try solve[inverts H2];
    try solve[inverts H8].
    inverts Typ.
    inverts H3.
    inverts H15. inverts H7.
    forwards*: TypedReduce_unique H1 H14.
    congruence.
    inverts Typ.
    inverts H3.
    inverts H12.
    forwards*: TypedReduce_unique H1 H18.
    congruence.
Qed.


