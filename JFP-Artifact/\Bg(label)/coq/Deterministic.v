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


Lemma flike_not_ground: forall v,
 value v ->
 FLike (principal_type v) ->
 not(Ground (principal_type v)).
Proof.
  introv val fl.
  inductions val; simpl in *; try solve[inverts* fl;
  inverts* H0;inverts* H2];
  try solve[unfold not; intros nt; inverts* nt].
  inverts* fl. inverts H1.
  unfold not; intros nt; inverts* nt.  
Qed.



Lemma TypedReduce_unique: forall v r1 r2 (A: typ) B p b,
    value v -> Typing nil v Chk B -> TypedReduce v p b A r1 -> TypedReduce v p b A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2. 
  gen r2 B.
  lets R1': R1.
  inductions R1; introv R2 typ;
    try solve [inverts* R2].
  - inverts* R2; try solve[inverts* H0].
  - inverts* R2; try solve[inverts H].
    inverts* Val; inverts* H0. inverts* H2. inverts H3.
    inverts H; simpl in *. inverts H4. 
    exfalso. apply H; auto.
    inverts* H. inverts* H.
  - inverts* R2; try solve[ inverts* H7];try solve[inverts* H0];
    try solve[inverts* H3].
    inverts Val. rewrite H6 in H2; inverts H2.
    exfalso.
    apply H7.
    eauto.
  - inverts* R2;
    try solve[forwards*: flike_not_ground H];
    try solve[inverts* H].
  - inverts* R2;
    try solve[inverts* H];
    try solve[inverts* H0];
    try solve[inverts* H1];
    try solve[inverts H9].
  -
    inverts* R2;
    try solve[inverts* H6];
    try solve[inverts* H5];
    try solve[inverts* H].
    inverts H8; simpl;eauto.
    inverts H0.
    exfalso; apply H1; simpl;eauto.
    inverts H8.
    exfalso; apply H6; simpl;eauto.
  - inverts* R2;
    try solve[inverts H3];
    try solve[inverts* H1];
    try solve[inverts* H].
    inverts* Val.
    forwards*: flike_not_ground H.
    exfalso.
    apply H9.
    apply BA_AB; auto.
  - inverts* R2; try solve[inverts* H5];
    try solve[inverts* H4];
    try solve[inverts* H7];
    try solve[inverts* H].
    inverts* Val.
    rewrite <- H6 in H2. inverts H2.
    inverts* Val.
    forwards*: flike_not_ground H3.
    exfalso; apply H7;
    apply sim_refl.
  -
  inverts* R2; simpl in *;try solve[inverts* H7];
  try solve[inverts* H1];
  try solve[inverts* H0].
  exfalso; apply H; eauto.
  exfalso; apply H;simpl; eauto.
  exfalso.
  apply H.
  apply BA_AB; auto.
  exfalso; apply H;
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
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red1.
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red2.
Qed.

Lemma fill_typ: forall E e1 A,
 wellformed E ->
 Typing nil (fill E e1) Chk A ->
 exists B, Typing nil e1 Chk B.
Proof.
  introv wf Typ. gen e1 A. 
  inductions E; intros.
  - simpl in *.
    inverts Typ. inverts H. 
    inverts wf.
    forwards*: Typing_chk H9.
  - unfold fill in *.
    inverts Typ.
    inverts* H.
  - unfold fill in *.
    inverts Typ.
    inverts* H. 
    - simpl in *.
    inverts Typ. inverts H. 
    inverts wf.
    forwards*: Typing_chk H4.
  - unfold fill in *.
    inverts Typ.
    inverts* H.
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
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity];
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1].
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    destruct E; unfold fill in *; inverts* H0;
    try solve[forwards*: step_not_value Red1].
    inverts H. inverts* H4.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H1; inverts* H1;
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
    destruct E; unfold fill in *; inverts* H0;
    try solve[forwards*: step_not_value Red1].
    inverts H. inverts* H4.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H3];
    try solve[inverts* H9];
    try solve[inverts* H0].
  - inverts* Red2;
    try solve[destruct E; unfold fill in H3; inverts* H3;
    forwards*: step_not_value H5;
    forwards*: step_not_value H5];
    try solve[inverts* H1].
    rewrite H10 in *. inverts H1.
    inverts Typ. inverts H1.
    forwards*: TypedReduce_unique H2 H11.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4];
    try solve[inverts* H8];
    try solve[inverts* H0].
    inverts Typ.
    inverts H2.
    forwards*: TypedReduce_unique H0 H8.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H3; inverts* H3;
    forwards*: step_not_value H5;
    forwards*: step_not_value H5];
    try solve[inverts H0].
    rewrite H2 in *. inverts* H13.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H3; inverts* H3;
    forwards*: step_not_value H5;
    forwards*: step_not_value H5];
    try solve[inverts* H1].
    rewrite H10 in *.
    inverts H1.
    inverts Typ.
    inverts H1.
    forwards*: TypedReduce_unique H2 H11.
    congruence.
    rewrite H10 in *.
    inverts H1.
    inverts Typ.
    inverts H1.
    forwards*: TypedReduce_unique H2 H11.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3];
    try solve[inverts* H8];
    try solve[inverts* H0];
    try solve[inverts* H5].
    destruct E; unfold fill in H1; inverts* H1;
    try solve[forwards*: step_not_value H3].
    inverts H2. inverts H5.
    destruct E; unfold fill in H1; inverts* H1;
    try solve[forwards*: step_not_value H3].
    inverts H2. inverts H5.
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in H; inverts* H;
    forwards*: step_not_value H1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H1].
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in H; inverts* H;
    forwards*: step_not_value H1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H1].
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H3].
Qed.


