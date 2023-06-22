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



Lemma flike_not_ground: forall v,
 value v ->
 FLike (dynamic_type v) ->
 not(Ground (dynamic_type v)).
Proof.
  introv val fl.
  inductions val; simpl in *; try solve[inverts* fl;
  inverts* H0;inverts* H2];
  try solve[unfold not; intros nt; inverts* nt].
  inverts* fl. inverts H1.
  unfold not; intros nt; inverts* nt.
  inverts* fl. inverts H1.
  unfold not; intros nt; inverts* nt.
Qed.



Lemma Cast_unique: forall v r1 r2 (A: typ) B,
    value v -> Typing nil v Chk B -> Cast v A r1 -> Cast v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2. 
  gen r2 B.
  lets R1': R1.
  inductions R1; introv R2 typ;
    try solve [inverts* R2].
  - inverts* R2; try solve[inverts* H0].
  - inverts* R2; try solve[inverts H].
    inverts* Val; inverts* H;inverts* H0. inverts* H1. inverts H2.
  - inverts* R2; try solve[ inverts* H0].
    +
    inverts Val. rewrite H2 in H1; inverts H1.
    +
    exfalso.
    apply H1.
    eauto.
  - inverts* R2;
    try solve[forwards*: flike_not_ground H];
    try solve[inverts* H].
  - inverts* R2;
    try solve[inverts* H];
    try solve[inverts* H0];
    try solve[inverts* H2].
    +
    inverts Val; try solve[forwards*: flike_not_ground H].
  - inverts* R2; try solve[inverts* H3];
    try solve[inverts* H2];
    try solve[inverts* H1].
    +
    inverts* Val.
    rewrite <- H0 in H2. inverts H2.
    +
    inverts* Val.
    forwards*: flike_not_ground H0.
    +
    exfalso; apply H0;eauto.
  -
    inverts* R2; try solve[inverts* H3];
    try solve[inverts* H1];
    try solve[inverts* H0].
    exfalso; apply H; eauto.
    exfalso; apply H;simpl; eauto.
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
    inverts Typ. inverts H.
    exists*.
  - unfold fill in *.
    inverts Typ.
    inverts H.
    exists*. 
  - unfold fill in *.
    inverts Typ.
    inverts H.
    exists*. 
Qed.


Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* fill -e *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1].
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    destruct E; unfold fill in H0; inverts* H0.
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1.
    inverts H. inverts H2.
  - (* fill -blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1;
    try solve[inverts* H;inverts* H2]].
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1.
    inverts H. inverts H2.
  - (* beta *)
    inverts* Red2; try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H4].
    +
    inverts Typ.
    inverts H2. 
    forwards*: Cast_unique H1 H9.
    congruence.
    +
    inverts Typ.
    inverts H2. 
    inverts H12.
    inverts H10.
    inverts H5. 
    forwards*: Cast_unique H1 H6.
    congruence.
  - (* anno beta -> blame*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H3;inverts* H0;
    forwards*: step_not_value H5;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H5];
    try solve[inverts* H0].
    +
    inverts H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H8.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H7.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H7.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H6.
    congruence.
  - (* annov *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ. inverts H2.
    forwards*: Cast_unique H0 H5.
  - (* add *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3];
    try solve[inverts* H8];
    try solve[inverts* H0].
    +
    inverts Typ.
    inverts H1. inverts H4.
    forwards*: Cast_unique H0 H5.
    congruence.
    +
    inverts Typ.
    inverts H1. 
    forwards*: Cast_unique H0 H3.
    congruence.
  - (* addl *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    +
    inverts Typ.
    inverts H1.
    inverts H4.
    forwards*: Cast_unique H0 H5.
    congruence.
    +
    inverts Typ.
    inverts H1.
    forwards*: Cast_unique H0 H5.
    congruence.
  - (* annotate beta *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H3; 
    forwards*: step_not_value H5; eapply value_fanno; simpl; eauto].
    +
    inverts Typ.
    inverts H3.
    inverts* H6.
    forwards*: Cast_unique H0 H7.
    congruence.
    +
    inverts Typ.
    inverts H3.
    forwards*: Cast_unique H0 H9.
    congruence.
  - (* v1:dyn:dyn->dyn v2 *) 
    inverts* Red2.
    +
    destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2.
    inverts* H1. inverts* H3.
    +
    destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2.
    inverts* H1. inverts* H3.
    +
    inverts* H3.
Qed.


