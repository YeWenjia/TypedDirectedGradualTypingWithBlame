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


Lemma TypedReduce_unique: forall v r1 r2 B (A: typ),
    walue v -> Typing nil v Chk B -> TypedReduce v A r1 -> TypedReduce v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
Qed.


Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red;try solve[inverts* Val]; eauto.
Qed.

Lemma TypedReduce_prv_walue: forall v A v',
    walue v -> TypedReduce v A (Expr v') -> walue v'.
Proof.
  intros v A v' Val Red.
  inductions Red;try solve[inverts* Val]; eauto.
Qed.

Lemma principle_inf: forall v A,
  ssval v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ]; simpl in *.
  inverts* Typ.
  forwards*: IHVal1 H2.
  forwards*: IHVal2 H3.
  subst*.
Qed. 


Lemma sim_sym: forall t1 t2,
 sim t1 t2 ->
 sim t2 t1.
Proof.
  introv sim.
  inductions sim; eauto.
Qed.


Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
  - inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H; destruct H0; try solve[left;  eauto];
    try solve[ right;
    unfold not; intros nt; inverts* nt]. 
    apply sim_sym in H; auto.
    right. unfold not; intros nt;inverts nt. 
    apply H.
    apply sim_sym in H4; auto.
  -
    inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H; destruct H0; try solve[left;  eauto];
    try solve[ right;
    unfold not; intros nt; inverts* nt]. 
Qed.


Lemma TypedReduce_preservation: forall v A v' B,
    walue v -> TypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red;try solve[inverts* Val]; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  -
  inverts Typ. inverts* H2. 
  inverts* H7; try solve[inverts H0]. 
  forwards*: principle_inf H2.
  rewrite H7 in *.
  eapply Typ_anno; eauto.
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
    try solve[inverts H0;inverts* H8];
    try solve[inverts H11].
    forwards*: TypedReduce_unique H0 H10.
  - 
    inverts typ; try solve[inverts H0].
    inverts* R2; try solve[inverts H10].
    forwards*: TypedReduce_unique H0 H7. 
  - 
    inverts* R2; try solve[inverts* R1]. 
    forwards*: TypedReduce_unique H0 H5. inverts* H1.
    forwards*: TypedReduce_prv_walue H0.   
    forwards*: TypedReduce_preservation H0.
    forwards* h1: Typing_chk H2. inverts h1.
    forwards*: IHR1 R1 H7.
    forwards*: TypedReduce_unique H0 H6. 
    congruence.
  - 
    inverts* R2.
    forwards*: TypedReduce_unique H0 H6. 
    forwards*: TypedReduce_unique H0 H5.
    congruence. 
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
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_walue red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_walue red2.
  -
    inductions E; unfold simpl_fill in *; inverts* eq.
  -
    inductions E; unfold simpl_fill in *; inverts* eq.
Qed.

Lemma principle_uniq: forall v A B,
 value v ->
 principal_type v = A ->
 principal_type v = B ->
 A = B.
Proof.
  introv val typ1 typ2.
  inductions val; try solve[inverts* typ1; inverts typ2].
Qed.



Lemma nlam_exists: forall e,
 lc_exp e ->
 not(nlam e) ->
 exists e', e = (e_abs e') .
Proof.
  introv lc nl.
  inductions lc; try solve[exfalso; apply nl;eauto].
  exists*. 
Qed.


Lemma fill_chk:  forall E e A,
  nil ⊢ simpl_fill E e ⇐  A ->
  exists B, nil ⊢ e ⇐  B .
Proof.
  introv typ.
  destruct(lambda_decidable e).
  -
  destruct E; unfold simpl_fill in *;
  try solve[inverts* typ;inverts* H0].
  -
  forwards* h1: nlam_exists H.
  forwards* h2: Typing_regular_1 typ.
  destruct E; unfold simpl_fill in *; inverts* h2.
  inverts* h1.
  inverts typ. destruct E; unfold simpl_fill in *; inverts* H0.
  inverts* H0; 
  try solve[destruct E; unfold simpl_fill in *; inverts* H3].
  destruct E; unfold simpl_fill in *; inverts* H3.
  inverts* H4.
  destruct E; unfold simpl_fill in *; inverts* H3.
  inverts* H4.
  inverts* H6.
  destruct E; unfold simpl_fill in *; inverts* H3.
  inverts* H4.
  inverts* H6.
  destruct E; unfold simpl_fill in *; inverts* H3.
  inverts* H4.
  destruct E; unfold simpl_fill in *; inverts* H3.
  inverts* H4.
Qed.



Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* \x.e:a->b ---> \x.e:a->b:a->b *)
    inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H3. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H4.
  - (* i ---> i:int *)
    inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - (* \x.e:dyn ---> \x.e:?->?:dyn *)
    inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H2. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H3. destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H4.
  - (* (s1:a, s2:b) *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value Red1].
  - (* e1 e2 ---> e1' e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1];
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
    forwards*: step_not_walue Red1;
    forwards*: step_not_walue Red1].
    + forwards*: sfill_eq H0.             
      destruct H3. subst. inverts Typ; 
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      forwards* h1: Typing_chk H3. inverts h1.
      forwards* h2: fill_chk H6. inverts h2.
      forwards*: IHRed1 Red1 H2. congruence.
    + forwards*: sfill_eq H0.             
      destruct H3. subst. inverts Typ; 
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      forwards* h1: Typing_chk H3. inverts h1.
      forwards* h2: fill_chk H6. inverts h2.
      forwards*: IHRed1 Red1 H2. congruence.
    + destruct E; unfold simpl_fill in *; inverts* H1.
      forwards*: step_not_walue Red1.
      forwards*: step_not_walue Red1.
    + destruct E; unfold simpl_fill in *; inverts* H0. 
      forwards*: step_not_value Red1.
      forwards*: step_not_walue Red1.
      inverts H. inverts H2.
  - (* e1 e2 ---> blame e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_walue Red1];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
     destruct H3. subst. inverts Typ; 
      try solve[destruct E0; unfold simpl_fill in H3; inverts H3].
      forwards* h1: Typing_chk H3. inverts h1.
      forwards* h2: fill_chk H6. inverts h2.
      forwards*: IHRed1 Red1 H2. congruence.
    +
    destruct E; unfold simpl_fill in *; inverts* H1. 
      forwards*: step_not_value Red1.
      forwards*: step_not_walue Red1.
    +
    destruct E; unfold simpl_fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_walue Red1.
    inverts H. inverts H2.
  - (* e:a ---> e':a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence];
    try solve[forwards*: step_not_walue Red1].
    inverts Typ. inverts H0. forwards*: IHRed1 H3; congruence.
  - (* e:a ---> blame:a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in *; inverts* H;
    forwards*: step_not_walue Red1;
    forwards*: step_not_walue Red1];
    try solve [inverts Typ; inverts H; forwards*: IHRed1 H1; congruence].
    forwards*: step_not_walue Red1.
    forwards*: step_not_walue Red1.
    inverts Typ. inverts H. 
    forwards*: step_not_walue Red1. 
  - (* v \x.e *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H3; inverts* H3;
    forwards*: step_not_walue H5];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence];
    try solve[inverts H5];
    try solve[inverts H7;inverts* H11];
    try solve[inverts H8].
    rewrite <- H0 in *.
    forwards*: pattern_abs_uniq H1 H7. congruence.
  - (* \x.e:a1->b1:a2->b2 v ---> e[x->v']:b1:b2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H3; inverts* H3; simpl in *;
    forwards*: step_not_walue H5;
    forwards*: step_not_walue H5];
    try solve[inverts H0].
    +
    inverts H1. inverts H10.
    +
    inverts Typ. inverts H3.
    inverts H8.
    forwards* h1: pattern_abs_uniq H12 H14. inverts h1.
    forwards* h2: pattern_abs_uniq H2 H12. inverts h2.
    forwards*: TypeLists_unique H1 H11. congruence.
    +
    inverts* H8.
    exfalso; apply H11; simpl ;eauto.
    +
    inverts Typ. inverts H3.
    inverts H8.
    forwards* h1: pattern_abs_uniq H12 H14. inverts h1.
    forwards* h2: pattern_abs_uniq H2 H12. inverts h2.
    forwards*: TypeLists_unique H1 H11. congruence.
  - (* v1 v *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2; simpl in *;
    forwards*: step_not_walue H4;
    forwards*: step_not_walue H4];
    try solve[inverts H];
    try solve[inverts H4].
    inverts* H1.
    exfalso; apply H11; simpl ;eauto.
    inverts H1.
  - (* \x.e:a1->b1:a2->b2 v --> blame *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H3; inverts* H3; simpl in *;
    forwards*: step_not_walue H5;
    forwards*: step_not_walue H5];
    try solve[inverts H0].
    inverts H1. inverts H10. inverts H10.
    inverts Typ. inverts H3.
    inverts H8.
    forwards*: pattern_abs_uniq H2 H14. inverts H3.
    forwards*: pattern_abs_uniq H2 H12. inverts H3.
    forwards*: TypeLists_unique H1 H11. congruence.
  - (* v: a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1];
    try solve[inverts H];
    try solve[forwards*: step_not_walue H4];
    try solve[forwards*: step_not_walue H3];
    try solve[inverts H0].    
    inverts* Typ. inverts* H1. 
    forwards*:  TypedReduce_unique H0 H5.
  - (* v1+v2-> blame+ v2*)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2;
    forwards*: step_not_walue H4; forwards*: step_not_walue H4].
    inverts* H1.
    exfalso. apply H7; eauto.
  - (* i+v2-> i+ blame*)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_walue H3; forwards*: step_not_walue H3].
    inverts* H0.
    exfalso. apply H6; eauto.
  - (* i:a + i: b *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H; inverts* H;
    forwards*: step_not_walue H1; forwards*: step_not_walue H1].
    inverts* H4.
    exfalso. apply H7; eauto.
    inverts* H4.
    exfalso. apply H6; eauto.
  - (* e_l v --> blame *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_walue H3];
    try solve[inverts H];
    try solve[forwards*: step_not_value H3].
    inverts H0.
    exfalso; apply H8; simpl; eauto.
  - (* e_l v --> *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_walue H3];
    try solve[inverts H];
    try solve[forwards*: step_not_walue H3].
    +
    inverts H3.
    exfalso; apply H8; simpl; eauto.
    +
    forwards*: pattern_pro_uniq H0 H6. inverts* H1.
  - (* e_r v --> blame *)
    inverts* Red2;
   try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
   forwards*: step_not_walue H3];
   try solve[inverts H];
   try solve[forwards*: step_not_walue H3].
   inverts H0.
   exfalso; apply H8; simpl; eauto.
 - (* e_r v --> *)
    inverts* Red2;
   try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
   forwards*: step_not_walue H3];
   try solve[inverts H];
   try solve[forwards*: step_not_walue H3].
   +
   inverts H3.
   exfalso; apply H8; simpl; eauto.
   +
   forwards*: pattern_pro_uniq H0 H6. inverts* H1.
 -
    inverts* Red2;
   try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
   forwards*: step_not_walue H2];
   try solve[inverts H];
   try solve[forwards*: step_not_walue H2].
   +
   destruct E; unfold simpl_fill in H0; inverts* H0.
   inverts H2.
   destruct E; unfold simpl_fill in H0; inverts* H0.
   inverts H1. inverts H3.
   +
   destruct E; unfold simpl_fill in H0; inverts* H0.
   inverts H2.
   destruct E; unfold simpl_fill in H0; inverts* H0.
   inverts H1. inverts H3.
   +
   inverts H4.
  -
  inverts* Red2;
  try solve[destruct E; unfold simpl_fill in *; inverts* H1;
  forwards*: step_not_walue H3];
  try solve[inverts H0];
  try solve[forwards*: step_not_value H3].
  -
  inverts* Red2;
  try solve[destruct E; unfold simpl_fill in *; inverts* H2;
  forwards*: step_not_walue H4];
  try solve[inverts H1];
  try solve[forwards*: step_not_value H3];
  try solve[inverts H7].
  +
  inverts Typ. inverts H2.
  inverts H10. inverts H12.
  forwards*: TypedReduce_unique H1 H7.
  congruence.
Qed.


