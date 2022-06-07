Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


Lemma fill_appl : forall e1 e2 l b,
  (e_app e1 l b e2) = (fill (appCtxL e2 l b) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2 l b,
  (e_app e1 l b e2) = (fill (appCtxR e1 l b) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_anno : forall e A l b,
  (e_anno e l b A) = (fill (annoCtx l b A) e).
Proof.
  intros. eauto.
Qed.


Lemma gvalue_decidable: forall e,
  lc_exp e -> gvalue e \/ not(gvalue e).
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
    left. eapply gvalue_fanno; eauto. reflexivity.
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply gvalue_fanno; eauto. reflexivity.
    destruct(eq_type A0);destruct(eq_type B);subst*;
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H5];
    try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
    try solve[left*].
   + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    right; unfold not; intros nt; inverts* nt. inverts* H7.
    right; unfold not; intros nt; inverts* nt. inverts* H3.
  - inductions lc; try solve[exfalso; apply H; auto];
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
Qed.


Theorem variant_calculus_tyred: forall v A l b l0 b0,
 value v -> gtyping nil (trans v) Chk A -> 
 TypedReduce v l0 b0 A (Blame l b) ->
 (trans (e_anno v l0 b0 A) ) ->** (Blame l b).
Proof.
  introv Val Typ Red.
  inductions Red;unfold trans in *; simpl;
  forwards*: gtyping_regular_1 Typ; fold trans in *.
  - inverts Typ. inverts H1. inverts H10. inverts H1.
    inverts H4;
    destruct B; try solve[inverts H2];
    try solve[exfalso;apply H; auto].
    apply gstep_b. apply gStep_annov; eauto.
    apply gTReduce_blame.
    unfold not; intros. inverts H1. 
    unfold not;intros nt; inverts* nt. inverts H11. 
  - 
    inverts Typ. inverts H0. inverts H9. inverts H0. inverts H3; inverts H1.
    inverts H. inverts H1. 
    destruct(eq_type A); destruct (eq_type B); subst.
    apply gstep_b. apply gStep_annov; eauto.
    eapply gvalue_dyn; eauto. eapply gvalue_fanno; eauto. reflexivity.
    apply gTReduce_blame.
    unfold not; intros. inverts H.
    unfold not;intros nt; inverts* nt. 
    eapply gstep_nb. rewrite fill_anno.
    apply gdo_step; eauto.
    apply gStep_annov; eauto. 
    eapply gvalue_fanno; eauto. reflexivity. apply gTReduce_anyd. 
    unfold FLike. split. unfold not; intros nt; inverts* nt.
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    unfold not; intros nt; inverts* nt. inverts H5. apply H1. reflexivity.
    apply gstep_b. apply gStep_annov; eauto.
    apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto. 
    eapply gvalue_fanno; eauto. reflexivity. reflexivity.
    apply gTReduce_blame. 
    unfold not; intros. inverts H.
    unfold not;intros nt; inverts* nt. 
    eapply gstep_nb. rewrite fill_anno.
    apply gdo_step; eauto.
    apply gStep_annov; eauto. 
    eapply gvalue_fanno; eauto. reflexivity. apply gTReduce_anyd. 
    unfold FLike. split. unfold not; intros nt; inverts* nt.
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    unfold not; intros nt; inverts* nt. inverts H5. apply H. reflexivity.
    apply gstep_b. apply gStep_annov; eauto.
    apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
    eapply gvalue_fanno; eauto. reflexivity.  reflexivity.
    apply gTReduce_blame. 
    unfold not; intros. inverts H1.
    unfold not;intros nt; inverts* nt.
    eapply gstep_nb. rewrite fill_anno.
    apply gdo_step; eauto.
    apply gStep_annov; eauto. 
    eapply gvalue_fanno; eauto. reflexivity. apply gTReduce_anyd. 
    unfold FLike. split. unfold not; intros nt; inverts* nt.
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    unfold not; intros nt; inverts* nt. inverts H6. apply H1. reflexivity.
    apply gstep_b. apply gStep_annov; eauto.
    apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto. 
    eapply gvalue_fanno; eauto. reflexivity. reflexivity.
    apply gTReduce_blame. 
    unfold not; intros. inverts H3.
    unfold not;intros nt; inverts* nt.  
Qed.



Lemma lam_value_step: forall v A B l b ,
 gvalue v ->
 principal_type v = t_arrow A B ->
 e_anno v l b t_dyn ->** (Expr (e_anno v l b t_dyn)) /\ gvalue (e_anno v l b t_dyn) /\ (t_arrow A B = t_arrow t_dyn t_dyn) \/
 e_anno v l b t_dyn ->** (Expr (e_anno (e_anno v l b (t_arrow t_dyn t_dyn)) l b t_dyn)) /\ gvalue (e_anno (e_anno v l b (t_arrow t_dyn t_dyn)) l b t_dyn).
Proof.
  introv val typ.
  forwards*: gvalue_lc val. inverts val; try solve[inverts* typ]. inverts typ.
  + destruct(eq_type A);destruct(eq_type B); substs*.
  - right. split. 
    eapply gstar_trans. 
    apply gstar_one.
    apply gStep_annov;try solve [unfold not; intros nt; inverts* nt; inverts H2; exfalso; apply 
    H1; auto];eauto.
    apply gTReduce_anyd. unfold FLike.
    split. unfold not; intros nt; inverts* nt. 
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    unfold not; intros nt; inverts* nt. inverts* H5.
    apply gstep_refl; auto. 
    eapply gvalue_dyn; eauto.
    eapply gvalue_fanno; eauto.  reflexivity.
  - right. split. 
  eapply gstar_trans. 
  apply gstar_one.
  apply gStep_annov;try solve [unfold not; intros nt; inverts* nt; inverts H2; exfalso; apply 
  H1; auto];eauto.
  apply gTReduce_anyd. unfold FLike.
  split. unfold not; intros nt; inverts* nt. 
  split. unfold not; intros nt; inverts* nt. simpl; eauto.
  unfold not; intros nt; inverts* nt. inverts* H5.
  apply gstep_refl; auto. 
  eapply gvalue_dyn; eauto.
  eapply gvalue_fanno; eauto.  reflexivity.
  - right. split. 
  eapply gstar_trans. 
  apply gstar_one.
  apply gStep_annov;try solve [unfold not; intros nt; inverts* nt; inverts H2; exfalso; apply 
  H1; auto];eauto.
  apply gTReduce_anyd. unfold FLike.
  split. unfold not; intros nt; inverts* nt. 
  split. unfold not; intros nt; inverts* nt. simpl; eauto.
  unfold not; intros nt; inverts* nt. inverts* H6.
  apply gstep_refl; auto. 
  eapply gvalue_dyn; eauto.
  eapply gvalue_fanno; eauto.  reflexivity.
Qed.

Lemma lam_value_tred: forall v A B l b ,
 gvalue v ->
 principal_type v = t_arrow A B ->
 gTypedReduce v l b t_dyn (Expr (e_anno v l b t_dyn)) /\ gvalue (e_anno v l b t_dyn) \/
 gTypedReduce v l b t_dyn (Expr (e_anno (e_anno v l b (t_arrow t_dyn t_dyn)) l b t_dyn)) /\ gvalue (e_anno (e_anno v l b (t_arrow t_dyn t_dyn)) l b t_dyn).
Proof.
  introv val typ.
  forwards*: gvalue_lc val. inverts val;inverts* typ. 
  + destruct(eq_type A);destruct(eq_type B); substs*.
  - right. split. 
    apply gTReduce_anyd. unfold FLike.
    split. unfold not; intros nt; inverts* nt. 
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    eapply gvalue_dyn; eauto.
    eapply gvalue_fanno; eauto.  reflexivity.
  - right. split. 
    apply gTReduce_anyd. unfold FLike.
    split. unfold not; intros nt; inverts* nt. 
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    eapply gvalue_dyn; eauto.
    eapply gvalue_fanno; eauto.  reflexivity.
  - right. split. 
    apply gTReduce_anyd. unfold FLike.
    split. unfold not; intros nt; inverts* nt. 
    split. unfold not; intros nt; inverts* nt. simpl; eauto.
    eapply gvalue_dyn; eauto.
    eapply gvalue_fanno; eauto.  reflexivity.
Qed.




Lemma value_gvalue:forall v dir A,
 gtyping nil (trans v) dir A ->
 value v ->
 exists v', (trans v) ->** (Expr v') /\ gvalue v'.
Proof.
  introv typ val. gen A.
  inductions val; intros;simpl.
  - destruct A.
    + exists. split. apply gstar_one; eauto.
      apply gStep_annov;try solve [unfold not; intros nt; inverts* nt];eauto. eauto.
    + inverts* typ. inverts* H6; inverts H; inverts H0. inverts H. inverts H8. inverts H; inverts H2.
    + exists. split*.
  - destruct C.
    + inverts typ. inverts H7. inverts H0; inverts H1.
      inverts H0. inverts H9. inverts H0; inverts H3.
    + forwards*: gtyping_regular_1 typ. inverts H0. inverts H2.
      exists. split*. eapply gvalue_fanno; eauto. 
      eapply gvalue_fanno; eauto. reflexivity. reflexivity.
    + simpl in *. forwards*: gtyping_regular_1 typ. inverts H0. inverts H2.
      assert(gvalue (e_anno (e_abs (trans e)) l1 b1 (t_arrow A B)) ); eauto.
      eapply gvalue_fanno; eauto. reflexivity.
      forwards*: lam_value_step H0.
Qed.

Lemma gTred_value: forall v v'  p b A,
  gvalue v->
  gTypedReduce v p b A (Expr v') ->
  gvalue v'.
Proof.
  introv Val Red.
  inductions Red; eauto.
  - apply gvalue_dyn; eauto.
    inverts H.
    inverts H1.
    inverts Val; inverts* H2.
    eapply gvalue_fanno; eauto.
    reflexivity.
  - inverts Val.
    inverts H.
    inverts H2.
    inverts* H4.
    inverts* H0.
    rewrite <- H4 in H3.
    inverts H3.
  - inverts* Val.
Qed.


Lemma typlist3_typlist4: forall v A3 A1 l1 b1 l2 b2 l3 b3 l b, 
 value v ->
 TypeLists v [t_typs A3 l1 b1 ;t_typs t_dyn l2 b2; t_typs A1 l3 b3] (Blame l b) ->
 TypeLists v [t_typs A3 l1 b1; t_typs A1 l3 b3] (Blame l b).
Proof.
  introv val tl.
  inverts tl;try solve[inverts val]; try solve[inverts H12]. 
  inverts H7.  inverts H10; try solve[inverts H12].
  forwards*: TypedReduce_prv_value H6. forwards*: value_lc H.
  forwards*: TypedReduce_prv_value H9. forwards*: value_lc H1.
  forwards*: TypedReduce_transr H9 H11.
  forwards*: TypedReduce_prv_value H6. 
  forwards*: TypedReduce_transr H9 H12.
  inverts H10. exfalso; apply H; eauto.
  apply TLists_consb; eauto.
Qed.


Lemma typlist_gtyplist: forall v A0 A1 l1 b1 l2 b2 l b,
  value v ->
  lc_exp (trans v) ->
  gtyping [] (trans v) Chk A0 ->
  TypeLists v [ t_typs A0 l1 b1; t_typs A1 l2 b2] (Blame l b) ->
  sim A0 A1 ->
  exists v', (trans v) ->** (Expr v') /\ gvalue v' /\ gTypeLists v' [ t_typs A0 l1 b1; t_typs A1 l2 b2] (Blame l b).
Proof.
  introv val lc typ typlist sim.
  inverts typlist.
  - inverts H7; try solve[inverts H10].
    + (* a1 blame *)
      inverts val;inverts H6; inverts* H9;try solve[inverts H10]; try solve[inverts sim]; simpl in *.
      * (* i:a0 *)
        inverts typ. inverts H. inverts H14. inverts H.
        inverts H3. inverts H0; try solve[exfalso; apply H8; auto]. 
        (* i:int-> a0 a1 *)
        exists. split. apply gstar_one; eauto.
        apply gStep_annov;try solve [unfold not; intros nt; inverts* nt];eauto. split*. 
        eapply gTLists_cons; auto.
        assert(not(syntax_ott.sim A1 t_int)). unfold not; intros nt. apply H8. apply BA_AB; auto.
        eapply gTLists_consb; auto.
        (* i:dyn-> a0 a1 *)
        inverts* H13.
        exists. split. apply gstep_refl; eauto.
        split*. 
        eapply gTLists_cons; auto.
        assert(not(syntax_ott.sim A1 t_int)). unfold not; intros nt. apply H8. apply BA_AB; auto.
        eapply gTLists_consb; auto.
      *
        inverts lc. inverts H1.
        inverts typ. inverts H0. inverts H15. inverts H0.
        inverts sim; inverts H14.
        inverts H6.
        assert(gvalue((e_anno (e_anno (e_abs (trans e)) l2 b0 (t_arrow A B)) l3 b2 (t_arrow C D)))).
        eapply gvalue_fanno; eauto. eapply gvalue_fanno;eauto. reflexivity. reflexivity.
        forwards*: lam_value_tred H0. inverts H6. inverts H8.
        exists. split. apply gstep_refl; eauto.
        split*.
        eapply gTLists_cons; auto.
        apply H6.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        inverts H8.
        exists. split. apply gstep_refl; eauto.
        split*.
        eapply gTLists_cons; auto.
        apply H6.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        
        assert(gvalue(e_anno (e_abs (trans e)) l2 b0 (t_arrow A B))).
        eapply gvalue_fanno; eauto. reflexivity.
        forwards*: lam_value_step H0. inverts H6. inverts H8. inverts H9. inverts H10.
        exists. split. apply H6.
        split*.
        eapply gTLists_cons; auto.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        inverts H8.
        exists. split. apply H6.
        split*.
        eapply gTLists_cons; auto.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
    + inverts val; inverts H6; inverts* H10;try solve[inverts* H9];try solve[inverts sim]; simpl in *.
      * (* i:a0 *)
        inverts typ. inverts H. inverts H14. inverts H.
        inverts H3. inverts H0; try solve[exfalso; apply H8; auto]. 
        (* i:int-> a0 a1 *)
        exists. split. apply gstar_one; eauto.
        apply gStep_annov;try solve [unfold not; intros nt; inverts* nt];eauto. split*. 
        eapply gTLists_cons; auto.
        assert(not(syntax_ott.sim A1 t_int)). unfold not; intros nt. apply H8. apply BA_AB; auto.
        eapply gTLists_consb; auto.
        (* i:dyn-> a0 a1 *)
        inverts* H13.
        exists. split. apply gstep_refl; eauto.
        split*. 
        eapply gTLists_cons; auto.
        assert(not(syntax_ott.sim A1 t_int)). unfold not; intros nt. apply H8. apply BA_AB; auto.
        eapply gTLists_consb; auto.
      *
        inverts lc. inverts H1.
        inverts typ. inverts H0. inverts H15. inverts H0.
        inverts sim; inverts H14.
        inverts H6. 
        assert(gvalue((e_anno (e_anno (e_abs (trans e)) l2 b0 (t_arrow A B)) l3 b2 (t_arrow C D)))).
        eapply gvalue_fanno; eauto. eapply gvalue_fanno;eauto. reflexivity. reflexivity.
        forwards*: lam_value_tred H0. inverts H6. inverts H8.
        exists. split. apply gstep_refl; eauto.
        split*.
        eapply gTLists_cons; auto.
        apply H6.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        inverts H8.
        exists. split. apply gstep_refl; eauto.
        split*.
        eapply gTLists_cons; auto.
        apply H6.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        
        assert(gvalue(e_anno (e_abs (trans e)) l2 b0 (t_arrow A B))).
        eapply gvalue_fanno; eauto. reflexivity.
        forwards*: lam_value_step H0. inverts H6. inverts H8. inverts H9. inverts H10.
        exists. split. apply H6.
        split*.
        eapply gTLists_cons; auto.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
        inverts H8.
        exists. split. apply H6.
        split*.
        eapply gTLists_cons; auto.
        eapply gTLists_baseb; eauto.
        apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
  -
    inverts val; inverts typ; simpl in *.
    +
    inverts H7.
    inverts* H. inverts H9. inverts H. inverts H3; try solve[exfalso; apply H11; auto].
    exists. split. 
    apply gstep_refl; eauto.
    split*.
    eapply gTLists_consb; auto.
    apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
    +
    inverts H0. inverts H11. inverts H0. inverts H7. inverts H1; inverts H4.
    forwards*: gtyping_regular_1 H13.
    assert(gvalue((e_anno (e_abs (trans e)) l1 b1 (t_arrow A B)))).
    eapply gvalue_fanno; eauto.  reflexivity.
    forwards*: lam_value_step H1. inverts H4. inverts H6. inverts H7. inverts H8.
    exists. split. apply gstep_refl; eauto.
    split*.
    eapply gTLists_consb; eauto.
    apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
    inverts H6.
    exists. split. apply H4.
    split*.
    eapply gTLists_consb; eauto.
    apply gTReduce_blame;try solve [unfold not; intros nt; inverts* nt];eauto.
Qed.



Lemma glist_blame: forall e x A0 A1 A B1 l1 b1 l2 b2 l3 b3 l b,
 gvalue x ->
 lc_exp (e_abs e) ->
 gTypeLists x [t_typs A0 l3 (negb b3); t_typs A1 l2 (negb b2) ] (Blame l b) ->
 e_app (e_anno (e_anno (e_abs e) l1 b1 (t_arrow A1 B1)) l2 b2 (t_arrow A0 A)) l3 b3 x ->** (Blame l b).
Proof.
  introv val lc ls.
  inverts ls. inverts H7.
  -
    eapply gstar_transb.
    apply gstar_one.
    apply gStep_abeta; eauto.
    eapply gvalue_fanno;eauto. reflexivity.
    rewrite fill_anno.
    apply gstep_b.
    apply gblame_step;eauto.
    apply gStep_betap; eauto.
    eapply gvalue_fanno;eauto. reflexivity.
    forwards*: gTred_value H6.
  -
    inverts H10.
  -
    eapply gstar_transb.
    apply gstar_one.
    apply gStep_abeta; eauto.
    eapply gvalue_fanno;eauto. reflexivity.
    rewrite fill_anno.
    apply gstep_b.
    apply gblame_step;eauto.
    apply gStep_betap; eauto.
    eapply gvalue_fanno;eauto. reflexivity.
    forwards*: gTred_value H6.
  -
    apply gstep_b.
    apply gStep_betap; eauto.
    eapply gvalue_fanno;eauto. eapply gvalue_fanno;eauto. reflexivity. reflexivity.
Qed.


Theorem variant_calculus: forall e dir A l b ,
 gtyping nil (trans e) dir A -> step e (Blame l b) 
-> (trans e) ->** (Blame l b).
Proof with eauto.
  introv Typ Red. gen dir A.
    inductions Red; intros; eauto; unfold trans; simpl;
    forwards*: gtyping_regular_1 Typ; fold trans.
  - destruct E; unfold simpl_fill in *; inverts* Typ.
    + forwards*: IHRed H8. inverts H0.
      apply multi_blame_app2...
    + inverts* H0. inverts H1. forwards*: IHRed H11. inverts H. 
      apply multi_blame_app2 ...
    + forwards*: IHRed H9. inverts H;simpl.
      inverts H3.
      forwards*: value_gvalue H. inverts H2. inverts H3.
      eapply gstar_transb.
      apply gmulti_red_app2... inverts* H0.
       apply multi_blame_app; eauto.
       eapply gstar_transb.
       apply gmulti_red_app2... inverts* H0.
        apply multi_blame_app; eauto.
        forwards*: gtyping_regular_1 H8.
        simpl; eauto. 
    + inverts* H0. inverts H1. forwards*: IHRed H12. inverts H; simpl.
      inverts H4.
       forwards*: value_gvalue H. inverts H1. inverts H4.
      eapply gstar_transb.
      apply gmulti_red_app2... 
       apply multi_blame_app; eauto.
       eapply gstar_transb.
       apply gmulti_red_app2... 
        apply multi_blame_app; eauto.
        forwards*: gtyping_regular_1 H11.
        simpl; eauto. 
    + inverts* H1.
    + inverts* H1.
  - inverts* Typ. forwards*: IHRed H8. 
    + apply multi_blame_anno; eauto.
    + inverts H1. forwards*: IHRed H10. 
      apply multi_blame_anno; eauto.
  - inverts H0; simpl in *.   
   +
     inverts Typ.
     *
     inverts H10.
     forwards*: gtyping_regular_1 H11. inverts H5. inverts H4; inverts H6.
     forwards*: gtyping_regular_1 H14.
     apply BA_AB in H9. 
     forwards*: typlist3_typlist4 H1.
     forwards*: typlist_gtyplist H0.
     inverts H6. inverts H8. inverts H10.
     eapply gstar_transb.
     eapply gmulti_red_app.
     eapply gvalue_fanno;eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
     apply H6.
     forwards*: glist_blame H8 H13.
     *
     inverts H0. inverts H12.
     forwards*: gtyping_regular_1 H13. inverts H7. inverts H6; inverts H8.
     apply BA_AB in H11.
     forwards*: gtyping_regular_1 H16.
     forwards*: typlist3_typlist4 H1.
     forwards*: typlist_gtyplist H7.
     inverts H8. inverts H10. inverts H12. 
     eapply gstar_transb.
     eapply gmulti_red_app.
     eapply gvalue_fanno;eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
     apply H8.
     forwards*: glist_blame H10 H15.
   +
   inverts H1; try solve[inverts* H10]; try solve[inverts* H11]. 
   inverts* H14.
   inverts Typ. inverts H9. inverts H4. inverts H0. inverts H1. inverts H7.
   inverts H0. inverts H11. inverts H6. inverts H0. inverts H5. inverts H9.
  - inverts H1.
     inverts Typ. 
    + 
      forwards*: variant_calculus_tyred H0.
    + inverts H1.
      forwards*: variant_calculus_tyred H0.
  - inverts* Typ. inverts* H3. 
  - inverts* Typ. inverts* H2. 
Qed.

