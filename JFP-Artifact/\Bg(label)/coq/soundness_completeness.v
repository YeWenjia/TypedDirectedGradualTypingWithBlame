Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        rulesb_inf
        Infrastructure
        Infrastructure_b
        Deterministic
        Typing_b
        Typing
        Type_Safety
        ttyping.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).


(* aux both *)

Lemma nlam_open3: forall e y,
  nlam e ->
  nlam (e ^^ e_var_f y).
Proof.
  introv nl.
  inverts nl; unfold open_exp_wrt_exp;simpl; eauto.
  destruct(lt_eq_lt_dec nat 0).
  inverts* s.
  eauto.
Qed.

Lemma principle_if: forall v A t,
    value v -> typing nil v Inf3 A t -> principal_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.

Lemma principle_if2: forall v A t,
    value v -> ttyping nil v Inf2 A t -> principal_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.


Lemma TypedReduce_walue3: forall v A v' p b,
    value v -> TypedReduce v p b A (e_exp v') -> walue v'.
Proof with auto.
 introv val red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 inverts* H1. inverts* red; try solve[forwards*: abs_nlam].
Qed.




Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma fillb_cast: forall v A p b B,
  (trm_cast v A p b B) = (fillb (castCtxb A p b B )  v).
Proof.
  introv.
  eauto.
Qed.


Lemma fillb_appl: forall e1 e2,
  (trm_app e1 e2) = (fillb (appCtxLb e2)  e1).
Proof.
  introv.
  eauto.
Qed.


Lemma fillb_appr: forall e1 e2,
  (trm_app e1 e2) = (fillb (appCtxRb e1)  e2).
Proof.
  introv.
  eauto.
Qed.



(* one *)


Lemma ttyping_chk: forall G e A t,
  ttyping G e Inf2 A t ->
  exists l b B tt, ttyping G e (Chk2 l b tt) B t.
Proof.
  introv Typ.
  inductions Typ; eauto; try solve[exists label true; eapply ttyp_sim; eauto;unfold not; intros nt; inverts* nt; inverts H0];
  try solve[exists label true; exists;eapply ttyp_sim; eauto;unfold not; intros nt; inverts* nt; inverts H1];
  try solve[exists label true; eapply ttyp_sim; eauto;unfold not; intros nt; inverts* nt; inverts H];
  try solve[exists label true; eapply ttyp_sim; eauto;unfold not; intros nt; inverts* nt; inverts H2].
  exists label true. exists.
  eapply ttyp_abs; eauto.
  exists label true. exists.
  pick fresh y and apply ttyp_abs2;eauto.
Qed.



Lemma value_valueb_chk: forall e t A l b tt,
 ttyping nil e (Chk2 l b tt) A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen A l b tt t.
  inductions H; intros;
  try solve[inverts typ;inverts* H4].
  -
    forwards*: ttyping_regular_3 typ.
    inverts typ; eauto.
    inverts H0. 
    apply valueb_dyn; eauto.
    inverts H0. 
    eapply valueb_dyn; eauto.
    inverts* H6.
  -
    inverts typ. inverts* H6. 
    forwards*: IHvalue. inverts* H11.
    forwards*: principle_if2 H7.
    rewrite H2 in *; inverts* H0.
  -
    forwards*: ttyping_regular_3 typ.
    inverts typ. inverts* H7. 
    forwards*: IHvalue. inverts* H12;
    try solve[forwards*: abs_nlam].
    forwards*: principle_if2 H8.
    rewrite H3 in *; inverts* H0.
Qed.




Lemma valueb_value_chk: forall e t A l b tt,
 ttyping nil e (Chk2 l b tt) A t -> valueb t ->
 value e.
Proof.
  introv typ H. gen A l b tt e.
  inductions H; intros;
  try solve[inverts typ;inverts* H4; inverts* H;
  inverts* H11].
  -
    forwards*: ttyping_regular_1 typ.
    inverts typ; eauto. inverts* H6.
    inverts* H1; try solve[inverts* H0].
    inverts* H13.
  -
    inverts typ. inverts* H5. 
    forwards*: IHvalueb. inverts* H7.
    forwards*: principle_if2 H6.
    inverts* H0. inverts H12.
  -
    forwards*: ttyping_regular_1 typ.
    inverts* typ. inverts* H7.
    forwards*: IHvalueb.
    inverts* H9.  
    forwards*: principle_if2 H8.
    rewrite <- H3 in *; eauto.
    inverts H2. 
    eapply value_dyn; eauto.
    eapply value_dyn; eauto.
    inverts* H14.
Qed.


Lemma value_valueb: forall dir e t A,
 ttyping nil e dir A t -> value e ->
 valueb t.
Proof.
  introv typ H. 
  destruct dir.
  -
  forwards*: ttyping_chk typ. lets(ll&bb&tb&tt&typp):H0.
  forwards*: value_valueb_chk typp.
  -
  forwards*: value_valueb_chk typ.
Qed.



Lemma valueb_value: forall dir e t A,
 ttyping nil e dir A t -> valueb t ->
 value e.
Proof.
  introv typ H. 
  destruct dir.
  -
  forwards*: ttyping_chk typ. lets(ll&bb&tb&tt&typp):H0.
  forwards*: valueb_value_chk typp.
  -
  forwards*: valueb_value_chk typ.
Qed.



Definition Ttyping_typing G dir e A  := 
   match dir with 
    | Chk2 l b B => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma ttyping_typing: forall G dir e  A t,
 ttyping G e dir A t ->
 Ttyping_typing G dir e A.
Proof.
  introv typ.
  inductions typ; unfold Ttyping_typing in *; intros; eauto.
  eapply Typ_app; eauto.
  inverts* IHtyp2.
  eapply Typ_app; eauto.
  inverts* IHtyp2.
Qed.


Lemma typing_ttyping: forall G e t A B,
 ttyping G e Inf2 A t ->
 Typing G e Inf B ->
 A = B.
Proof.
  introv typ1 typ2. gen B.
  inductions typ1;intros; 
  try solve[inductions typ2; eauto].
  -
    inverts* typ2.
    forwards*: binds_unique H0 H4.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    inverts* H. inverts* H3.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    inverts* H.
    inverts* H3.
  -
      inverts typ2.
    forwards*: IHtyp1_1 H2.
    inverts* H0.
Qed.


(* one aux*)

Lemma tTypedReduce_completeness: forall v t B A t' l b ,
    ttyping nil v (Chk2 l b B) A t ->
    valueb t ->
    bstep (trm_cast t l b B A) (t_term t') ->
    (exists  n t2 v',  bbsteps t' (t_term t2) n /\ TypedReduce v l b A (e_exp v') /\
    ttyping nil v' Inf2 A t2 /\ 0<=n <= 1) \/ (bstep t' (t_blame l b) /\ (TypedReduce v l b A (e_blame l b))).
Proof.
    introv typ val red.
    forwards*: valueb_value val.
    inductions red; try solve[inverts* H].
    -
      destruct E; unfold fillb; inverts x;
      try forwards*: bstep_not_value red.
    -
      inverts* typ. inverts* H5. 
      left. exists*. 
      inverts* H0;try solve[forwards*: abs_nlam].
    -
      inverts* typ. 
      left. exists.
      splits*.
      left.
      exists.
      splits*.
      forwards*: principle_if2 H6.
      inverts H0; inverts H1.
      left.
      exists. splits*.
    -
      inverts* H2. inverts* typ.
      forwards*: principle_if2 H10.
      left.
      exists. splits*.
      eapply TReduce_anyd.
      rewrite H2.
      unfold FLike.
      splits*.
      eapply ttyp_anno; eauto.
    -
    inverts* H2. 
    inverts H3;inverts* typ; try solve[inverts* H9];
    try solve[forwards*: abs_nlam];
    try solve[inverts H11].
    inverts H4; try solve[inverts* H2].
    +
    inverts H11. inverts H6. inverts H11.
    right. rewrite fillb_cast.
    rewrite fillb_cast.
    splits.
    apply blame_stepb;eauto.
    simpl.
    eapply bStep_vanyp;eauto.
    inverts* H13.
    unfold not;intros nt;inverts* nt.
    inverts* H13.
    eapply TReduce_blame;simpl;eauto.
    unfold not;intros nt;inverts* nt.
    +
    forwards* h1: ttyping_regular_3 H11.
    inverts H11; try solve[forwards*: abs_nlam]. 
    inverts H13; try solve[forwards*: abs_nlam].
    inverts h1.  
    left.
    exists. splits.
    eapply sstar_one.
    rewrite fillb_cast.
    apply do_stepb;eauto.
    eapply TReduce_adyn; simpl;eauto.
    unfold FLike; splits*.
    eapply ttyp_anno; eauto.
    omega. omega.
    inverts h1.  
    left.
    exists. splits.
    eapply sstar_one.
    rewrite fillb_cast.
    apply do_stepb;eauto.
    eapply TReduce_adyn; simpl;eauto.
    unfold FLike; splits*.
    eapply ttyp_anno; eauto.
    omega. omega.
    +
    inverts H2.
    inverts H11.
    forwards* h1: ttyping_regular_3 H9.
    inverts val. inverts H12.
    inverts H9. inverts H13; try solve[].
    inverts H9.
    left.
    exists. splits.
    eapply sstar_one.
    rewrite fillb_cast.
    apply do_stepb;eauto.
    eapply  TReduce_dyna; simpl;eauto.
    unfold FLike; splits*.
    eapply ttyp_anno; eauto.
    omega.
    omega.
    -
      inverts* typ. 
      inverts H7; try solve[inverts H2;try solve[inverts H14]].
      +
      inverts H9; try solve[forwards*: abs_nlam].
      forwards*: valueb_value H7.
      forwards*: principle_if2 H7.
      rewrite <- H3.
      left.
      exists. splits*.
      rewrite H3; auto.
      +
      inverts H2;try solve[forwards*: abs_nlam].
      left.
      exists.
      splits*.
      left.
      exists.
      splits*.
Qed.

Lemma value_tred_keep3: forall v A l b t,
 ttyping nil (e_anno v l b A) Inf2 A t ->
 value (e_anno v l b A) ->
 TypedReduce v l b A (e_exp (e_anno v l b A)).
Proof.
 introv typ val.
 inverts* val; simpl in *; eauto.
 inverts H1; inverts* H4.
 -
 inverts typ. inverts* H4. inverts* H7.
 -
 inverts typ. inverts* H2. inverts* H5.
 -
 inverts typ. inverts* H2. inverts* H5.
Qed.


Lemma value_anno:forall v t l b,
 value(e_anno v l b t) ->
 value v.
Proof.
  introv val.
  inverts* val.
Qed.


Lemma val_nlam_wal: forall v,
 value v ->
 nlam v ->
 walue v.
Proof.
  introv val nl.
  inductions val; try solve[inverts* nl].
  -
  inductions val;eauto.
  -
  inductions val;eauto.
Qed.


Lemma tTypedReduce_nlambda2: forall v t A B v' p b,
    value v -> ttyping nil v (Chk2 p b B) A t -> TypedReduce v p b A (e_exp v') -> nlam v'.
Proof with auto.
 introv val typ red.
 inductions red; eauto.
Qed.

Lemma tTypedReduce_walue2: forall v A B v' t p b,
    value v -> ttyping nil v (Chk2 p b B) A t -> TypedReduce v p b A (e_exp v') -> walue v'.
Proof with auto.
 introv val typ red.
 forwards*: Tred_value red.
 forwards*: value_group H.
 inverts* H0.
 forwards*: tTypedReduce_nlambda2 red.
 inverts* H1. inverts H0.
Qed.

Theorem typing_elaborate_completeness_gen1: forall l b B e t t' A n,
  size_exp e + size_term t < n ->
  ttyping nil e (Chk2 l b B) A t ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ ttyping nil e' (Chk2 l b B) A t''  /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen l b B e t t' A.
  induction n; intros; try omega.
  lets Red': Red.
  inductions Red; intros.
  - clear IHRed.
     destruct E; unfold fillb in *; simpl in *.
    +
    forwards* lc: ttyping_regular_1 Typ.
    inverts Typ; simpl in *.
    inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
    *
      forwards*: ttyping_chk H4.
      lets(ll1&bb1&tb1&tb2&ttyp1):H0.
      forwards*: IHn Red ttyp1. simpl in *; omega.
      forwards* lc1:ttyping_regular_3 H7. 
      inverts H1.
      --
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H2.
      inverts lc.
      forwards*: steps_nlam rred1.
      unfold not;intros nt. inverts nt.
      forwards*: value_valueb ttyp1; 
      forwards*: bstep_not_value Red.
      inverts ttyp2;
      try solve[exfalso; apply H1; eauto].
      forwards*: ttyping_typing H4; simpl in *.
      forwards*: preservation_multi_step rred1.
      forwards*: typing_ttyping H14 H6. 
      subst*.
      left.
      exists. splits.
      apply mmulti_red_app2.
      auto. apply rred2.
      apply multi_rred_app2.
      auto. apply rred1.
      eapply ttyp_sim; eauto.
      omega. omega.
      --
      lets(ll&bb&rred1&rred2): H2.
      right. exists.
      splits.
      rewrite fillb_appl.
      apply blame_stepb; auto.
      apply rred1.
      inverts lc.
      apply multi_bblame_app2.
      auto. auto.
    *
      inverts lc.
      destruct(value_decidable e0); auto.
      ++
      lets red: Red.
      forwards*: value_valueb H4.
      inverts Red;
      try solve[
        destruct E; unfold fillb in *; inverts* H3;
        forwards*: bstep_not_value H11
      ];
      try solve[exfalso; apply H15; eauto].
      inverts H0; try solve[inverts H4].
      forwards*: tTypedReduce_completeness red.
      inverts H0.
      --
      inverts H.
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H11.
      left.
      exists. splits.
      apply mmulti_red_app2.
      auto.
      apply rred2.
      eapply stars_trans.
      apply stars_one.
      apply Step_betad; eauto.
      rewrite fill_app.
      apply stars_one.
      apply do_step; eauto.
      apply Step_annov; eauto.
      unfold not;intros nt;inverts* nt. inverts H18.
      unfold fill.
      eapply ttyp_sim; eauto.
      omega. omega.
      --
      lets(rred1&rred2): H11.
      right. exists.
      splits.
      rewrite fillb_appl.
      apply blame_stepb; auto.
      apply rred1.
      eapply stars_transb.
      apply stars_one.
      apply Step_betad;eauto.
      apply step_b.
      rewrite fill_appl.
      eapply blame_step;eauto.
      eapply Step_annov;eauto.
      unfold not;intros nt;inverts* nt. inverts H18.
      ++
      assert(not (valueb t1)).
      unfold not;intros nt.
      forwards*: valueb_value H4.
      inverts* Red;
      try solve[ destruct E; unfold fillb in *;
       inverts* H3].
       --
       destruct E; unfold fillb in *;
       inverts* H3.
       forwards*: ttyping_chk H4.
       lets(ll1&bb1&tb1&tb2&ttyp1):H3.
       forwards*: IHn H11. simpl in *;omega.
       inverts H5.
       ---
       lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H12.
       forwards*: ttyping_typing H4;simpl in H12.
       forwards*: preservation_multi_step rred1.
       forwards*: steps_nlam rred1.
       unfold not; intros nt. inverts nt.
       exfalso; apply H0; eauto.
       inverts ttyp2; 
       try solve[exfalso; apply H14;eauto].
       forwards*: typing_ttyping H20.
       inverts H15.
       inverts H.
       left.
       exists. splits.
       apply mmulti_red_app2.
       auto.
       apply mmulti_red_cast.
       apply rred2.
       apply multi_rred_app2. auto.
       apply rred1.
       eapply ttyp_sim; eauto.
       omega. omega.
       ---
       lets(ll&bb&rred1&rred2): H12.
       right. exists.
       splits.
       rewrite fillb_appl.
       apply blame_stepb; auto.
       rewrite fillb_cast.
       apply blame_stepb; auto.
       apply rred1.
       apply multi_bblame_app2.
       auto. auto.
       --
       inverts H4.
       inverts H16.
       forwards*: valueb_value H13.
       forwards*: principle_if2 H13.
       rewrite <- H4 in H10.
       exfalso; apply H0; eauto.
       forwards*: ttyping_regular_1 H3.
       exfalso; apply H0; eauto.
    *
      forwards*: ttyping_chk H2.
      lets(ll1&bb1&tb1&tb2&ttyp1):H0.
      forwards*: IHn Red ttyp1. simpl in *; omega.
      forwards* lc1:ttyping_regular_3 H6. 
      inverts H1.
      --
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H3.
      inverts lc.
      forwards*: steps_nlam rred1.
      unfold not;intros nt. inverts nt.
      forwards*: value_valueb ttyp1; 
      forwards*: bstep_not_value Red.
      inverts ttyp2;
      try solve[exfalso; apply H1; eauto].
      forwards*: ttyping_typing H2; simpl in *.
      forwards*: preservation_multi_step rred1.
      forwards*: typing_ttyping H15 H11. 
      subst*.
      left.
      exists. splits.
      apply mmulti_red_app2.
      auto. apply rred2.
      apply multi_rred_appv2.
      auto. apply rred1.
      eapply ttyp_sim; eauto.
      omega. omega.
      --
      lets(ll&bb&rred1&rred2): H3.
      right. exists.
      splits.
      rewrite fillb_appl.
      apply blame_stepb; auto.
      apply rred1.
      inverts lc.
      apply multi_bblame_appv2.
      auto. auto.
    +
     forwards* lc: ttyping_regular_1 Typ.
     inverts Typ; simpl in *.
     inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
     *
      inverts lc.
      inverts H7; try solve[
        forwards*: value_valueb H13;
        forwards*: bstep_not_value Red
      ].
      destruct(value_decidable e3); auto.
      ++
      forwards*: value_valueb H13.
      forwards*: tTypedReduce_completeness Red.
      inverts H3.
      ---
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H7.
      inverts H.
      forwards*: valueb_value H4.
      forwards*: principle_if2 H4.
      forwards*: tTypedReduce_walue2 rred1.
      left.
      exists. splits.
      apply mmulti_red_app. auto.
      apply rred2.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      eapply ttyp_sim; eauto.
      omega. omega.
      ---
      lets(rred1&rred2): H7.
      inverts H.
      forwards* h1: valueb_value H4.
      forwards* h2: principle_if2 H4.
      right. exists.
      splits.
      rewrite fillb_appr.
      apply blame_stepb; auto.
      apply rred1.
      apply step_b.
      eapply Step_betap;eauto.
      ++
      assert(not(valueb t0)).
      unfold not;intros nt. forwards*: valueb_value H13.
      lets red: Red.
      inverts Red;
      try solve[destruct E; unfold fill in *; inverts H3;
      try solve[forwards*: bstep_not_value H7]];
      try solve[exfalso; apply H1; eauto].
      destruct E; unfold fill in *; inverts H3; simpl in *.
      forwards*: IHn H13. simpl in *; omega.
      inverts H3.
      ---
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H7.
      forwards*: valueb_value H4.
      inverts* H.
      inverts H.
      forwards*: principle_if2 H4.
      left.
      exists. splits.
      apply mmulti_red_app.
      auto.
      apply mmulti_red_cast.
      apply rred2.
      eapply multi_rred_app.
      apply H.
      auto. 
      apply rred1.
      apply ttyp_sim; eauto.
      eapply ttyp_app; eauto.
      forwards*: steps_not_nlam rred1.
      omega.
      omega.
      ---
      lets(ll&bb&rred1&rred2): H7.
      inverts H.
      forwards*: valueb_value H4.
      forwards* h1: principle_if2 H4.
       right. exists.
       splits.
       rewrite fillb_appr.
       apply blame_stepb; auto.
       rewrite fillb_cast.
       apply blame_stepb; auto.
       apply rred1.
       eapply multi_bblame_app; simpl.
       apply h1.
       auto. auto.
    *
      inverts H. inverts* H1.
    *
      inverts H.
      forwards* h1: valueb_value H2.
      forwards*: ttyping_chk H6.
      lets(ll1&bb1&tb1&tb2&ttyp1):H.
      forwards*: IHn Red. simpl in *. omega.
      inverts H0.
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H3.
      --
      forwards* h2: steps_nlam rred1.
      inverts ttyp2; try solve[
        exfalso; apply h2; eauto
      ].
      forwards*: ttyping_typing H6. 
      forwards* h3: preservation_multi_step rred1. 
      forwards*: typing_ttyping H12 h3. 
      subst*.
      left.
      exists. splits.
      apply mmulti_red_app.
      auto.
      apply rred2.
      eapply multi_rred_appv.
      auto.
      apply rred1.
      apply ttyp_sim; eauto.
      omega.
      omega.
      --
      lets(ll&bb&rred1&rred2): H3.
      right. exists.
      splits.
      rewrite fillb_appr.
      apply blame_stepb; auto.
      apply rred1.
      apply multi_bblame_appv.
      auto.
      auto. 
    +
      forwards* lc: ttyping_regular_3 Typ. inverts lc.
      inverts Typ;
      try solve[forwards*: bstep_not_value Red].
      forwards* lc2: ttyping_regular_1 H6.
      inverts H6;
      try solve[inverts* H0; try solve[
        inverts lc2;
      forwards*: bstep_not_value Red
      ]; try solve[inverts H13]].
      forwards*: IHn H8. simpl in *; omega.
      inverts H0.
      lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): H2.
      --
      left.
      exists. splits.
      apply mmulti_red_cast.
      apply rred2.
      apply multi_rred_anno.
      apply rred1.
      forwards*: steps_not_nlam rred1. 
      omega. omega.
      --
      lets(ll&bb&rred1&rred2): H2.
      right. exists.
      splits.
      rewrite fillb_cast.
      apply blame_stepb; auto.
      apply rred1.
      apply multi_bblame_anno.
      auto. 
  -
    forwards lc: ttyping_regular_1 Typ.
    inverts* Typ; try solve[inverts H1;inverts* H11].
    inverts H6; try solve[inverts H1;inverts H13].
    +
      forwards*: valueb_value H8.
      inverts* H5.
      --
      forwards*: valueb_value H8.
      forwards*: value_tred_keep3 H2.
      forwards*: value_anno H2.
      inverts lc.
      forwards*: TypedReduce_walue3 H3.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      apply stars_one.
      eapply Step_nbeta; simpl;eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H6.
      forwards*: walue_nlam H5.
      pick fresh y.
      forwards*: nlam_open2 y H11 H13.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H12 y.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyping_c_subst_simpl; eauto.
      forwards*: nlam_open3 y H13.
      forwards*: nlam_open2 y H11 H17.
      omega. omega.
      --
      forwards*: valueb_value H8.
      forwards*: value_tred_keep3 H2.
      forwards*: value_anno H2.
      inverts lc. 
      forwards*: TypedReduce_walue3 H3.
      forwards*: nlam_exist H13. inverts H6.
      unfold open_term_wrt_term; simpl.
      pick fresh y. 
       forwards*: not_nlam_open (e_anno e2 l1 b0 t_dyn) y H13.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal;simpl; eauto.
      apply stars_one.
      apply Step_nbeta; eauto.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H11.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H12 y.
      unfold open_term_wrt_term; simpl in *.
      forwards*: ttyping_c_subst_simpl H14 H8.
      omega. omega.
      --
      inverts H2; try solve[inverts H15].
      ++
      forwards*: valueb_value H8.
      forwards*: value_tred_keep3 H2.
      forwards*: value_anno H2.
      inverts lc. inverts H11.
      forwards*: TypedReduce_walue3 H3.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      apply stars_one.
      eapply Step_beta; simpl;eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H11.
      forwards*: walue_nlam H5.
      pick fresh y.
      forwards*: nlam_open2 y H16 H12.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H7 y.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyping_c_subst_simpl; eauto.
      forwards*: nlam_open3 y H16.
      forwards*: nlam_open2 y H12 H17.
      omega. omega.
      ++
      forwards*: valueb_value H8.
      forwards*: value_tred_keep3 H2.
      forwards*: value_anno H2.
      inverts lc. inverts H11.
      forwards*: TypedReduce_walue3 H3.
      forwards*: nlam_exist H16. inverts H11.
      unfold open_term_wrt_term; simpl.
      pick fresh y.
      forwards*: not_nlam_open (e_anno e2 l1 b0 t_dyn) y H16. 
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal;simpl; eauto.
      apply stars_one.
      apply Step_beta; eauto.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H12.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H7 y.
      unfold open_term_wrt_term; simpl in *.
      forwards*: ttyping_c_subst_simpl H13 H8.
      omega. omega. 
    +
      inverts H3.
      --
      forwards* h2: valueb_value H7.
      inverts lc.
      forwards*: val_nlam_wal h2 H11.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      apply Step_nbeta; eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H2.
      pick fresh y.
      forwards*: nlam_open2 y H11 H13.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H12 y.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyping_c_subst_simpl; eauto.
      forwards*: nlam_open3 y H13.
      forwards*: nlam_open2 y H11 H8.
      omega. omega.
      --
      forwards* h2: valueb_value H7.
      inverts lc.
      forwards*: val_nlam_wal h2 H11.
      forwards* h1: nlam_exist H13. inverts h1.
      unfold open_term_wrt_term; simpl.
      pick fresh y.
      forwards*: not_nlam_open e2 y H13.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      apply Step_nbeta; eauto.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H5.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H12 y.
      unfold open_exp_wrt_exp in *.
      simpl in *.
      forwards*:ttyping_c_subst_simpl H6 H7.
      omega. omega.
      --
      inverts* H1; try solve[forwards*: abs_nlam].
      ---
      inverts lc. inverts H3.
      forwards* h2: valueb_value H7.
      forwards*: val_nlam_wal h2 H11.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      apply Step_beta; eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H3.
      pick fresh y.
      forwards*: nlam_open2 y H11 H16.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H6 y.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyping_c_subst_simpl; eauto.
      forwards*: nlam_open3 y H16.
      forwards*: nlam_open2 y H11 H12.
      omega. omega.
      ---
      forwards*: nlam_exist H16. inverts H1.
      unfold open_term_wrt_term; simpl.
      pick fresh y.
      forwards*: not_nlam_open e2 y H16.
      inverts lc. inverts H4.
      forwards* h2: valueb_value H7.
      forwards* h3: val_nlam_wal h2. 
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      apply Step_beta; eauto.
      assert((open_term_wrt_term_rec 0 v t0) = (open_term_wrt_term t0 v)); eauto.
      rewrite H2.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: H6 y.
      unfold open_exp_wrt_exp in *.
      simpl in *.
      forwards*:ttyping_c_subst_simpl H4 H7.
      omega. omega. 
  -
   forwards lc: ttyping_regular_1 Typ.
    inverts Typ. inverts H4;
    try solve[inverts* H;try solve[forwards*: abs_nlam]].
    inverts H6. inverts H4; try solve[inverts* H;try solve[forwards*: abs_nlam]].
    left.
    exists.
    splits.
    apply bbstep_refl.
    apply stars_one.
    apply Step_annov; eauto.
    unfold not;intros nt. inverts nt.
    inverts* H7.
    omega. omega.
  -
    forwards lc: ttyping_regular_1 Typ.
    inverts Typ. inverts H6;
    try solve[inverts* H1;inverts* H7].
    +
      inverts H5; try solve[inverts* H1;inverts* H7].
      inverts H11; try solve[exfalso; apply H15; eauto];
      try solve[inverts* H1;inverts* H7];
      try solve[forwards*: abs_nlam].
      forwards*: valueb_value H8.
      forwards*: value_anno H1.
      inverts H. 
      forwards*: valueb_value H6.
      inverts lc.
      inverts H6;try solve[inverts* H14];
      try solve[inverts* H].
      --
      forwards*: value_tred_keep3 H1.
      forwards*: TypedReduce_walue3 H6.
      inverts H.
      inverts H13.
      forwards* h3: val_nlam_wal H18.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      eapply value_fanno;eauto. reflexivity.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply walue_fanno;eauto. simpl;reflexivity.
      simpl; reflexivity.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyp_sim; eauto.
      omega. omega.
      --
      forwards*: value_tred_keep3 H1.
      forwards*: TypedReduce_walue3 H5.
      inverts H.
      inverts H13.
      inverts H7. inverts H11.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_equal; simpl;eauto.
      eapply value_fanno;eauto. reflexivity.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply walue_fanno;eauto. simpl;reflexivity.
      simpl;reflexivity.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      eapply ttyp_sim; eauto.
      omega. omega.
    +
      forwards*: valueb_value H3.
      inverts H. 
      forwards*: valueb_value H7.
      inverts lc.  
      inverts H3;try solve[inverts* H17];
      try solve[inverts* H].
      --
      forwards* h2: valueb_value H16.
      forwards* h3: val_nlam_wal h2.
      forwards* h4: valueb_value H7.
      forwards* h5: val_nlam_wal h4.
      inverts H1.
      inverts H16; try solve[inverts h3].
      inverts H19.
      forwards* h6: principle_if2 H14.
      rewrite h6 in *. inverts H15.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply ttyp_sim; eauto.
      eapply ttyp_anno; eauto.
      omega. omega.
      --
      inverts H1; simpl in *. inverts H16.
      inverts* H2; try solve[forwards*: abs_nlam].
  -
    inverts Typ; try solve[inverts H0;inverts* H6].
    inverts H5; try solve[inverts* H0;inverts* H6].
    forwards*: tTypedReduce_completeness H7 Red'.
    inverts H0.
    *
    lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): H1.
    forwards*: ttyping_regular_1 H7.
    forwards*: valueb_value H7.
    forwards*: tTypedReduce_nlambda2 rred2.
    forwards*: value_decidable (e_anno e0 p b0 t_dyn).
    inverts H4.
    +
    forwards*: value_tred_keep2 rred2. inverts H4.
    left.
    exists. splits.
    apply rred1.
    apply step_refl.
    apply ttyp_sim;auto.
    omega. omega.
    +
    left.
    exists. splits.
    apply rred1.
    apply stars_one.
    apply Step_annov; eauto.
    apply ttyp_sim; eauto.
    omega. omega.
    *
    lets(rred1&rred2):H1.
    inverts* rred2.
    exfalso; apply H0; auto.
  -
    inverts Typ; try solve[exfalso; apply H1; auto].
    inverts H2; try solve[exfalso; apply H0; auto].
    inverts H8; try solve[
      inverts H2; try solve[exfalso; apply H1; auto];
      try solve[forwards*: abs_nlam]
    ].
    forwards*: tTypedReduce_completeness Red'.
    inverts H2.
    *
    lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): H3.
    forwards*: ttyping_regular_1 H13.
    forwards*: valueb_value H13.
    forwards*: tTypedReduce_nlambda2 rred2.
    forwards*: value_decidable (e_anno e0 p b0 t_dyn).
    inverts H8.
    +
    forwards*: value_tred_keep2 rred2. inverts H8.
    left.
    exists. splits.
    apply rred1.
    apply step_refl.
    apply ttyp_sim;auto.
    omega. omega.
    +
    left.
    exists. splits.
    apply rred1.
    apply stars_one.
    apply Step_annov; eauto.
    apply ttyp_sim; eauto.
    omega. omega.
    *
    lets(rred1&rred2):H3.
    inverts* rred2.
    exfalso; apply H2; auto.
  -
    inverts Typ; try solve[exfalso; apply H1; auto].
    inverts H2; try solve[exfalso; apply H0; auto].
    inverts H8; try solve[
      inverts H2; try solve[exfalso; apply H1; auto];
      try solve[forwards*: abs_nlam]
    ].
    forwards*: tTypedReduce_completeness Red'.
    inverts H2.
    *
    lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): H3.
    forwards*: ttyping_regular_1 H13.
    forwards*: valueb_value H13.
    forwards*: tTypedReduce_nlambda2 rred2.
    forwards*: value_decidable (e_anno e0 p b0 (t_arrow A1 B0)).
    inverts H8.
    +
    forwards*: value_tred_keep2 rred2. inverts H8.
    left.
    exists. splits.
    apply rred1.
    apply step_refl.
    apply ttyp_sim;auto.
    omega. omega.
    +
    left.
    exists. splits.
    apply rred1.
    apply stars_one.
    apply Step_annov; eauto.
    apply ttyp_sim; eauto.
    omega. omega.
    *
    forwards* h2: valueb_value H13.
    lets(rred1&rred2):H3.
    lets rred1': rred1.
    inverts rred1.
    destruct E; unfold fillb in *; inverts H2.
    inverts* H9.
    destruct E; unfold fillb in *; inverts H2;
    try solve[forwards*: bstep_not_value H14].
    inverts H13.
    inverts H14; try solve[exfalso; apply H17; auto].
    inverts H19; try solve[inverts H2; try solve[forwards*: abs_nlam]].
    inverts H14.
    inverts h2.
    inverts H10; inverts H13.
    right. 
    exists.
    splits.
    apply rred1'.
    apply step_b.
    apply Step_annov; eauto.
    unfold not;intros nt;inverts nt.
    inverts H20.
  -
    inverts Typ; try solve[exfalso; apply H1; auto].
    inverts H6; try solve[
      inverts H1; try solve[exfalso; apply H1; auto];
      try solve[forwards*: abs_nlam]
    ].
    forwards*: tTypedReduce_completeness Red'.
    inverts H1.
    *
    lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): H2.
    forwards*: ttyping_regular_1 H8.
    inverts H8.
    forwards*: valueb_value H11.
    forwards*: tTypedReduce_nlambda2 rred2.
    forwards*: value_decidable (e_anno e0 p b2 A).
    inverts H5.
    +
    forwards*: value_tred_keep2 rred2. inverts H5.
    left.
    exists. splits.
    apply rred1.
    apply step_refl.
    apply ttyp_sim;auto.
    omega. omega.
    +
    left.
    exists. splits.
    apply rred1.
    apply stars_one.
    apply Step_annov; eauto.
    apply ttyp_sim; eauto.
    omega. omega.
    *
    forwards* h2: valueb_value H8.
    lets(rred1&rred2):H2.
    forwards*: value_decidable (e_anno e0 p b2 A).
    inverts H1.
    forwards*: value_tred_keep2 rred2. inverts H1.
    right. 
    exists.
    splits.
    apply rred1.
    apply step_b.
    apply Step_annov; eauto.
  -
    inverts Typ. inverts H4.
    inverts H6; try solve[inverts H10].
    inverts H10; try solve[forwards*: abs_nlam].
    inverts H; try solve[forwards*: abs_nlam].
    inverts H1.
    inverts H; try solve[forwards*: abs_nlam].
  -
    inverts Typ. inverts H4.
    inverts H6; try solve[inverts H10].
    inverts H10; try solve[forwards*: abs_nlam].
    inverts H; try solve[forwards*: abs_nlam].
    inverts H1.
    inverts H; try solve[forwards*: abs_nlam].
Qed.




Theorem typing_elaborate_completeness_chk: forall l b tt e t t' A ,
  ttyping nil e (Chk2 l b tt) A t ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ ttyping nil e' (Chk2 l b tt) A t''  /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv Typ Red. 
  eapply typing_elaborate_completeness_gen1; eauto.
Qed.
  


Theorem typing_elaborate_completeness_dir: forall dir e t t' A ,
  ttyping nil e dir A t ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ ttyping nil e' dir A t''  /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv Typ Red. 
  destruct dir.
  -
   forwards*: ttyping_chk Typ. 
   inverts H. inverts H0. inverts* H. inverts H0.
   forwards*: typing_elaborate_completeness_chk Red.
   inverts H0.
   *
   lets(vv1&vv2&nn1&rred1&rred2&ttyp1&sz2): H1.
   forwards*: ttyping_regular_1 H.
   destruct(exists_decidable e).
   inverts H2. 
   forwards*: value_valueb H. forwards*: bstep_not_value Red.
   forwards*: steps_nlam rred2.
   inverts* ttyp1; try solve[exfalso; apply H3; eauto].
   forwards*: ttyping_typing Typ; simpl in *.
   forwards*: preservation_multi_step rred2.
   forwards*: typing_ttyping H9 H5.
   subst*.
   left. exists*.
   *
   lets(ll1&llb& rred1& rred2): H1.
   right. exists*.
  -
  forwards*: typing_elaborate_completeness_chk Red.
Qed.



Definition Deterministic_blame_Calculus := forall t r1 r2,
  bstep t r1 ->
  bstep t r2 ->
  r1 = r2.



Theorem typing_elaborate_completeness1: forall e t t' A n n1 dir,
  Deterministic_blame_Calculus ->
  n < n1 ->
  ttyping nil e dir A t ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ ttyping nil e' dir A t' /\ value e'.
Proof.
  introv dd sz typ red val. gen t t' A e n.
  inductions n1; intros; try solve[omega].
  inverts* red.
  -
  forwards*: valueb_value typ.
  -
  forwards*: typing_elaborate_completeness_dir H0.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&typ1&ssz): H1.
  inverts H2.
  *
  inverts* rred1.
  forwards*: valueb_value typ1.
  forwards*: bstep_not_value H2.
  *
  destruct nn2.
  ++
  inverts* rred1.
  assert(bbsteps ee2 (t_term t') (1+n)).
  eapply bbstep_n;eauto.
  forwards*: IHn1 H.
  omega.
  inverts* H2. 
  ++
  assert(nn2 = 0).
  omega.
  rewrite H in *.
  inverts* rred1.
  inverts* H8.
  forwards* h1: dd H3 H7.
  inverts* h1.
  forwards*: IHn1 H5.
  omega.
  inverts* H2. 
  +
  inverts* H1.
  inverts* H.
  inverts* H1.
  inverts* H2.
  forwards*: bstep_not_value H.
  forwards*: dd H H4.
  inverts* H1.
Qed.


Theorem typing_elaborate_completeness_all1: forall e t t' A n dir,
  Deterministic_blame_Calculus ->
  ttyping nil e dir A t ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ ttyping nil e' dir A t' /\ value e'.
Proof.
  introv dd typ red val.
  eapply typing_elaborate_completeness1;eauto.
Qed.




(** annother *)

Lemma btyping_typing: forall G e t A,
 btyping G t A e ->
 Typing G e Inf A.
Proof.
  introv typ.
  inductions typ;eauto.
  -
  eapply Typ_anno;eauto.
  pick fresh x and apply Typ_abs.
  forwards*: H0 x.
  inverts* H1.
  -
  inverts* IHtyp2; try solve[inverts* typ2].
  -
  destruct(lambda_decidable e); eauto.
  forwards* ha: nlam_exist H0.
  inverts* ha;inverts* typ. 
Qed.



Definition typing_typing_aux G dir e A  := 
   match dir with 
    | Chk3 l b => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma typing_typing: forall G dir e  A t,
 typing G e dir A t ->
 typing_typing_aux G dir e A.
Proof.
  introv typ.
  inductions typ; unfold typing_typing_aux in *; intros; eauto.
  (* eapply Typ_app; eauto.
  inverts* IHtyp2.
  eapply Typ_app; eauto.
  inverts* IHtyp2. *)
Qed.


Lemma typing_typing1: forall G e t A B,
 typing G e Inf3 A t ->
 Typing G e Inf B ->
 A = B.
Proof.
  introv typ1 typ2. gen B.
  inductions typ1;intros; 
  try solve[inductions typ2; eauto].
  -
    inverts* typ2.
    forwards*: binds_unique H0 H4.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    inverts* H. inverts* H3.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H2.
    inverts* H0.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    subst. inverts* H3.
Qed.




Lemma value_valueb2: forall e t A,
 btyping nil t A e -> value e ->
 valueb t.
Proof.
  introv typ val. gen A t.
  inductions val; intros;
  try solve[inverts* typ].
  -
    forwards*: btyping_regular_1 typ.
    inverts typ; eauto.
    inverts* H9.
    forwards* h1: btyping_typing H6.
    forwards* h2: principle_inf h1.
    rewrite h2 in *.
    congruence. 
  -
    inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H5.
    forwards* h2: principle_inf h1.
    rewrite h2 in *; eauto.
Qed.


Lemma valueb_value2: forall e t A,
 btyping nil t A e -> valueb t ->
 value e.
Proof.
  introv typ val. gen A e.
  inductions val; intros;
  try solve[inverts* typ].
  - 
    forwards* h1: btyping_regular_3 typ. inverts* typ.
    inverts* h1.
  -
     inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H7.
    forwards* h2: principle_inf h1.
  -
     inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H8.
    forwards* h2: principle_inf h1.
    rewrite <- h2 in *; eauto.
Qed.





Lemma lc_lcb: forall E e t dir A,
 typing E e dir A t ->
 lc_exp e ->
 lc_term t.
Proof.
  introv typ H. 
  inductions typ;try solve[inverts* H];eauto. 
  -
    inverts H1. 
    pick fresh x.
    forwards*: H.
  - inverts H1. 
    pick fresh x.
    forwards*: H.
  - inverts H1. 
    pick fresh x.
    forwards*: H.
  -
    inverts* H0.
Qed.



Lemma value_valueb1: forall e t A,
 typing nil e Inf3 A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ. 
    pick fresh x.
    forwards*: H2.
    forwards*: lc_lcb H. 
  - inverts typ.
    forwards*: value_lc H.
    forwards*: lc_lcb H1.  
    inverts* H8. 
    forwards*: IHvalue.
    forwards*: principle_if H5.
    rewrite H4 in H0. inverts H0.
    eapply valueb_fanno; eauto.
  - inverts typ.
    forwards*: value_lc H0.
    forwards*: lc_lcb H8.
    inverts* H8.
    inverts* H2.
    forwards*: IHvalue.
    forwards*: principle_if H5.
    rewrite H4 in H.
    apply valueb_dyn; eauto.
Qed.



Lemma Tred_soundness: forall v t v' p b A,
  typing nil (e_anno v p b A) Inf3 A t->
  value v ->
  TypedReduce v p b A (e_exp v') ->
  exists t', t ->* (t_term t') /\ typing nil v' Inf3 A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - inverts Typ.
    inverts H7. exists*.
    forwards*: principle_if H3.
  - inverts Typ.
    forwards*: value_lc val.
  - inverts Typ.
    inverts H5.
    inverts H1.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply typ_lit; eauto.
  - 
    inverts Typ. inverts H6.
    forwards*: value_valueb1 H2.
    inverts H2. inverts H11.
    exists* (trm_cast (trm_abs t_dyn t) q b1 (t_arrow t_dyn t_dyn) t_dyn).
    inverts val. forwards*: principle_if H3. rewrite H1 in *.
    exists((trm_cast t q b1 A t_dyn)).
    splits*. 
  - inverts Typ. inverts H6.
    exists.
    splits*.
    forwards*: principle_if H2.
    rewrite H0 in H.
    inverts* H.
    inverts H3.
    inverts H4.
    rewrite <- TEMP in H.
    rewrite <- TEMP in H1.
    exists. split.
    apply star_one.
    apply bStep_anyd; eauto.
    forwards*: value_valueb1 val.
    simpl.
    apply typ_anno; eauto.
    apply typ_sim; eauto.
    apply typ_anno; eauto.
    apply typ_sim; eauto.
    rewrite <- TEMP in H2. auto.
    rewrite <- TEMP in H1.
    exfalso. apply H1. reflexivity.
  -
    inverts Typ. inverts H. inverts H1.
    inverts H3.
    +
    forwards* lc: typing_regular_3 H7.
    inverts H7; try solve[inverts* H4]. 
    inverts* H4.
    inverts* H14;
    try solve[exfalso; apply H6; eauto];
    try solve[exfalso; apply H2; eauto];
    try solve[inverts* H15].
    inverts lc. inverts H3.
    exists.
    splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; eauto.
    apply star_one.
    rewrite fillb_cast.
    apply do_stepb.
    auto.
    apply bStep_vany; auto.
    forwards*: value_valueb1 val.
    apply typ_anno; eauto.
    apply typ_sim; eauto.
    +
    exfalso; apply H0; eauto.
  -
    inverts Typ. inverts* H5. inverts* H1.
    forwards*: value_lc val.
    inverts H.
    forwards*: lc_lcb H9.
    inverts* H9.
    exists. splits.
    apply star_one.
    apply bStep_vany; eauto.
    forwards*: value_valueb1 val. inverts* H0.
    apply typ_anno; eauto.
     inverts H12.
  - 
    inverts Typ. inverts val.
    inverts H9. inverts H6. inverts H15;
    try solve[forwards*: abs_nlam].
    forwards*: principle_if H6.
    rewrite H2 in H0.
    rewrite H2 in H5.
    inverts H. inverts H8.
    inverts* H9.
    destruct A0; try solve[inverts H0];
    try solve[inverts H5]. inverts H5.
    forwards*: value_valueb1 H7.
    exists. split.
    eapply star_trans.
    apply star_one.
    eapply bStep_dyna;eauto.
    eapply star_one.
    rewrite fillb_cast.
    apply do_stepb.
    auto.
    unfold fillb.
    apply bStep_vany; eauto.
    unfold fillb.
    apply typ_anno; eauto.
  - inverts Typ. inverts val.
    inverts H6.
    inverts H3. inverts H12;
    try solve[forwards*: abs_nlam].
    forwards*: principle_if H3.
    exists. split.
    apply star_one.
    rewrite H0. rewrite H0 in H2.
    apply bStep_vany; eauto.
    forwards*: value_valueb1 H3.
    rewrite H0. auto.
Qed.



Lemma soundness_mul_two: forall e t e' A dir ,
  typing nil e dir A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ typing nil e' dir A t' .
Proof.
  introv Typ Red. gen A t dir.
  inductions Red; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      *
      forwards*: IHRed H8. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H3.
      eapply typ_app; eauto.
      *
      inverts H0.
      forwards*: IHRed H10. inverts H0. inverts H3.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app x t2) l0 b0 A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app2; auto.
      inverts H.
      forwards*: lc_lcb H5. 
      apply bstep_refl.
      eapply typ_sim; eauto.
      forwards*: IHRed H10. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      apply multi_red_app2.
      inverts H.
      forwards*: lc_lcb H5. 
      apply multi_red_cast.
      apply H0.
      eapply typ_sim; eauto.
      *
      forwards*: IHRed H8. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2.
      inverts H.
      forwards*: lc_lcb H3.
      apply multi_red_cast.
      apply H0.
      eapply typ_appd; eauto.
    + 
      inverts Typ. 
      * inverts H.
      forwards*: value_valueb1 H4.
      forwards*: IHRed H9. 
      inverts H0. inverts H1.
      exists. split.
      forwards: multi_red_app H H0.
      apply H1.
      eapply typ_app; eauto.
      *
      inverts H. inverts H0.
      -- 
      forwards*: value_valueb1 H7.
      forwards*: IHRed H12. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      forwards: multi_red_app H H0.
      apply H3.
      eapply typ_sim; eauto.
      --
      forwards*: principle_if H11.
      rewrite H in *.
      inverts* H5.
      *
      inverts H. 
      forwards*: principle_if H8.
      rewrite H in *.
      inverts* H2.
    + inverts Typ. 
      * forwards*: IHRed H8. inverts H0. inverts H1.
        exists. split.
        apply H0.
        apply typ_anno; eauto.
      * inverts H0.
        forwards*: IHRed H10. inverts H0. inverts H3.
        exists. split.
        apply multi_red_cast.
        apply H0.
        apply typ_sim;eauto.
    + inverts Typ.
      *
      inverts H0.
      forwards*: IHRed H5. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H6.
      apply typ_sim;eauto.
      *
      inverts H.
      forwards*: IHRed H2. inverts H. inverts H0.
      exists. split.
      apply multi_red_app2; eauto.
      forwards*: lc_lcb H1.
      eapply typ_appv;eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards*: IHRed H7. inverts H0. inverts H3.
      exists. split.
      apply multi_red_cast.
      apply multi_red_app.
      inverts H.   
      forwards*: value_valueb1 H6.
      apply H0.
      apply typ_sim;eauto.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H4. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app.
      inverts H.   
      forwards*: value_valueb1 H5.
      apply H0.
      forwards*: step_not_nlam Red.
  - 
    inverts* Typ.
    + 
      inverts H1.
      forwards*: value_valueb1 H8.
      forwards*: value_valueb1 H6.
      inverts H6.
      inverts H16; try solve[forwards*: abs_nlam].
      exists. split.
      eapply star_trans.
      apply multi_red_cast.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply typ_sim; eauto.
      apply typ_anno; eauto.
      pick fresh y.
      forwards*: H14.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply typing_c_subst_simpl; auto.
      apply H5. auto.
    +
      forwards*: value_valueb1 H3.
      forwards*: value_valueb1 H5.
      inverts H3.
      inverts H14; try solve[forwards*: abs_nlam].
      exists. split.
      eapply star_trans.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply typ_anno; eauto.
      pick fresh y.
      forwards*: H12.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply typing_c_subst_simpl; auto.
      apply H3. auto.
  - 
    inverts Typ.
    assert (typing nil (e_anno v l b A0) Inf3 A0 t).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H2.
    assert (typing nil (e_anno v l b A1) Inf3 A1 t0).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H5. inverts H6.
    exists. split.
    apply multi_red_cast; eauto.
    apply typ_sim;eauto.
    forwards*: TypedReduce_nlambda2 H0.
  - 
    inverts Typ. 
    * 
    inverts H3. inverts H8. inverts H16;
    try solve[inverts H0]. 
    forwards*: value_valueb1 H7.
    forwards*: value_valueb1 H10.
    forwards*: principle_if H7.
    rewrite H8 in *. subst.
    inverts H12. 
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply typ_sim; eauto.
    apply typ_anno; eauto. 
    * 
    inverts H5. inverts H14; try solve[inverts H0]. 
    forwards*: value_valueb1 H7.
    forwards*: value_valueb1 H5.
    forwards*: principle_if H5.
    rewrite H6 in *. subst.
    inverts H9. 
    exists. split.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply typ_anno; eauto.
  -
    inverts Typ.
    +
    forwards*: principle_if H11. rewrite H3 in H1. inverts H1.
    assert(typing nil (e_anno v2 l b A) Inf3 A t2).
    apply typ_anno; auto. 
    forwards*: Tred_soundness H2.
    destruct H4. destruct H4.
    forwards*:  TypedReduce_walue2 H2.
    forwards*: value_valueb1 H11.
    exists. splits.
    apply multi_red_app; eauto.
    eapply typ_appv; eauto.
    +
    inverts H3.
    forwards*: principle_if H13. rewrite H3 in H1. inverts H1.
    forwards*: value_valueb1 H13.
    assert(typing nil (e_anno v2 l b A) Inf3 A t2).
    apply typ_anno; auto. 
    forwards*: Tred_soundness H2.
    destruct H7. destruct H7.
    forwards*:  TypedReduce_walue2 H2.
    exists. splits.
    apply multi_red_cast.
    apply multi_red_app; eauto.
    eapply typ_sim; eauto.
    forwards*: principle_if H13. rewrite H3 in H1. inverts H1.
    +
    forwards*: principle_if H11. rewrite H3 in H1. inverts H1.
  -
    inverts Typ; try solve[inverts H9].
    +
    inverts H1; try solve[inverts H11].
    forwards* h1: value_valueb1 H11.
    exists. splits.
    eapply bstep_refl.
    eapply typ_sim; eauto.
    +
    forwards* h1: value_valueb1 H9.
    exists. splits.
    eapply bstep_refl.
    eapply typ_app; eauto.
  -
    inverts Typ.
    +
    inverts H. inverts H4. inverts H6.
    exists. splits.
    apply multi_red_cast.
    apply star_one; eauto.
    eapply typ_sim; eauto.
    +
    inverts H1. inverts H3.
    exists. splits.
    apply star_one; eauto.
    eapply typ_addl; eauto.
  -
    inverts Typ.
    +
    inverts H. inverts H4. inverts H6.
    exists. splits.
    apply multi_red_cast.
    apply star_one; eauto.
    eapply typ_sim; eauto.
    +
    inverts H1. inverts H3.
    exists. splits.
    apply star_one; eauto.
    eapply typ_lit; eauto.
  -
    inverts* Typ.
    + 
    inverts* H1. 
    inverts* H6; try solve[exfalso; apply H5; eauto].
    forwards*: value_valueb1 H8.
    forwards*: lc_lcb H.
    exists. split.
    eapply star_trans.
    rewrite fillb_cast.
    apply star_one.
    apply do_stepb;auto. 
    unfold fillb.
    apply bstep_refl. 
    eapply typ_sim; eauto.
    apply typ_anno; eauto.
    pick fresh y.
    forwards*: H10.
    rewrite (subst_exp_intro y); auto.
    rewrite (subst_term_intro y); auto.
    eapply typing_c_subst_simpl; auto.
    apply H5. auto.
  +
    inverts H3. 
    forwards*: value_valueb1 H5.
    forwards*: lc_lcb H.
    exists. split.
    eapply star_trans.
    apply star_one.
    apply bStep_beta;auto.
    apply bstep_refl. 
    apply typ_anno; eauto.
    pick fresh y.
    forwards*: H7.
    rewrite (subst_exp_intro y); auto.
    rewrite (subst_term_intro y); auto.
    eapply typing_c_subst_simpl; auto.
    apply H3. auto.
Qed.

Theorem soundness: forall e t v1 A,
  typing nil e Inf3 A t->
  e ->** (e_exp v1) ->
  value v1 ->
  exists t', t ->* (t_term t') /\ valueb t' /\ typing nil v1 Inf3 A t' .
Proof.
  introv typ red val. gen A t.
  inductions red;intros.
  -
  forwards*: value_valueb1 val.
  -
  forwards*: soundness_mul_two H.
  inverts H0. inverts H1.
  forwards*: IHred H2.
  inverts* H1. 
Qed.



Lemma typedReduce_completeness: forall v t B A t' l b ,
  btyping nil t B v ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_term t') ->
  (exists  n t2 v',  bbsteps t' (t_term t2) n /\ TypedReduce v l b A (e_exp v') /\
  btyping nil t2 A v' /\ 0<=n <= 1) \/ (bstep t' (t_blame l b) /\ (TypedReduce v l b A (e_blame l b))).
Proof.
  introv typ val red.
  forwards* h1: valueb_value2 val.
  inductions red; try solve[inverts* typ].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts* typ; inverts h1.
    left. 
    exists.
    splits*.
  -
     inverts* typ; inverts h1.
     left. 
    exists.
    splits*.
  -
    inverts* H2. 
    forwards* h2:btyping_typing typ.
    forwards*: principle_inf h2.
    left.
    exists. splits. 
    apply bbstep_refl.
    eapply TReduce_anyd.
    rewrite H2.
    unfold FLike.
    splits*.
    eapply btyp_cast; eauto.
    omega.
    omega.
  -
    inverts* H2. 
    inverts val;inverts* typ.
    inverts H2; try solve[inverts H13;inverts* H3].
    +
    right. rewrite fillb_cast.
    rewrite fillb_cast.
    splits.
    apply blame_stepb;eauto.
    simpl.
    eapply bStep_vanyp;eauto.
    inverts* H13.
    unfold not;intros nt;inverts* nt.
    inverts* H13.
    eapply TReduce_blame;simpl;eauto.
    unfold not;intros nt;inverts* nt.
    +
    inverts h1.
    inverts* H13. inverts H8.
    left.
    exists. splits.
    eapply sstar_one.
    rewrite fillb_cast.
    apply do_stepb;eauto.
    eapply TReduce_dyna; simpl;eauto.
    unfold FLike; splits*.
    eapply btyp_cast; eauto.
    omega. omega.
    +
    inverts h1.
    inverts* H13. inverts H3.
    left.
    exists. splits.
    eapply sstar_one.
    rewrite fillb_cast.
    apply do_stepb;eauto.
    eapply TReduce_dyna; simpl;eauto.
    unfold FLike; splits*.
    eapply btyp_cast; eauto.
    omega.
    omega.
  -
    inverts* typ. 
    forwards* h2:btyping_typing H8. 
    forwards*: valueb_value2 H8.
    forwards* h3: principle_inf h2.
    rewrite <- h3.
    destruct(lambda_decidable e).
    left. exists. splits*.
    rewrite h3; auto.
    forwards* h4: nlam_exist.
    inverts h4.
    inverts* H8.
Qed.




Theorem typing_elaborate_completeness_gen: forall e t t' A n,
 size_exp e + size_term t < n ->
  btyping nil t A e ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ btyping nil t'' A e' /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t t' A.
  induction n; intros; try omega.
  lets Red': Red.
  inductions Red; intros.
  - clear IHRed.
     destruct E; unfold fillb in *; simpl in *.
    +
    forwards h1: btyping_typing Typ.
    forwards* lc: Typing_regular_1 h1.
    inverts Typ; simpl in *.
    inverts h1; simpl in *.
    forwards* h2: IHn Red H3. simpl in *; omega.
    inverts H.
    inverts* h2.
    *
    lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H.
    inverts lc.
    left.
    exists. splits.
    eapply mmulti_red_app2.
    auto.
    apply rred2.
    apply multi_rred_appv2.
    auto. apply rred1.
    eapply btyp_app; eauto.
    omega.
    omega.
    *
    lets(ll1&bb1&rred1&rred2):H.
    right. exists.
    splits.
    rewrite fillb_appl.
    apply blame_stepb;eauto.
    eapply multi_bblame_appv2;eauto.
    inverts* lc.
    +
    inverts Typ. inverts H.
    forwards* h1: valueb_value2 H3.
    forwards* h2: IHn Red H6. simpl in *; omega.
    inverts h2.
    *
    lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H.
    left.
    exists. splits.
    eapply mmulti_red_app.
    auto.
    apply rred2.
    apply multi_rred_appv.
    auto. apply rred1.
    eapply btyp_app; eauto.
    omega.
    omega.
    *
    lets(ll1&bb1&rred1&rred2):H.
    right. exists.
    splits.
    rewrite fillb_appr.
    apply blame_stepb;eauto.
    eapply multi_bblame_appv;eauto.
    +
     forwards* lc: btyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts lc.
     forwards* h1: IHn Red H8. simpl in *; omega.
     inverts h1.
     lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H0.
     left.
     exists. splits.
     apply mmulti_red_cast.
     apply rred2. 
     apply multi_rred_anno.
     apply rred1.
     eapply btyp_cast; eauto.
     omega.
     omega.
     lets(ll1&bb1&rred1&rred2):H0.
     right. exists.
     splits.
     rewrite fillb_cast.
     apply blame_stepb;eauto.
     eapply multi_bblame_anno;eauto.
  -
    forwards* lc: btyping_regular_3 Typ.
    inverts Typ. inverts H4.
    forwards* h1: valueb_value2 H7.
    inverts lc. inverts H3.
    forwards* h2: value_group h1.
    inverts h2.    
    pick fresh x.
    forwards* h3: H9 x.
    left.
    exists. splits.
    eapply bbstep_refl.
    eapply stars_one.
    eapply Step_beta.
    auto.
    auto.
    rewrite (subst_term_intro x);eauto.
    rewrite (subst_exp_intro x);eauto.
    assert((e_anno [x ~> e2] (e ^^ e_var_f x) l0 b A0) = ([x ~> e2](e_anno (e ^^ e_var_f x) l0 b A0))).
    simpl; reflexivity.
    rewrite H3 in *.
    eapply btyping_c_subst_simpl;eauto.
    omega. omega.
    inverts H1; inverts H7.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H7.
    forwards*: typedReduce_completeness H7 Red'.
    inverts H.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H0.
    inverts* H7.
    inverts* rred1.
    left.
    exists. splits.
    eapply bbstep_refl.
    apply stars_one.
    apply Step_annov; eauto.
    unfold not;intros nt;inverts* nt.
    auto.
    omega. omega.
    ++
    lets(rred1&rred2):H0.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ. inverts H4.
    inverts H. 
    forwards* h1: valueb_value2 H12.
    forwards* h3: valueb_value2 H7.    
     forwards* h2: value_group h3. 
    inverts h2.
    +
    forwards* h4: value_group h1.
    inverts h4. 
    forwards*: btyping_typing H12.
    forwards*: principle_inf H3.
    inverts H13.
    left.
    exists. splits.
    eapply bbstep_refl.
    eapply stars_one.
    eapply Step_abeta;eauto.
    eapply btyp_cast;eauto.
    omega. omega.
    inverts H1; try solve[inverts H12]. 
    +
    inverts* H; try solve[inverts H7].
  -
    inverts Typ.
    forwards* h1: valueb_value2 H8.
    forwards*: typedReduce_completeness H8 Red'.
    inverts H0.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H1.
    forwards*: value_decidable (e_anno e0 p b t_dyn).
    inverts H0.
    +
    forwards*: value_tred_keep2 rred1. inverts H0.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    omega.
    omega.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    omega.
    omega.
    ++
    lets(rred1&rred2):H1.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H11.
    forwards*: typedReduce_completeness H11 Red'.
    inverts H3.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H4.
    forwards* h2: value_decidable (e_anno e0 p b t_dyn).
    inverts h2.
    +
    forwards* h3: value_tred_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    omega.
    omega.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    omega.
    omega.
    ++
    inverts* H2.
    lets(rred1&rred2):H4.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H11.
    forwards*: typedReduce_completeness H11 Red'.
    inverts H3.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H4.
    forwards* h2: value_decidable (e_anno e0 p b A0).
    inverts h2.
    +
    forwards* h3: value_tred_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    omega.
    omega.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    omega.
    omega.
    ++
    inverts* H2.
    lets(rred1&rred2):H4.
    right. exists.
    splits*.
    inverts h1;inverts H11.
    eapply step_b;eauto.
    eapply Step_annov;eauto.
    unfold not;intros nt;inverts* nt. inverts H15.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H9.
    forwards*: typedReduce_completeness H9 Red'.
    inverts H1.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H2.
    forwards* h2: value_decidable (e_anno e0 p b2 A0).
    inverts h2.
    +
    forwards* h3: value_tred_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    omega.
    omega.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    omega.
    omega.
    ++
    lets(rred1&rred2):H2.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ. inverts H2. inverts* H5.
    left. exists. splits.
    eapply bbstep_refl.
    eapply stars_one;eauto.
    eapply btyp_addl;eauto.
    omega. omega.
  -
    inverts Typ. inverts H2. inverts* H5.
    left. exists. splits.
    eapply bbstep_refl.
    eapply stars_one;eauto.
    eapply btyp_lit;eauto.
    omega. omega.
Qed.




Theorem typing_elaborate_completeness: forall e t t' A n n1,
  Deterministic_blame_Calculus ->
  n < n1 ->
  btyping nil t A e ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ btyping nil t' A e' /\ value e'.
Proof.
  introv dd sz typ red val. gen t t' A e n.
  inductions n1; intros; try solve[omega].
  inverts* red.
  -
  forwards*: valueb_value2 typ.
  -
  forwards*: typing_elaborate_completeness_gen H0.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&typ1&ssz): H1.
  inverts H2.
  *
  inverts* rred1.
  forwards*: valueb_value2 typ1.
  forwards*: bstep_not_value H2.
  *
  destruct nn2.
  ++
  inverts* rred1.
  assert(bbsteps ee2 (t_term t') (1+n)).
  eapply bbstep_n;eauto.
  forwards*: IHn1 H.
  omega.
  inverts* H2. 
  ++
  assert(nn2 = 0).
  omega.
  rewrite H in *.
  inverts* rred1.
  inverts* H8.
  forwards* h1: dd H3 H7.
  inverts* h1.
  forwards*: IHn1 H5.
  omega.
  inverts* H2. 
  +
  inverts* H1.
  inverts* H.
  inverts* H1.
  inverts* H2.
  forwards*: bstep_not_value H.
  forwards*: dd H H4.
  inverts* H1.
Qed.


Theorem typing_elaborate_completeness_all: forall e t t' A n,
  Deterministic_blame_Calculus ->
  btyping nil t A e ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ btyping nil t' A e' /\ value e'.
Proof.
  introv dd typ red val.
  eapply typing_elaborate_completeness;eauto.
Qed.



(* sound2 *)


Lemma tTypedReduce_soundness2: forall v t A v' l b ,
  ttyping nil (e_anno v l b A) Inf2 A t ->
  value v ->
  TypedReduce v l b A (e_exp v') ->
  exists t', bsteps t (t_term t')  /\ ttyping nil v' Inf2 A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - inverts Typ.
    inverts H4; try solve[forwards*: abs_nlam].
    +
    forwards*: principle_if2 H7.
    +
    inverts* H7.
  - inverts Typ.
    +
    inverts H3; try solve[forwards*: abs_nlam].
    forwards*: principle_if2 H6.
    +
    inverts* H6.
  - inverts Typ.
    inverts H2.
    inverts H5.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply ttyp_lit; eauto.
  - 
    inverts Typ. inverts H3.
    forwards*: value_valueb H6.
    inverts H6. 
    +
    inverts* H0.
    exists. splits.
    apply star_one.
    apply bStep_dd; eauto. 
    eapply ttyp_anno;eauto.
    +
    exists. splits.
    apply star_one.
    apply bStep_dd; eauto. 
    eapply ttyp_anno2;eauto.
  - inverts Typ. inverts H3; try solve[forwards*: abs_nlam].
    +
    forwards*: principle_if2 H6.
    rewrite H0 in *.
    inverts* H.
    inverts H2.
    forwards*: value_valueb H6.
    exists. split.
    apply star_one.
    apply bStep_anyd; eauto.
    apply ttyp_anno; eauto.
    +
    forwards*: value_valueb H6.
    inverts* H6; try solve[inverts H11].
    exists. splits*.
    exists. splits*.
  -
    inverts Typ. inverts H7. inverts* H6;
    try solve[forwards*: abs_nlam].
    forwards* lc: ttyping_regular_3 H10.
    inverts* H10; try solve[inverts H14].
    +
    inverts H. inverts H1.
    inverts lc.
    exists. splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; auto.
    apply star_one.
    rewrite fillb_cast.
    eapply do_stepb.
    auto.
    eapply bStep_vany;eauto.
    apply ttyp_anno; eauto.
    eapply ttyp_sim; eauto.
    apply BA_AB; auto.
    +
    inverts H. inverts H1.
    inverts lc.
    exists. splits.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; auto.
    apply star_one.
    rewrite fillb_cast.
    eapply do_stepb.
    auto.
    eapply bStep_vany;eauto.
    apply ttyp_anno; eauto.
    eapply ttyp_sim; eauto.
    apply BA_AB; auto.
  -
    inverts Typ. inverts* H2. inverts* H5;
    try solve[forwards*: abs_nlam].
    inverts* H8; try solve[inverts H12].
    +
    exists. splits.
    apply star_one.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H.
    eapply ttyp_anno2; eauto.
    +
    exists. splits.
    apply star_one.
    apply bStep_vany; eauto.
    forwards*: value_valueb val. inverts* H.
    eapply ttyp_anno2; eauto.
  - 
    inverts Typ. inverts val.
    inverts H9. inverts H12; try solve[forwards: abs_nlam H1;inverts H2].
    inverts H14;try solve[forwards: abs_nlam H1;inverts H2] .
    forwards: principle_if2 H11. auto.
    rewrite H2 in *.
    inverts H. inverts H6.
    inverts H8; try solve[forwards: abs_nlam H1;inverts H2];
    try solve[exfalso; apply H3; auto].
    inverts H4; try solve[inverts* H0].
    rewrite <- TEMP in H0. inverts H0.
    forwards: value_valueb H11.
    auto.
    exists. split.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna.
    auto. auto. auto. auto.
    apply star_one.
    rewrite fillb_cast.
    apply do_stepb.
    auto.
    apply bStep_vany.
    auto. auto.
    apply ttyp_anno.
    eapply ttyp_sim.
    rewrite <- TEMP in *.
    auto. auto. auto. auto.
  - inverts Typ. inverts val.
    inverts H3.
    inverts H9; try solve[forwards*: abs_nlam]. 
    inverts H11; try solve[forwards*: abs_nlam].
    forwards*: principle_if2 H8.
    rewrite H0 in *.
    forwards: value_valueb H8.
    auto.
    exists. split.
    apply star_one.
    apply bStep_vany; eauto.
    auto.
Qed.
  



Theorem typing_elaborate_soundness_chk2: forall l b B e t e' A,
  ttyping nil e (Chk2 l b B) A t ->
  step e (e_exp e') ->
  exists t', bsteps t (t_term t') /\ ttyping nil e' (Chk2 l b B) A t' .
Proof.
  introv Typ Red. gen l b B t A.
  inductions Red; intros.
  - 
     destruct E; unfold fill in *; simpl in *.
    +
    forwards* lc: ttyping_regular_3 Typ.
    inverts Typ; simpl in *.
    inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
    *
    forwards*: ttyping_chk H10.
    lets(ll1&bb1&tb1&tb2&ttyp1):H0.
    forwards*: IHRed ttyp1. 
    lets(vv1&rred1&ttyp2): H1.
    forwards*: step_not_nlam Red.
    inverts ttyp2;
    try solve[inverts H2].
    forwards*: ttyping_typing H10; simpl in *.
    forwards*: preservation Red.
    forwards*: typing_ttyping H12 H4. 
    subst*.
    inverts lc.
    exists. splits.
    apply multi_red_app2.
    auto. apply rred1.
    eapply ttyp_sim; eauto.
    *
    forwards*: ttyping_chk H10.
    lets(ll1&bb1&tb1&tb2&ttyp1):H0.
    forwards*: IHRed ttyp1. 
    lets(vv1&rred1&ttyp2): H1.
    forwards*: step_not_nlam Red.
    inverts ttyp2;
    try solve[inverts H2].
    forwards*: ttyping_typing H10; simpl in *.
    forwards*: preservation Red.
    forwards*: typing_ttyping H12 H4. 
    subst*.
    inverts lc.
    exists. splits.
    apply multi_red_app2.
    auto. 
    apply multi_red_cast.
    apply rred1.
    eapply ttyp_sim; eauto.
    +
     forwards* lc: ttyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
     *
      inverts lc. inverts H.
      forwards*: value_valueb H10.
      forwards* lc2: ttyping_regular_1 H11.
      inverts lc2.
      inverts H11; try solve[
        forwards*: step_not_value Red
      ].
      forwards*: IHRed H16. 
      lets(vv1&rred1&ttyp1): H0.
      exists. splits.
      apply multi_red_app.
      auto.
      apply multi_red_cast. 
      apply rred1.
      apply ttyp_sim; eauto.
      eapply ttyp_app; eauto.
      forwards*: step_not_nlam Red.
    *
      inverts lc. inverts H.
      forwards*:principle_if2 H10.
      rewrite H in *. inverts H4.
    +
    forwards* lc: ttyping_regular_1 Typ. inverts lc.
    inverts Typ.
    forwards* lc2: ttyping_regular_3 H6.
    inverts H6;
    try solve[
    forwards*: step_not_value Red
    ].
    forwards*: IHRed H11. 
    lets(vv1&rred1&ttyp1): H0.
    exists. splits.
    apply multi_red_cast.
    apply rred1.
    forwards*: step_not_nlam Red.
    +
    inverts H.
    forwards* lc: ttyping_regular_3 Typ.
    inverts Typ; simpl in *.
    inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
    *
    forwards*: ttyping_chk H2.
    lets(ll1&bb1&tb1&tb2&ttyp1):H.
    forwards*: IHRed ttyp1. 
    lets(vv1&rred1&ttyp2): H0.
    forwards*: step_not_nlam Red.
    inverts ttyp2;
    try solve[inverts H3].
    forwards*: ttyping_typing H13; simpl in *.
    forwards*: ttyping_typing H2; simpl in *.
    forwards*: preservation Red.
    forwards*: typing_ttyping H10. 
    subst*.
    inverts lc.
    exists. splits.
    apply multi_red_app2.
    auto. apply rred1.
    eapply ttyp_sim; eauto.
    +
    inverts H.
    forwards* lc: ttyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts H5; try solve[inverts H0;inverts* H6]; simpl in *.
     *
      inverts lc.
      forwards*: value_valueb H2.
      forwards* lc2: ttyping_regular_1 H4.
      forwards*: ttyping_chk H4.
      lets(ll1&bb1&tb1&tb2&ttyp1):H0.
      forwards*: IHRed ttyp1. 
      lets(vv2&rred2&ttyp2): H7.
      forwards*: step_not_nlam Red.
      inverts ttyp2; try solve[forwards*: abs_nlam].
      forwards*: ttyping_typing H4; simpl in *.
      forwards*: preservation Red.
      forwards*: typing_ttyping H16.
      subst*. 
      exists. splits.
      apply multi_red_app.
      auto.
      apply rred2.
      apply ttyp_sim; eauto.
  -
    inverts Typ. inverts H6. 
    inverts* H3; try solve[forwards*: abs_nlam].
    forwards*: value_valueb H5.
    forwards*: value_valueb H14.
    inverts* H14; try solve[inverts H17].
    +
    inverts H2.
    exists. splits.
    apply star_one.
    apply bStep_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    rewrite (subst_term_intro y); eauto.
    forwards*: H16 y.
    simpl in *.
    eapply ttyp_sim; eauto.
    eapply ttyp_anno; eauto.
    eapply ttyping_c_subst_simpl; eauto.
    forwards*: nlam_open3 y H17.
    forwards*: nlam_open2 y H7 H3.
    +
    forwards* h1: nlam_exist H17. inverts h1.
    pick fresh y.
    forwards* h2: not_nlam_open v y H17.
    inverts H2.
    exists. splits.
    apply star_one.
    apply bStep_beta; eauto.
    unfold open_term_wrt_term; simpl.
    assert((open_term_wrt_term_rec 0 t2 t) = (open_term_wrt_term t t2)); eauto.
    rewrite H2.
    rewrite (subst_exp_intro y); eauto.
    rewrite (subst_term_intro y); eauto.
    forwards*: H16 y.
    unfold open_exp_wrt_exp in *.
    simpl in *.
    forwards*:ttyping_c_subst_simpl H3 H5.
  -
    inverts Typ. 
    assert(A = B). inverts* H7. subst*.
    forwards*: tTypedReduce_soundness2 H7.
    inverts H2. inverts* H3.
    exists. splits.
    apply H2.
    forwards*: TypedReduce_walue3 H0.
  -
    inverts Typ. inverts H8.
    forwards*: value_valueb H5.
    forwards*: value_valueb H7.
    inverts H5; try solve[inverts H0].
    inverts H3. 
    inverts H18; try solve[forwards*: abs_nlam].
    forwards* h1: principle_if2 H14.
    rewrite h1 in *. inverts H2.
    inverts* H17.
    exists. splits.
    apply star_one.
    apply bStep_abeta;eauto.
    eapply ttyp_sim;eauto.
    eapply ttyp_anno; eauto.
  -
    inverts Typ. inverts H8.
    +
    forwards*: value_valueb H13.
    forwards*: principle_if2 H13.
    rewrite H4 in *. inverts H1.
    forwards*: tTypedReduce_soundness2 H14.
    forwards*: TypedReduce_walue3 H2.
    inverts H1. inverts* H6.
    exists. splits.
    apply multi_red_app.
    auto. apply H1.
    eapply ttyp_sim; eauto.
    +
    forwards*: principle_if2 H13.
    rewrite H3 in *. inverts H1.
  -
    inverts Typ. inverts* H6. 
    + inverts* H11.
    +
    exists. splits.
    apply bstep_refl.
    eapply ttyp_sim; eauto.
  -
    inverts Typ. inverts H4.
    inverts H1.
  -
    inverts Typ. inverts H4.
    inverts H1.
  -
    inverts Typ. inverts H6. 
    forwards*: value_valueb H3.
    forwards*: value_valueb H5.
    inverts* H3; try solve[forwards*: abs_nlam].
    +
    inverts H1.
    exists. splits.
    apply star_one.
    apply bStep_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    rewrite (subst_term_intro y); eauto.
    forwards*: H12 y.
    simpl in *.
    eapply ttyp_sim; eauto.
    eapply ttyp_anno; eauto.
    eapply ttyping_c_subst_simpl; eauto.
    forwards*: nlam_open3 y H13.
    forwards*: nlam_open2 y H7 H3.
    +
    forwards* h1: nlam_exist H13. inverts h1.
    pick fresh y.
    forwards*: not_nlam_open v y H13.
    inverts H1.
    exists. splits.
    apply star_one.
    apply bStep_beta; eauto.
    unfold open_term_wrt_term; simpl.
    assert((open_term_wrt_term_rec 0 t2 t) = (open_term_wrt_term t t2)); eauto.
    rewrite H1.
    rewrite (subst_exp_intro y); eauto.
    rewrite (subst_term_intro y); eauto.
    forwards*: H12 y.
    unfold open_exp_wrt_exp in *.
    simpl in *.
    forwards*:ttyping_c_subst_simpl H4 H5.
Qed.




Theorem typing_elaborate_soundness_dir2: forall dir e t e' A ,
  ttyping nil e dir A t ->
  step e (e_exp e') ->
  exists t', bsteps t (t_term t') /\ ttyping nil e' dir A t' .
Proof.
  introv Typ Red. 
  destruct dir.
  -
   forwards*: ttyping_chk Typ. 
   inverts H. inverts H0. inverts* H. inverts H0.
   forwards*: typing_elaborate_soundness_chk2 Red.
   inverts H0. inverts H1.
   forwards*: step_nlam Red.
   inverts* H2; try solve[exfalso; apply H1; eauto].
   forwards*: ttyping_typing Typ; simpl in *.
   forwards*: preservation Red.
   forwards*: typing_ttyping H8 H3.
   subst*.
  -
  forwards*: typing_elaborate_soundness_chk2 Red.
Qed.



Theorem typing_elaborate_soundness2: forall dir e t e' A ,
  ttyping nil e dir A t ->
  steps e (e_exp e') ->
  value e' ->
  exists t', bsteps t (t_term t') /\ valueb t' /\ ttyping nil e' dir A t' .
Proof.
  introv Typ Red val. gen dir A t.
  inductions Red; intros;eauto.
  -
   forwards*: value_valueb Typ.
  -
   forwards*: typing_elaborate_soundness_dir2 H.
   inverts* H0. inverts H1.
   forwards*: IHRed H2.
   lets(vv&rred&vval&ell): H1.
   exists. splits.
   eapply star_trans.
   apply H0. apply rred.
   auto. auto.
Qed.