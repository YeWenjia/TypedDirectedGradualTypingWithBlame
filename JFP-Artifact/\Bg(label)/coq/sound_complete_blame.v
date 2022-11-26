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
        ttyping
        soundness_completeness.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).



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

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma principle_if: forall v A t,
 value v -> typing nil v Inf3 A t -> principal_type v = A.
Proof.
  introv H typ.
  inductions H; inverts* typ; eauto.
Qed.



Lemma fillb_cast: forall v p b A B,
  (trm_cast v p b A B) = (fillb (castCtxb p b A B)  v).
Proof.
  introv.
  eauto.
Qed.



Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma Tred_blame_soundness: forall v t p b A,
  typing nil (e_anno v p b A) Inf3 A t->
  value v ->
  TypedReduce v p b A (e_blame p b) ->
  t ->* (t_blame p b) .
Proof.
  introv Typ val Red.
  inductions Red; intros. 
  inverts Typ. inverts H7.
  inverts H3.
  forwards* h1: typing_regular_3 H11. 
  inverts H11; simpl in *. 
  -
    destruct A; try solve[exfalso; apply H;eauto].
    inverts val.
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros n;inverts n.
    inverts* h1.
  -
    inverts val; simpl in *.
    forwards*: value_valueb1 H3.
    forwards* h2: principle_if H3.
    rewrite h2 in *.
    inverts H4.
    +
    rewrite <- TEMP in *.
    destruct A; try solve[exfalso; apply H; auto].
    destruct(eq_type A2). destruct(eq_type A1).
    subst.
    *
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros n;inverts n.
    *
    eapply bstep_nb.
    eapply bStep_dyna; auto.
    unfold not; intros n;inverts n.
    unfold not; intros n;inverts* n.
    rewrite fillb_cast.
    eapply bstep_b.
    apply blame_stepb; auto.
    eapply bStep_vanyp; auto.
    unfold not; intros n;inverts* n.
    *
    eapply bstep_nb.
    eapply bStep_dyna; auto.
    unfold not; intros n;inverts n.
    unfold not; intros n;inverts* n.
    rewrite fillb_cast.
    eapply bstep_b.
    apply blame_stepb; auto.
    eapply bStep_vanyp; auto.
    unfold not; intros n;inverts* n.
    +
    rewrite <- TEMP in *.
    destruct A; try solve[exfalso; apply H; auto].
    eapply bstep_b.
    apply bStep_vanyp; eauto.
    unfold not; intros n;inverts n.
Qed.



Lemma Soundness_blame_two: forall e t dir p b A,
  typing nil e dir A t->
  step e (e_blame p b) ->
  t ->* (t_blame p b).
Proof.
  introv Typ J. gen A dir t.
  inductions J; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      * forwards*: IHJ H8. 
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H9.
      * 
      inverts H0.
      ++
      forwards*: IHJ H10.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H11.
      ++
      forwards*: typing_regular_3 H11.
      forwards*: IHJ H10.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto.
      apply multi_blame_cast; eauto.     
      *
      forwards*: typing_regular_3 H9.
      forwards*: IHJ H8.
      apply multi_blame_app2; eauto.
      apply multi_blame_cast; eauto.
    + 
      inverts Typ.
      *
      forwards*: typing_regular_1 H9. 
      forwards*: IHJ H9. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H8.
      *
      inverts H0.
      -- 
      forwards*: typing_regular_1 H10.
      forwards*: IHJ H11. 
      inverts H.
      forwards*: value_valueb1 H10.
      apply multi_blame_cast; eauto.      
      apply multi_blame_app; eauto.
      --
      inverts H.
      forwards*: principle_if H10.
      rewrite H in *. inverts H4.
      *
      inverts H.
      forwards*: principle_if H8.
      rewrite H in *. inverts H2. 
    + 
      forwards*: typing_regular_1 Typ. inverts H0.
      inverts Typ; try solve[forwards*: step_not_value J].
      forwards*: IHJ H9.
      inverts H0; try solve[forwards*: step_not_value J].
      forwards*: IHJ H11.
      apply multi_blame_cast; eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards*: IHJ H5.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H7.
      *
      forwards*: typing_regular_3 H4.
      forwards*: IHJ H2.
      apply multi_blame_app2; eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards*: IHJ H7.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H5.
      *
      forwards*: IHJ H4.    
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H3.
  - 
    inverts Typ.
    + 
      forwards*: principle_if H11.
      rewrite H3 in *. inverts H1.
      forwards*: Tred_blame_soundness H2.
      apply multi_blame_app; eauto.
      forwards*: value_valueb1 H11.
    + inverts H3.
      forwards*: principle_if H13.
      rewrite H3 in *. inverts H1.
      forwards*: Tred_blame_soundness H2.
      apply multi_blame_cast; eauto.      
      apply multi_blame_app; eauto.
      forwards*: value_valueb1 H.
      forwards*: principle_if H13.
      rewrite H3 in *. inverts H1.    
    +
      forwards*: principle_if H11.
      rewrite H3 in *. inverts H1.
  - 
    inverts Typ. 
    *
    lets H0':H0.
    inverts* H0.
    forwards*: Tred_blame_soundness H0'.
    *
    inverts H2.
    --
    lets H0':H0.
    inverts* H0.
    forwards*: Tred_blame_soundness H0'.
    apply multi_blame_cast; eauto.          
Qed.




Theorem soundness: forall e t A dir l b ,
  typing nil e dir A t->
  e ->** e_blame l b ->
  t ->* t_blame l b .
Proof.
  introv typ red. gen dir A t.
  inductions red;intros.
  -
  forwards*: soundness_mul_two H.
  inverts H0. inverts H1. 
  forwards*: IHred H2.
  -
  forwards*: Soundness_blame_two typ H.
Qed.


Lemma tTypedReduce_completeness: forall v t B A l b ,
  btyping nil t B v ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_blame l b) ->
  TypedReduce v l b A  (e_blame l b).
Proof.
  introv typ val red.
  forwards* h1: valueb_value2 val.
  inductions red; try solve[inverts* typ].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts* typ; inverts h1.
    forwards* h2: btyping_typing H10.
    forwards*: principle_inf h2.
    rewrite <- H3 in *. 
    eapply TReduce_blame;eauto.
    unfold not;intros nt.
    inverts H0. inverts* H.
    rewrite <- H4 in nt. inverts nt.
    inverts* H.
    rewrite <- H4 in nt. inverts nt.
Qed.



Theorem typing_elaborate_completeness_gen_blame: forall e t A n l b,
  size_exp e + size_term t < n ->
  btyping nil t A e ->
  bstep t (t_blame l b) ->
  steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t A.
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
    inverts lc.
    apply multi_bblame_appv2.
    auto. apply h2.
    +
    inverts Typ. inverts H.
    forwards* h1: valueb_value2 H3.
    forwards* h2: IHn Red H6. simpl in *; omega.
    apply multi_bblame_appv.
    auto. apply h2.
    +
     forwards* lc: btyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts lc.
     forwards* h1: IHn Red H8. simpl in *; omega.
     apply multi_bblame_anno.
     apply h1.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H11.
    forwards* h2: tTypedReduce_completeness H11 Red'.
    forwards* h3: value_decidable (e_anno e0 l b A0).
    inverts h3.
    +
    forwards* h4: value_tred_keep2 h2. inverts h4.
    +
    apply step_b.
    apply Step_annov; eauto.
Qed.


Theorem ttyping_completeness_blame: forall e t A n n1 l b,
  Deterministic_blame_Calculus ->
  n < n1 ->
  btyping nil t A e ->
  bbsteps t (t_blame l b) n ->
  steps e (e_blame l b).
Proof.
  introv dd sz typ red. gen t l b A e n.
  inductions n1; intros; try solve[omega].
  inverts* red.
  -
  forwards*: typing_elaborate_completeness_gen H2.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&ttyp1&ssz): H0.
  destruct(nn2).
  inverts* rred1.
  *
  forwards* h1: IHn1 H4.
  omega.
  *
  assert(n =0).
  omega.
  rewrite H in *.
  inverts* rred1.
  inverts* H7.
  assert(bbsteps ee2 (t_blame l b) (n0-1)).
  inverts H4.
  forwards* h1: dd H6 H7. inverts h1.
  simpl;eauto.
  assert(n2-0 = n2). omega.
  rewrite H1;eauto.
  forwards* h2: dd H6 H8.
  inverts* h2.
  forwards*: IHn1 H1.
  omega.
  +
  inverts* H0. inverts* H. inverts* H0.
  inverts* H4.
  forwards* h2: dd H H6.
  inverts* h2.
  forwards* h2: dd H H7.
  inverts* h2.
  -
  forwards*:  typing_elaborate_completeness_gen_blame H3.
Qed.


(* complete 2 *)


Lemma Tred_completeness_blame: forall v t B A l b ,
  ttyping nil v (Chk2 l b B) A t ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_blame l b) ->
  TypedReduce v l b A (e_blame l b).
Proof.
  introv typ val red.
  forwards*: valueb_value val.
  inductions red; try solve[inverts* H].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts typ; try solve[inverts H0].
    inverts H9.
    +
    inverts H3.
    inverts* H11; try solve[forwards*: abs_nlam].
    forwards*: principle_if2 H10.
    rewrite <- H3 in *; eauto.
    eapply TReduce_blame; eauto.
    unfold not; intros nt.
    inverts H0. inverts H.
    rewrite <- H4 in *.
    exfalso; apply H1; auto.
    rewrite <- H4 in *.
    inverts nt.
    inverts nt.
    rewrite <- H5 in *.
    inverts H.
    exfalso; apply H1; auto.
    rewrite <- H5 in *.
    inverts H.
    +
    eapply TReduce_blame; eauto; simpl.
    unfold not; intros nt.
    inverts nt.
    inverts H0.
    inverts H.
    inverts H4; try solve[forwards*: abs_nlam].
    exfalso; apply H1; auto. 
    inverts* H0. 
Qed.




Lemma completeness_blame_two2: forall e t dir p b A n,
  size_exp e + size_term t < n ->
  ttyping nil e dir A t->
  bstep t (t_blame p b) ->
  steps e (e_blame p b).
Proof.
  introv sz Typ J. gen t p b A dir e.
  induction n; intros;try solve[omega].
  inductions J; intros.
  - destruct E; unfold fill in *.
  + inverts Typ; simpl in *.
    * forwards: IHn J H6. simpl in *; omega. 
    apply multi_bblame_app2; eauto.
    forwards*: ttyping_regular_1 H7.
    inverts* H1.
    *
    forwards: ttyping_regular_1 H6.
    forwards: ttyping_regular_1 H7.
    destruct(value_decidable e0). auto.
    --
    lets red: J. inverts red.
    destruct E; unfold fillb in *; inverts H3.
    forwards: value_valueb H6; auto.
    forwards: bstep_not_value H9. eauto.
    inverts H4.
    forwards: Tred_completeness_blame J ; auto.
    destruct(lambda_decidable e0); eauto.
    inverts H2; try solve[inverts H6;
    exfalso; apply H3; eauto].
    inverts H2; inverts H6;
    try solve[inverts H3;simpl in *;
    exfalso; apply H15; auto].
    inverts H1.
    eapply stars_transb.
    apply stars_one.
    apply Step_betad; eauto.
    apply multi_bblame_app2; auto.
    apply step_b.
    eapply Step_annov; eauto.
    unfold not;intros nt;inverts nt.
    inverts H16.
    inverts H10.
    inverts H17; try solve[forwards: abs_nlam H19;inverts H2].
    exfalso; apply H13; auto.
    --
    assert(not(valueb t1)).
    unfold not;intros nt. 
    forwards*: valueb_value H6.
    lets red: J. inverts red;
    try solve[exfalso; apply H3; eauto].
    destruct E; unfold fillb in *; inverts H4.
    forwards: IHn H10 H6. omega.
    inverts H1.
    apply multi_bblame_app2; eauto.
    *
    inverts H0. inverts H10.
    * 
    inverts H0; try solve[inverts H3;inverts H12 ].
    --
    forwards: IHn J H7. simpl in *; omega. 
    apply multi_bblame_app2; eauto.
    forwards*: ttyping_regular_1 H9. inverts* H3.
    --
    forwards: ttyping_regular_1 H9.
    forwards: ttyping_regular_1 H7.
    destruct(value_decidable e0). auto.
    ---
    lets red: J. inverts red.
    destruct E; unfold fillb in *; inverts H5.
    forwards: value_valueb H7; auto.
    forwards: bstep_not_value H11. eauto.
    inverts H6.
    forwards: Tred_completeness_blame J ; auto.
    destruct(lambda_decidable e0); eauto.
    inverts H4; try solve[inverts H7;
    exfalso; apply H5; eauto].
    inverts H4; inverts H5;
    try solve[inverts H3;simpl in *;
    exfalso; apply H15; auto].
    inverts H0.
    eapply stars_transb.
    apply stars_one.
    apply Step_betad; eauto.
    apply multi_bblame_app2; auto.
    apply step_b.
    eapply Step_annov; eauto.
    unfold not;intros nt;inverts nt.
    inverts H18.
    ---
    assert(not(valueb t1)).
    unfold not;intros nt. 
    forwards*: valueb_value H7.
    lets red: J. inverts red;
    try solve[exfalso; apply H5; eauto].
    destruct E; unfold fillb in *; inverts H6.
    forwards: IHn H12 H7. simpl in *;omega.
    inverts H0.
    apply multi_bblame_app2; eauto.
    --
    forwards:IHn J H5. simpl in * ; omega.
    forwards lc1: ttyping_regular_1 H8.
    apply multi_bblame_appv2; auto.
    *
    forwards:IHn J H2. simpl in * ; omega.
    forwards lc1: ttyping_regular_1 H7.
    apply multi_bblame_appv2; auto.
  +
    forwards: ttyping_regular_3 Typ. simpl in *. inverts H0. 
    inverts Typ; simpl in *; try solve[forwards: bstep_not_value J].
    *
    inverts H9.
    ++
    forwards: ttyping_regular_1 H11.
    destruct(value_decidable e2); auto.
    --
      forwards: value_valueb H11; auto.
      assert(l0 = p).
      inverts* J; 
      destruct E; unfold fillb in ; inverts H6;
      forwards*: bstep_not_value H13.
      assert(b0 = b).
      inverts* J;
      destruct E; unfold fillb in ; inverts H7;
      forwards: bstep_not_value H14; auto.
      inverts H7.
      subst.
      forwards: Tred_completeness_blame H11; auto.
      inverts H.
      forwards: valueb_value H8; auto.
      forwards: principle_if2 H8; auto.
      eapply step_b.
      eapply Step_betap; auto. 
      apply H7. apply H6.
    --
      assert(not(valueb t0)).
      unfold not; intros nt.
      forwards: valueb_value H11; auto.
      inverts H.
      forwards: valueb_value H8; auto.
      lets red: J.
      inverts J.
      destruct E; unfold fillb in *; inverts H6.
      forwards: IHn H14 H11. simpl in *; omega.
      forwards: principle_if2 H8. auto.
      eapply multi_bblame_app; auto.
      apply H9.
      forwards: Tred_completeness_blame H11; auto.
      forwards: valueb_value H11; auto.
      forwards: principle_if2 H8; auto.
      eapply step_b.
      eapply Step_betap; auto. 
      apply H10. apply H6.
    ++
    forwards: ttyping_regular_1 H11.
    forwards: value_valueb H11; auto.
    forwards: bstep_not_value J; auto.
    inverts H5.
    *
    inverts H. inverts H1.
    *
    inverts H0. inverts H12.
    *
    inverts H0.
    --
    inverts H11.
    ++
    forwards: ttyping_regular_1 H13.
    destruct(value_decidable e2); auto.
    ---
      forwards: value_valueb H13; auto.
      assert(l1 = p).
      inverts* J;
      try solve[
      destruct E; unfold fillb in ; inverts H8;
      forwards: bstep_not_value H15;auto;inverts H8].
      assert(b1 = b).
      inverts* J;
      try solve[
      destruct E; unfold fillb in ; inverts H10;
      forwards: bstep_not_value H16; auto;inverts H10].
      inverts H8. inverts H10.
      forwards: Tred_completeness_blame H13; auto.
      inverts H.
      forwards: valueb_value H9; auto.
      forwards: principle_if2 H9; auto.
      eapply step_b.
      eapply Step_betap; auto. 
      apply H10. apply H8.
    ---
      assert(not(valueb t0)).
      unfold not; intros nt.
      forwards: valueb_value H13; auto.
      inverts H.
      forwards: valueb_value H9; auto.
      lets red: J.
      inverts J.
      destruct E; unfold fillb in *; inverts H8.
      forwards: IHn H16 H13. simpl in *; omega.
      forwards: principle_if2 H9. auto.
      eapply multi_bblame_app; auto.
      apply H11.
      forwards: Tred_completeness_blame H13; auto.
      forwards: valueb_value H13; auto.
      forwards: principle_if2 H9; auto.
      eapply step_b.
      eapply Step_betap; auto. 
      apply H12. apply H8.
    ++
    forwards: ttyping_regular_1 H13.
    forwards: value_valueb H13;auto.
    forwards: bstep_not_value J.
    auto.
    inverts H7.
    --
    inverts H. inverts H5.
    --
    inverts H5. inverts H14.
    --
    forwards:IHn J H10. simpl in * ; omega.
    inverts H.
    forwards: valueb_value H7. auto.
    apply multi_bblame_appv; auto.
    *
    forwards:IHn J H9. simpl in * ; omega.
    inverts H.
    forwards: valueb_value H2. auto.
    apply multi_bblame_appv; auto.
  +
    simpl in *. forwards: ttyping_regular_3 Typ. inverts H0.
    inverts Typ; simpl in *; try solve[inverts J];
    try solve[forwards: bstep_not_value J; auto;inverts H0].
    *
    forwards: IHn J H7. simpl in *; omega. 
    apply multi_bblame_anno; eauto.
    *
    inverts H0; try solve[forwards: bstep_not_value J;auto;inverts H0].
    inverts H11.
    *  
    inverts H0; try solve[forwards: bstep_not_value J].
    forwards: IHJ H10; auto. simpl in *; omega.
    apply multi_bblame_anno; eauto.
    inverts H4; try solve[forwards: bstep_not_value J;auto;inverts H0].
    inverts H13.  
  -
   inverts Typ.
   +
   forwards: Tred_completeness_blame H9; auto.
   forwards: ttyping_regular_1 H9.
   apply step_b.
   destruct(value_decidable (e_anno e0 p b B)); eauto.
   forwards: value_tred_keep2 H3;auto. inverts H6.
   apply Step_annov; eauto.
   forwards: valueb_value H9;auto.
   +
   inverts H3; inverts H13.
   +
   inverts H3.
   *
   forwards: Tred_completeness_blame H12; auto.
   forwards: ttyping_regular_1 H12.
   apply step_b.
   destruct(value_decidable (e_anno e0 p b B)); eauto.
   forwards: value_tred_keep2 H7. 
   apply H3.
   inverts H8.
   apply Step_annov; eauto.
   forwards: valueb_value H12;auto.
   *
   inverts H6. inverts H11.
Qed.




Theorem typing_elaborate_completeness_blame2: forall e t A n n1 l b dir,
  Deterministic_blame_Calculus ->
  n < n1 ->
  ttyping nil e dir A t->
  bbsteps t (t_blame l b) n ->
  steps e (e_blame l b).
Proof.
  introv dd sz typ red. gen t l b dir A e n.
  inductions n1; intros; try solve[omega].
  inverts* red.
  -
  forwards*:  typing_elaborate_completeness_dir H2.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&ttyp1&ssz): H0.
  destruct(nn2).
  inverts* rred1.
  *
  forwards* h1: IHn1 H4.
  omega.
  *
  assert(n =0).
  omega.
  rewrite H in *.
  inverts* rred1.
  inverts* H7.
  assert(bbsteps ee2 (t_blame l b) (n0-1)).
  inverts H4.
  forwards* h1: dd H6 H7. inverts h1.
  simpl;eauto.
  assert(n2-0 = n2). omega.
  rewrite H1;eauto.
  forwards* h2: dd H6 H8.
  inverts* h2.
  forwards*: IHn1 H1.
  omega.
  +
  inverts* H0. inverts* H. inverts* H0.
  inverts* H4.
  forwards* h2: dd H H6.
  inverts* h2.
  forwards* h2: dd H H7.
  inverts* h2.
  -
  forwards*:  completeness_blame_two2 H3.
Qed.


(* sound2 *)


Lemma Tred_blame_soundness2: forall v t p b A,
  ttyping nil (e_anno v p b A) Inf2 A t->
  value v ->
  TypedReduce v p b A (e_blame p b) ->
  t ->* (t_blame p b) .
Proof.
  introv Typ val Red.
  inductions Red; intros. 
  inverts Typ. inverts H7. 
  inverts H6; simpl in *. 
  -
    inverts H10; try solve[forwards*: abs_nlam].
    inverts val.
    forwards*: principle_if2 H6.
    forwards*: value_valueb H6.
    rewrite H0 in *.
    inverts H2.
    +
    destruct A.
    *
    rewrite <- TEMP in *.
    exfalso; apply H; auto.
    *
    destruct(eq_type A1). destruct(eq_type A2).
    subst.
    --
    apply bstep_b.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    --
    eapply star_transb.
    eapply star_one.
    eapply bStep_dyna;auto.
    unfold not;intros nt;inverts nt.
    unfold not;intros nt;inverts nt.
    exfalso;apply H2; auto.
    eapply bstep_b.
    rewrite fillb_cast.
    eapply blame_stepb;eauto.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    --
    eapply star_transb.
    eapply star_one.
    eapply bStep_dyna;auto.
    unfold not;intros nt;inverts nt.
    unfold not;intros nt;inverts nt.
    exfalso;apply H0; auto.
    eapply bstep_b.
    rewrite fillb_cast.
    eapply blame_stepb;eauto.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    *
    rewrite <- TEMP in *.
    exfalso; apply H; auto.
    +
    destruct A.
    *
    apply bstep_b.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    *
    rewrite <- TEMP in *.
    exfalso; apply H; auto.
    *
    rewrite <- TEMP in *.
    exfalso; apply H; auto.
  -
    inverts val; simpl in *.
    forwards: value_valueb H10; auto.
    inverts H10; try solve[inverts H17].
    +
    destruct A.
    *
    inverts H0.
    apply bstep_b.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    *
    exfalso; apply H; auto.
    *
    exfalso; apply H; auto.
    +
    destruct A.
    *
    inverts H0.
    apply bstep_b.
    eapply bStep_vanyp; auto.
    unfold not;intros nt;inverts nt.
    *
    exfalso; apply H; auto.
    *
    exfalso; apply H; auto.
Qed.



Lemma Soundness_blame_two2: forall e t dir p b A,
  ttyping nil e dir A t->
  step e (e_blame p b) ->
  t ->* (t_blame p b).
Proof.
  introv Typ J. gen A dir t.
  inductions J; intros.
  - destruct E; unfold fill in *.
    + inverts* Typ.
      * forwards*: IHJ H8. 
      apply multi_blame_app2; eauto.
      forwards*: ttyping_regular_3 H9.
      *
      forwards*: ttyping_regular_3 H9.
      forwards*: IHJ H8.
      apply multi_blame_app2; eauto.
      apply multi_blame_cast; eauto.
      * 
      inverts H0.
      ++
      forwards*: IHJ H10. 
      apply multi_blame_app2; eauto.
      forwards*: ttyping_regular_3 H11.
      ++
      forwards*: ttyping_regular_3 H11.
      forwards*: IHJ H10.
      apply multi_blame_app2; eauto.
      apply multi_blame_cast; eauto.
    + 
      inverts Typ.
      *
      forwards*: ttyping_regular_1 H9. inverts H0.
      inverts H9; try solve[forwards*: step_not_value J].
      forwards*: IHJ H10. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H8.
      apply multi_blame_cast; eauto.
      *
      inverts H.
      forwards*: principle_if2 H8.
      rewrite H in *. inverts H2.
      *
      inverts H0.
      -- 
      forwards*: ttyping_regular_1 H11. inverts H0.
      inverts H11; try solve[forwards*: step_not_value J].
      forwards*: IHJ H12. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb H10.
      apply multi_blame_cast; eauto.
      --
      inverts H.
      forwards*: principle_if2 H10.
      rewrite H in *. inverts H4.
    + 
      forwards*: ttyping_regular_1 Typ. inverts H0.
      inverts Typ; try solve[forwards*: step_not_value J].
      forwards*: IHJ H9.
      apply multi_blame_cast; eauto.
      forwards*: ttyping_regular_1 H0. inverts H4.
      inverts H0; try solve[forwards*: step_not_value J].
      forwards*: IHJ H12.
      apply multi_blame_cast; eauto.
    +
      forwards*: ttyping_regular_3 Typ. 
      inverts Typ; try solve[forwards*: step_not_value J].
      *
      inverts H1.
      inverts H0.
      forwards*: IHJ H6.
      apply multi_blame_app2; eauto.
      *
      inverts H0.
      forwards*: IHJ H3.
      apply multi_blame_app2; eauto.
    +
      forwards*: ttyping_regular_3 Typ.
      inverts H. 
      inverts Typ; try solve[forwards*: step_not_value J].
      *
      inverts H.
      forwards*: value_valueb H6.
      forwards*: IHJ H8.
      apply multi_blame_app; eauto.
      *
      forwards*: value_valueb H3.
      forwards*: IHJ H5.
      apply multi_blame_app; eauto.
  - 
   inverts Typ.
   + 
    forwards*: principle_if2 H11.
    rewrite H3 in *. inverts H1.
    forwards*: Tred_blame_soundness2 H2.
    apply multi_blame_app; eauto.
    forwards*: value_valueb H11.
   +
      forwards*: principle_if2 H11.
      rewrite H3 in *. inverts H1.
   + inverts H3.
     forwards*: principle_if2 H13.
    rewrite H3 in *. inverts H1.
    forwards*: Tred_blame_soundness2 H2.
    apply multi_blame_app; eauto.
    forwards*: value_valueb H.
    forwards*: principle_if2 H13.
    rewrite H3 in *. inverts H1.
  - inverts Typ. 
    *
    lets H0':H0.
    inverts* H0.
    forwards*: Tred_blame_soundness2 H0'.
    *
    lets H0':H0.
    inverts* H0.
    *
    inverts H2.
    --
    lets H0':H0.
    inverts* H0.
    forwards*: Tred_blame_soundness2 H0'.
    --
    lets H0':H0.
    inverts* H0.
Qed.




Theorem soundness2: forall e t A dir l b ,
  ttyping nil e dir A t->
  e ->** e_blame l b ->
  t ->* t_blame l b .
Proof.
  introv typ red. gen dir A t.
  inductions red;intros.
  -
  forwards*: typing_elaborate_soundness_dir2 H.
  inverts H0. inverts H1. 
  forwards*: IHred H2.
  -
  forwards*: Soundness_blame_two2 typ H.
Qed.
