Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
    syntax_ott
    syntaxb_ott
    rules_inf
    rulesb_inf
    Typing 
    Infrastructure
    Infrastructure_b
    Typing_b
    Type_Safety
    ttyping
    Omega.


Lemma tpre_factoring_right_gen: forall t1 t2 n,
size_typ t1 + size_typ t2 < n ->
ssuba t1 t2 ->
ssubb t2 t1 ->
tpre t1 t2.
Proof.
 introv sz suba subb. gen t1 t2.
 inductions n; intros;try solve[omega].
 inductions suba; eauto; simpl in *.
 inverts subb.
 -
 forwards*: IHn H3 H. omega.
 forwards*: IHn suba H5. omega.
 -
 eauto.
Qed.



Lemma ttpre_factoring_right: forall t1 t2,
ssuba t1 t2 ->
ssubb t2 t1 ->
tpre t1 t2.
Proof.
 introv suba subb.
 eapply tpre_factoring_right_gen; eauto.
Qed.


Lemma ssub_factoring_right_gen: forall t1 t2 n,
size_typ t1 + size_typ t2 < n ->
ssuba t1 t2 ->
ssubb t1 t2 ->
ssub t1 t2.
Proof.
 introv sz suba subb. gen t1 t2.
 inductions n; intros; try solve[omega].
 inductions suba; eauto.
 -
 inverts* subb; eauto. simpl in *.
 forwards*: IHn H3 H. omega.
 forwards*: IHn suba H5. omega.
 inverts suba.
 inverts* H.
 -
 inverts* subb.
Qed.


Lemma ssub_factoring_right: forall t1 t2,
ssuba t1 t2 ->
ssubb t1 t2 ->
ssub t1 t2.
Proof.
 introv suba subb.
 eapply ssub_factoring_right_gen; eauto.
Qed.


Lemma ssub_factoring: forall t1 t2,
ssub t1 t2 ->
ssuba t1 t2 /\
ssubb t1 t2.
Proof.
 introv sub.
 inductions sub; eauto.
 -
 inverts IHsub1. inverts* IHsub2.
Qed.



Lemma ttpre_factoring: forall t1 t2,
tpre t1 t2 ->
ssuba t1 t2 /\
ssubb t2 t1.
Proof.
 introv tp.
 inductions tp; eauto.
 -
 inverts IHtp1. inverts* IHtp2.
Qed.

Lemma sub_factoring: forall t1 t2,
sub t1 t2 ->
suba t1 t2 /\
subb t1 t2.
Proof.
 introv sub.
 inductions sub; eauto.
 -
 inverts IHsub1. inverts* IHsub2.
 -
 inductions H; try solve[inverts* sub].
Qed.



Lemma tpre_factoring: forall t1 t2,
tpre t1 t2 ->
suba t1 t2 /\
subb t2 t1.
Proof.
 introv tp.
 inductions tp; eauto.
 -
 inverts IHtp1. inverts* IHtp2.
Qed.



Lemma safe_TypedReduction: forall w A w' l b l0 b0,
 walue w ->
 Safe nil (e_anno w l0 b0 A) l b ->
 TypedReduce w l0 b0 A (e_exp w') ->
 Safe nil w' l b.
Proof.
  introv wal sf red.
  inductions red; eauto;
  try solve[inverts* sf].
  -
  inverts H. inverts H1. inverts* H2.
  +
  inverts sf; try solve[inverts wal].
  *
   forwards: principle_inf H9; auto.
   rewrite <- H1 in *. inverts H2.
   eapply Safe_annoeq;eauto. 
  *
    forwards*: principle_inf H9.
   rewrite <- H1 in *. inverts H2.
   eapply Safe_annoeqn;eauto. 
   inductions H12; eauto.
  *
   apply Safe_anno; eauto.
  +
  rewrite H3 in *.
  exfalso; apply H0; auto. 
  -
    inverts sf.
    +
    inverts H5. inverts H. inverts H1.
    inductions H8; eauto.
    exfalso; apply H0; auto.
    +
    inverts H5. inverts H. inverts H1.
    inverts* H2.
    assert(subb (t_arrow t_dyn t_dyn) (t_arrow A0 B)).
    eapply subb_arr; eauto.
    inverts* H7; try solve[forwards*: abs_nlam].
    eapply Safe_annoeqn; eauto.
    inverts* H9; try solve[inverts H13].
    +
    eapply Safe_anno; eauto.
    inverts* H4; try solve[inverts H15].
  -
    inverts sf.
    +
    inverts H4. 
    inductions H7; eauto.
    +
    inverts H4. 
    inverts* H8; try solve[forwards*: abs_nlam].
    +
    inverts* H3; try solve[try solve[forwards*: abs_nlam]].
  -
    inverts H. inverts* wal; try solve[forwards*: abs_nlam]. 
    inverts H3. inverts* H4.
    inverts H7; inverts H5;inverts H0.
    +
    inverts* sf.
    * 
    inverts* H12; try solve[inverts H15].
    *
    inverts* H12.
    inverts H14. inverts H0.
    apply Safe_annoeqn with (B:= (t_arrow t_dyn t_dyn)); eauto.
    inverts* H16.
    *
    eapply Safe_anno; eauto.
    inverts* H8.
    +
    inverts* sf. 
    inverts* H13; try solve[inverts* H16].
    inverts* H13; try solve[inverts* H16].
    inverts H15. inverts H0. 
    apply Safe_annoeqn with (B:= (t_arrow t_dyn t_dyn)); eauto.
    inverts* H17.
    eapply Safe_anno; eauto.
    inverts* H11.
  -
  inverts* sf;try solve[ inverts* H9; try solve[try solve[forwards*: abs_nlam]]];
  try solve[inverts* H4; try solve[try solve[forwards*: abs_nlam]]].
Qed.




Lemma nlam_open: forall e v x,
  nlam v ->
  nlam e ->
  nlam [x ~> v] e.
Proof.
  introv nl1 nl2.
  inverts nl2; unfold subst_exp; eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
  destruct(x0 == x); try solve[inverts* e];
  eauto.
Qed.




Lemma anno_chk: forall e t1 t2 l b,
 nil ⊢ e_anno e l b t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.




Lemma safe_weaken: forall  F1 G1 G3 e1 l b ,
 Safe (G3 ++ G1) e1 l b ->
 uniq (G3 ++F1 ++  G1) ->
 Safe (G3 ++F1 ++  G1) e1 l b .
Proof.
  introv sf. gen F1.
  inductions sf; intros;eauto.
  -
    pick fresh y. apply Safe_abs with (L := union L
    (union (singleton l1)
       (union (singleton l2)
          (union (dom G1) (union (dom G3) (union (dom F1) (fv_exp e)))))));intros.
    rewrite_env (((x, A) :: G3) ++ F1 ++ G1).
    forwards: H0 x G1 ([(x, A)] ++ G3). 
    auto.
    auto.
    auto.
    assert(uniq (((x, A) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3. 
    assert(uniq (((x, A) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3.
  -
  pick fresh y. apply Safe_absn with (L := union L
  (union (singleton l2)
     (union (dom G1) (union (dom G3) (union (dom F1) (fv_exp e))))));intros.
  rewrite_env (((x, t_dyn) :: G3) ++ F1 ++ G1).
  forwards: H0 x G1 ([(x, t_dyn)] ++ G3). 
  auto.
  auto.
  auto.
  assert(uniq (((x, t_dyn) :: G3) ++ F1 ++ G1)).
  solve_uniq.
  apply H3. 
  assert(uniq (((x, t_dyn) :: G3) ++ F1 ++ G1)).
  solve_uniq.
  apply H3.
  -
    pick fresh y. apply Safe_absd with (L := union L
    (union (singleton l2)
      (union (dom G1) (union (dom G3) (union (dom F1) (fv_exp e))))));intros.
    rewrite_env (((x, t_dyn) :: G3) ++ F1 ++ G1).
    forwards: H0 x G1 ([(x, t_dyn)] ++ G3). 
    auto.
    auto.
    auto.
    assert(uniq (((x, t_dyn) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3. 
    assert(uniq (((x, t_dyn) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3.
  -
    forwards*: Typing_weaken H H0.
  -
    forwards*: Typing_weaken H H0.
  -
    forwards*: Typing_weaken H H2.
  -
   forwards*: Typing_weaken H H2.
Qed.


Lemma safe_weakening : forall E1 F1 e1 l b,
    Safe E1 e1 l b ->
    uniq (F1 ++ E1) ->
    Safe (F1 ++ E1) e1 l b.
Proof.
  intros.
  rewrite_env (nil ++ F1 ++ E1).
  apply~ safe_weaken.
Qed.


Lemma safe_open1: forall e1 u1 x A GG1 G1 l b,
 Safe (GG1 ++ [(x,A)] ++ G1) e1 l b ->
 Safe G1 u1 l b ->
 nlam u1 ->
 Typing G1 u1 Inf A ->
 Safe (GG1++G1) [x~> u1]e1 l b.
Proof.
  introv sf1 sf2 nl ty1 . gen u1.
  inductions sf1; intros; 
  simpl; eauto.
  -
    forwards*: Typing_weakening ty1.
    forwards*: Typing_weaken H0 H.
    forwards* h1: Typing_regular_2 H0.
    forwards*: safe_weakening sf2 h1.
    destruct (x0 == x); eauto.
  -
    pick fresh y.
    apply Safe_abs with (L:=  union L
    (union (singleton l1)
       (union (singleton l2)
          (union (singleton x)
             (union (dom GG1)
                (union (dom G1) (union (fv_exp e) (fv_exp u1))))))));intros.
    forwards* lc: Typing_regular_1 ty1. 
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x0, A0)] ++ GG1) ++ G1).
    forwards*: H0 x0 x  ty1 .
    auto.
  -
    pick fresh y.
    apply Safe_absn with (L:= union L
    (union (singleton l2)
       (union (singleton x)
          (union (dom GG1)
             (union (dom G1) (union (fv_exp e) (fv_exp u1)))))));intros.
    forwards* lc: Typing_regular_1 ty1. 
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x0, t_dyn)] ++ GG1) ++ G1).
    forwards*: H0 x0 x  ty1 .
    auto.
  -
    pick fresh y.
    apply Safe_absd with (L:= union L
    (union (singleton l2)
       (union (singleton x)
          (union (dom GG1)
             (union (dom G1) (union (fv_exp e) (fv_exp u1)))))));intros.
    forwards* lc: Typing_regular_1 ty1. 
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x0, t_dyn)] ++ GG1) ++ G1).
    forwards*: H0 x0 x  ty1 .
    auto.
  -
    forwards* h1: IHsf1_1.
    forwards* h2: IHsf1_2.
    forwards*: Typing_subst_1 H ty1.
  -
    forwards* h1: IHsf1_1.
    forwards* h2: IHsf1_2.
    forwards*: Typing_subst_1 H ty1.
  -
    forwards* h1: IHsf1.
    forwards*: Typing_subst_1 H ty1.
    eapply Safe_annoeq; eauto.
    forwards*: nlam_open nl H1.
  -
    forwards* h1: IHsf1.
    forwards*: Typing_subst_1 H ty1.
    eapply Safe_annoeqn; eauto.
    forwards*: nlam_open nl H1.
  -
    forwards* h1: IHsf1.
    eapply Safe_anno; eauto.
    forwards*: nlam_open nl H2.
Qed.


Lemma safe_open: forall e1 u1 x A  G1 l b,
 Safe ( [(x,A)] ++ G1) e1 l b ->
 Safe G1 u1 l b ->
 nlam u1 ->
 Typing G1 u1 Inf A ->
 Safe (G1) [x~> u1]e1 l b.
Proof.
  introv sf1 sf2 nl ty1 . introv.
  rewrite_env (nil ++ G1).
  eapply safe_open1; eauto.
Qed.



Lemma anno_prv: forall e1 e2 l1 b1 l2 b2 t t2,
 nlam e1 ->
 nlam e2 ->
 nil ⊢ e1 ⇒ t ->
 nil ⊢ e2 ⇒ t ->
 Safe nil e2 l2 b2 ->
 Safe nil (e_anno e1 l1 b1 t2) l2 b2 ->
 Safe nil (e_anno e2 l1 b1 t2) l2 b2.
Proof.
  introv nl nl2 typ1 typ2 sf1 sf2.
  inverts* sf2; try solve[inverts typ1];
  try solve[inverts nl].
  forwards*: inference_unique typ1 H4. subst*.
  forwards*: inference_unique typ1 H4. subst*.
Qed.


Lemma safe_inner: forall e A l1 b1 l2 b2,
  nlam e ->
  Safe nil (e_anno e l1 b1 A) l2 b2 ->
  Safe nil e l2 b2.
Proof.
  introv typ sf.
  inverts* sf; try solve[inverts typ].
Qed.



Lemma safe_preservation: forall dir e A l b e',
 Typing nil e dir A ->
 Safe nil e l b ->
 step e (e_exp e') ->
 Safe nil e' l b.
Proof.
  introv Typ safe Red. gen dir A.
  inductions Red;intros; eauto.
  -
    destruct E; unfold fill in *.
    +
      inverts Typ. 
      --
      destruct(lambda_decidable e1).
      +++
      inverts safe.
      *
        forwards*: safe_inner H12.
        forwards*: IHRed H8.
        forwards: preservation H11 Red.
        forwards*: anno_prv H2 H12.
        forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H8.
      forwards*: preservation H11 Red.
      +++
      forwards* ha: nlam_exist H0.
      forwards: Typing_regular_1 H8.
      inverts ha; try solve[forwards*: step_not_value Red]. 
      --
      inverts H0.
      destruct(lambda_decidable e1).
      ++
      inverts safe.
      *
      forwards*: safe_inner H14.
      forwards*: IHRed H10.
      forwards: preservation H13 Red.
      forwards*: anno_prv H4 H14.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H13.
      forwards*: preservation H13 Red.
      ++
      forwards* ha: nlam_exist H0.
      forwards: Typing_regular_1 H10.
      inverts ha; try solve[forwards*: step_not_value Red]. 
    +
      inverts Typ. 
      --
      destruct(lambda_decidable e1).
      +++
      inverts safe.
      *
        inverts H.
        forwards*: principle_inf H11.
        rewrite H in *. inverts H3.
      *
      forwards*: Typing_regular_1 H9.
      inverts H9; try solve[exfalso; apply H0; eauto];
      try solve[
      forwards*: step_not_value Red].
      forwards: safe_inner H4 H13.
      forwards: IHRed H5 H2; auto.
      forwards: preservation H2 Red.
      forwards ha: step_not_nlam Red.
      forwards*: anno_prv H6 H13.
      +++
      forwards* ha: nlam_exist H0.
      forwards: Typing_regular_1 H9.
      inverts ha; try solve[forwards*: step_not_value Red]. 
      --
      inverts safe.
      *
        inverts H.
        forwards*: principle_inf H10.
        rewrite H in *. inverts H5.
      *
      inverts H0.
      forwards*: Typing_regular_1 H14.
      inverts H14; try solve[exfalso; apply H0; eauto];
      try solve[
      forwards*: step_not_value Red].
      forwards: safe_inner H5 H12.
      forwards: IHRed H6 H3; auto.
      forwards: preservation H3 Red.
      forwards*: anno_prv H8 H12.
      forwards*: step_not_nlam Red.
    +
      inverts Typ. 
      --
      inverts safe.
      *
      forwards*: Typing_regular_1 H7.
      forwards*: step_not_value Red.
      *
      forwards*: Typing_regular_1 H7.
      forwards*: step_not_value Red.
      *
      forwards*: IHRed H7.
      forwards: preservation H5 Red.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H7.
      forwards*: preservation H5 Red.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H7.
      forwards*: step_not_nlam Red.
      --
      inverts H0.
      inverts safe.
      *
      forwards*: Typing_regular_1 H9.
      forwards*: step_not_value Red.
      *
      forwards*: Typing_regular_1 H9.
      forwards*: step_not_value Red.
      *
      forwards*: IHRed H9.
      forwards*: preservation H7 Red.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H9.
      forwards*: preservation H7 Red.
      forwards*: step_not_nlam Red.
      *
      forwards*: IHRed H9.
      forwards*: step_not_nlam Red.
    +
      inverts Typ. 
      --
      inverts safe.
      inverts* H0.
      --
      inverts* safe.
    +
       inverts Typ. 
      --
      inverts safe.
      inverts* H0.
      --
      inverts* safe.
  -
    inverts safe.
    forwards: walue_nlam H0.
    inverts* H4; try solve[inverts H8];
    try solve[forwards*: abs_nlam].
    +
    inverts Typ. inverts H2.
    inverts H8.
    pick fresh y.
    forwards*: H12.
    rewrite (subst_exp_intro y); eauto.
    forwards*: safe_open H2 H7.
    inverts H4.
    pick fresh y.
    forwards*: H12.
    rewrite (subst_exp_intro y); eauto.
    forwards*: safe_open H2 H7.
  -
   forwards*: value_group H. inverts H2.
   +
   forwards*: safe_TypedReduction safe.
   +
   inverts* H3. 
   inverts* safe;
   try solve[inverts* H0];
   try solve[forwards*: abs_nlam];
   try solve[exfalso; apply H1; eauto].
  -
   inverts safe. inverts H6.
   + inverts H0.
   + 
    inverts Typ.
    *
    inverts H3. inverts H8.
    inverts H7; try solve[forwards*: abs_nlam].
    forwards*: principle_inf H10.  
    forwards*: principle_inf H3.
    rewrite H7 in *. rewrite H11 in *.
    inverts H; try solve [forwards*: abs_nlam].
    rewrite <- H23 in *. inverts H7. inverts H6.
    inverts H13.  
    eapply Safe_annoeq; eauto. 
    *
    inverts H5. inverts H; try solve[inverts H0]. 
    forwards*: principle_inf H10.
    rewrite <- H17 in *. inverts H. inverts H13. 
    inverts H6; try solve[inverts H0].
    forwards*: principle_inf H.
    rewrite H6 in *. inverts H17. inverts H2. inverts H3. 
    eapply Safe_annoeq; eauto.
   +
    inverts H; try solve[inverts H0].
    forwards*: principle_inf H10.
    rewrite H in *. subst.
    assert((negb (negb b)) = b).
    destruct b; unfold negb; eauto.
    rewrite H2.
    inverts Typ.
    --
    inverts H3. inverts H12.
    inverts H8; try solve[inverts H0].
    forwards*: principle_inf H3. rewrite H8 in *. subst.
    inverts H7.
    inverts H13. 
    eapply Safe_annoeqn; eauto.
    eapply Safe_annoeqn; eauto.
    inductions H7; eauto. inverts H. 
    inductions H7; eauto. 
    eapply Safe_appv; eauto.
    inductions H7; eauto. inverts H. 
    inverts* H11.
    --
    inverts H6. 
    inverts H7; try solve[inverts H0].
    forwards*: principle_inf H3. rewrite H7 in *. subst.
    inverts H4.
    inverts H13. 
    eapply Safe_annoeqn; eauto.
    eapply Safe_annoeqn; eauto.
    inductions H4; eauto. inverts H. 
    inductions H4; eauto. 
    eapply Safe_appv; eauto.
    inductions H4; eauto. inverts H. 
    inverts* H11.
   +
    inverts Typ. 
    *
    inverts H3. inverts H10.
    apply Safe_anno; eauto.
    inverts H; try solve[inverts H0].
    inverts H7; try solve[inverts H0].
    forwards*: principle_inf H.
    rewrite H7 in *. subst. 
    eapply Safe_appv; eauto.
    eapply Safe_anno; eauto.
    destruct b1; unfold negb; eauto.
    *
    inverts H5.
    inverts H6; try solve[inverts H0].
    inverts H; try solve[inverts H0].
    forwards*: principle_inf H3.
    rewrite <- H20 in *. subst.
    apply Safe_anno; eauto.
    eapply Safe_appv; eauto.
    destruct b1; unfold negb; eauto. 
  -
    forwards*: value_group H0.
    inverts H3.
    +
    inverts Typ. 
    *
    forwards*: principle_inf H12.
    rewrite H3 in *. inverts H1. inverts H11.
    assert(Safe nil (e_anno v2 l0 b0 A1) l b).
    inverts* safe; try solve[
    forwards*: inference_unique H12 H11; inverts* H1];
    try solve[
    forwards*: inference_unique H12 H8; inverts* H1].
    forwards*: safe_TypedReduction H2.
    inverts* safe; try solve[
      forwards*: inference_unique H12 H15; inverts* H6].
    *
    inverts H3.
    forwards*: principle_inf H14.
    rewrite H3 in *. inverts H1. inverts H11.
    assert(Safe nil (e_anno v2 l0 b0 A2) l b).
    inverts* safe; try solve[
    forwards*: inference_unique H14 H13; inverts* H1];
    try solve[
      forwards*: inference_unique H13 H11; inverts* H1]
    .
    forwards*: safe_TypedReduction H2.
    inverts* safe;try solve[
      forwards*: inference_unique H14 H17; inverts* H8].
    +
    inverts H4. inverts* safe; try solve[inverts H10];
    try solve[inverts H11].
    forwards*: principle_inf H10.
    rewrite H3 in *. inverts H1.
    forwards*: principle_inf H10.
    rewrite H3 in *. inverts H1.
    inverts* H2. inverts* H8.
  -
    inverts safe; try solve[inverts H8].
    inverts Typ. 
    +
    inverts H12. inverts H11. 
    inverts* H9.
    +
    inverts H1. inverts H14. 
    inverts* H11.
  -
    inverts safe. inverts* H4.
    inverts Typ. inverts H1.
    inverts H8.
    pick fresh x.
    forwards*: H3 x.
    rewrite (subst_exp_intro x); eauto.
    forwards*: safe_open H1 H7.
    inverts H4.
    pick fresh x.
    forwards*: H3 x.
    rewrite (subst_exp_intro x); eauto.
    forwards*: safe_open H1 H7.
Qed.



Lemma safe_progress: forall e A l b,
 Typing nil e Chk A ->
 Safe nil e l b ->
 not(step e (e_blame l b)).
Proof.
  introv Typ safe. gen A.
  inductions safe; intros;
  try solve[unfold not;intros nt; 
  forwards*: step_not_value nt];
  try solve[unfold not;intros nt; 
  inverts* nt];
  try solve[inverts* Typ; inverts* H].
  - unfold not;intros nt; 
  inverts* nt; destruct E; unfold fill in *;inverts H0.
  -
    forwards*: Typing_regular_1 Typ.
    inverts H1.
    unfold not;intros nt; 
    forwards*: step_not_value nt.
  -
    forwards*: Typing_regular_1 Typ.
    unfold not;intros nt; 
    forwards*: step_not_value nt.
  -
    forwards*: Typing_regular_1 Typ.
    inverts H1.
    unfold not;intros nt; 
    forwards*: step_not_value nt.
  -
    inverts Typ. inverts H0.
    destruct(lambda_decidable e1).
    --
    forwards*: IHsafe1.
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H4.
    *
    assert(not(value (e_anno e1 l1 b1 (t_arrow t_dyn t_dyn)))).
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value H9
    ].
    apply H3. rewrite fill_anno.
    apply blame_step; auto.
    *
    inverts H8.
    forwards*: principle_inf H.
    rewrite H4 in *. inverts H6.
    +
    forwards*: principle_inf H.
    rewrite H4 in *. inverts H15.
    --
     forwards ha: nlam_exist H0.
     inverts* ha; try solve[inverts H].
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct(lambda_decidable e1).
    --
    destruct E; unfold fill in *; inverts* H0.
    inverts Typ. inverts H0. inverts H3.
    forwards*: principle_inf H13.
    forwards*: principle_inf H.
    rewrite H3 in *. subst.
    inverts H10.
    forwards*: IHsafe2.
    assert(not(value (e_anno e2 l1 b1 A3))).
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value H4
    ].
    apply H0. rewrite fill_anno.
    apply blame_step; auto.
    --
    destruct E; unfold fill in *; inverts* H0.
    forwards ha: nlam_exist H1.
    inverts* ha; try solve[inverts safe1].
    forwards*: Typing_regular_1 H.
    forwards*: step_not_value H4.
    forwards ha: nlam_exist H1.
    inverts* ha; try solve[inverts safe1].
    inverts Typ. inverts H0.
    forwards*: inference_unique H H13. subst.
    inverts H10.
    forwards*: IHsafe2.
    assert(not(value (e_anno e2 l1 b1 A3))).
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value H4
    ].
    apply H0. rewrite fill_anno.
    apply blame_step; auto.
    +
    inverts Typ. inverts H0.
    forwards*: principle_inf H.
    rewrite H0 in H8. inverts H8.
    inverts H9.
    inverts* safe2.
    inverts H12. inverts* H17.
    destruct b; unfold negb in H16; inverts H16.
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H2.
    +
    inverts H8. inverts H.
    inverts* H0.
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H2.
    +
    inverts* H8; try solve[
      inductions b; try solve[inverts* H2]
    ].
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H3.
    inverts Typ. inverts H3.
    forwards*: IHsafe.
    +
    inverts* H9.
  -
    unfold not;intros nt;inverts* nt.
    destruct E; unfold fill in *; inverts* H.
    +
    inverts* Typ. inverts* H.
    forwards* h1: Typing_chk H6.
    lets(tt1&ttyp1):h1.
    forwards*: IHsafe1.
    +
    inverts* Typ. inverts* H.
Qed.


