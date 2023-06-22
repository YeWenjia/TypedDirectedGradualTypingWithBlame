Require Import Bool.
Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntax_ott.
Require Import rules_inf.
Require Import syntaxb_ott.
Require Import syntaxl_ott.
Require Import Infrastructure.
Require Import Omega.




Scheme eexp_ind' := Induction for eexp Sort Prop.

Definition eexp_mutind :=
fun H1 H2 H3 H4 H5 H6 H7 H8  =>
eexp_ind' H1 H2 H3 H4 H5 H6 H7 H8.


Scheme eexp_rec' := Induction for eexp Sort Set.

Definition eexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8  =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Ltac default_auto ::= auto with arith lngen.


Fixpoint size_eexp (e1 : eexp) {struct e1} : nat :=
  match e1 with
    | ee_var_f x1 => 1
    | ee_var_b n1 => 1
    | ee_lit i1 => 1
    | ee_abs t1 e2 l b t2 => 1 +  (size_typ t1) + (size_eexp e2) + (size_typ t2) 
    | ee_app e2 p b e3 => 1 + (size_eexp e2) + (size_eexp e3)
    | ee_anno e2 p b A1 => 1 + (size_eexp e2) + (size_typ A1)
    | ee_add => 1
    | ee_addl i1 => 1
  end.




Lemma erase_open2: forall n e v,
 (erase (open_eexp_wrt_eexp_rec n v e )) = 
 (open_exp_wrt_exp_rec n (erase v) (erase e) ).
Proof.
    introv. gen n v.
    inductions e; intros;simpl in *; eauto;
    try solve[f_equal; eauto].
    -
    destruct(lt_eq_lt_dec n n0); simpl in *; eauto.
    destruct s; eauto.
Qed.


Lemma erase_open: forall n e x,
 (erase (open_eexp_wrt_eexp_rec n (ee_var_f x)  e )) = 
 (open_exp_wrt_exp_rec n (e_var_f x) (erase e) ).
Proof.
    introv. gen n x.
    inductions e; intros;simpl in *; eauto;
    try solve[f_equal; eauto].
    -
    destruct(lt_eq_lt_dec n n0); simpl in *; eauto.
    destruct s; eauto.
Qed.


Theorem bgl_to_bg_typing: forall G e dir A, 
 TTyping G e dir A ->
 Typing G (erase e) dir A.
Proof.
 introv typ.
 inductions typ; simpl in *; eauto.
 -
 pick fresh x and apply Typ_abs.
 unfold open_eexp_wrt_eexp in *.
 unfold open_exp_wrt_exp in *.
 rewrite <- erase_open; eauto.
Qed.


Lemma principal_pprincipal: forall v,
 pdynamic_type v = 
 dynamic_type (erase v).
Proof.
 introv.
 inductions v; eauto.
Qed.


Lemma lc_lce: forall v,
 lc_eexp v ->
 lc_exp (erase v).
Proof.
    introv lc.
    inductions lc;simpl in *;eauto.
    unfold open_eexp_wrt_eexp in *.
    apply lc_e_abs; intros.
    unfold open_exp_wrt_exp.
    rewrite <- erase_open;eauto.
Qed.


Theorem bgl_to_bg_casting: forall e r A l b, 
 CCast e l b A r ->
 Cast (erase e) A (eraser r).
Proof.
 introv red.
 inductions red; intros;simpl in *; eauto.
 -
 rewrite principal_pprincipal in H0; eauto.
 -
 rewrite principal_pprincipal in H; eauto.
 -
 forwards*: lc_lce H.
 -
 rewrite principal_pprincipal in H; eauto.
 -
 rewrite principal_pprincipal in H0; eauto.
 -
 rewrite principal_pprincipal; eauto.
 -
 rewrite principal_pprincipal in H; eauto.
Qed.


Lemma value_evalue: forall v,
 evalue v ->
 value (erase v).
Proof.
 introv val.
 inductions val; simpl in *; eauto.
 -
 forwards*: lc_lce H.
 -
 rewrite principal_pprincipal in H; eauto.
 -
 rewrite principal_pprincipal in H; eauto.
Qed.




Lemma size_eexp_open_eexp_wrt_eexp_rec_var_mutual :
(forall e1 x1 n1,
  size_eexp (open_eexp_wrt_eexp_rec n1 (ee_var_f x1) e1) = size_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.



Lemma lce_lc: forall v n,
 size_eexp v < n ->
 lc_exp (erase v) ->
 lc_eexp v.
Proof.
 introv sz lc. gen v.
 inductions n; intros;try solve[omega].
 inductions v;simpl in *;eauto;
 try solve[inverts* lc].
 -
    inverts lc.
    apply lc_ee_abs;intros.
    forwards*: H0 x.
    unfold open_exp_wrt_exp in *.
    rewrite <- erase_open in H.
    forwards*: IHn (open_eexp_wrt_eexp_rec 0 (ee_var_f x) v).
    simpl in *.
    rewrite size_eexp_open_eexp_wrt_eexp_rec_var_mutual.
    omega.
 -
    inverts* lc.
    forwards*: IHn v1.
    simpl in *; omega.
    forwards*: IHn v2.
    simpl in *; omega.
 -
   inverts* lc.
    forwards*: IHn v.
    simpl in *; omega.
Qed.


Lemma evalue_value_gen: forall v n,
 size_eexp v < n ->
 value (erase v) ->
 evalue v.
Proof.  
 introv sz val.
 gen v.
 inductions n;intros; simpl in *; try solve[inverts* val];
 try solve[omega].
 inductions v; try solve[simpl in *; inverts* val].
 -
 forwards* lc: value_lc val.
 forwards*: lce_lc lc.
 -
 inverts val.
 +
 forwards*: IHn v. 
 simpl in *. omega.
 rewrite <- principal_pprincipal in H2.
 forwards*: IHn v. 
 simpl in *. omega.
 +
 rewrite <- principal_pprincipal in H1.
 simpl in *. 
 forwards*: IHn v.
 simpl in *. omega.
Qed.


Lemma evalue_value: forall v,
 value (erase v) ->
 evalue v.
Proof.
 introv val.
 eapply evalue_value_gen; auto.
Qed.




Theorem bgl_to_bg: forall e r, 
 sstep e r ->
 step (erase e) (eraser r).
Proof.
 introv red.
 inductions red; intros;simpl in *; eauto.
 -
 destruct E; unfold ffill in *; simpl in *; eauto.
 +
 inverts H.
 forwards*: lc_lce H1.
 assert(fill ((appCtxL (erase e))) (erase e1) = e_app (erase e1) (erase e)); eauto.
 rewrite <- H0.
 assert(fill ((appCtxL (erase e))) (erase e2) = e_app  (erase e2) (erase e)); eauto.
 rewrite <- H2; eauto.
 +
 inverts H.
 forwards*: value_evalue H4.
 rewrite principal_pprincipal in H2; eauto.
 assert(fill ((appCtxR (erase e))) (erase e1) = e_app (erase e) (erase e1)); eauto.
 rewrite <- H0.
 assert(fill ((appCtxR (erase e))) (erase e2) = e_app  (erase e) (erase e2)); eauto.
 rewrite <- H1; eauto.
 +
 inverts H.
 assert(fill ((annoCtx t)) (erase e1) = e_anno (erase e1) t); eauto.
 rewrite <- H.
 assert(fill ((annoCtx t)) (erase e2) = e_anno (erase e2) t); eauto.
 rewrite <- H0; eauto.
 -
 destruct E; unfold ffill in *; simpl in *; eauto.
 +
 inverts H.
 forwards*: lc_lce H1.
 assert(fill ((appCtxL (erase e))) (erase e1) = e_app (erase e1) (erase e)); eauto.
 rewrite <- H0; eauto.
 +
 inverts H.
 forwards*: value_evalue H4.
 rewrite principal_pprincipal in H2; eauto.
 assert(fill ((appCtxR (erase e))) (erase e1) = e_app (erase e) (erase e1)); eauto.
 rewrite <- H0; eauto.
 +
 inverts H.
 assert(fill ((annoCtx t)) (erase e1) = e_anno (erase e1) t); eauto.
 rewrite <- H; eauto.
 -
 unfold open_eexp_wrt_eexp.
 rewrite erase_open2; eauto.
 assert((open_exp_wrt_exp_rec 0 (erase v') (erase e)) = 
 (open_exp_wrt_exp (erase e) (erase v') ) ).
 simpl; eauto.
 rewrite H2.
 forwards*: bgl_to_bg_casting H1; simpl in *.
 forwards*: value_evalue H0.
 forwards*: lc_lce H.
 -
 rewrite principal_pprincipal in H1; eauto.
 forwards*: value_evalue H.
 forwards*: value_evalue H0.
 forwards*: bgl_to_bg_casting H2; simpl in *.
 -
 forwards*: value_evalue H.
 forwards*: bgl_to_bg_casting H0; simpl in *.
 assert(not (value (erase (ee_anno v l b A)))).
 unfold not;intros nt.
 apply H1.
 forwards*: evalue_value nt.
 simpl in H4; eauto.
 -
 forwards*: value_evalue H.
 forwards*: value_evalue H0.
 forwards*: value_evalue H1.
 forwards* h1: principal_pprincipal v1.
 rewrite h1 in *.
 forwards*: bgl_to_bg_casting H2; simpl in *.
 -
 forwards*: value_evalue H.
Qed.

