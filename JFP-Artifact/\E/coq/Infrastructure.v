Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).


Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).

Notation "t ->* r" := (steps t r) (at level 68). 
Notation "t ->** r" := (gsteps t r) (at level 68).

Lemma star_one:
forall a b, step a (Expr b) -> steps a (Expr b).
Proof.
eauto using steps.
Qed.

Lemma star_trans:
forall a b, steps a (Expr b) -> forall c, steps b (Expr c) -> steps a (Expr c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma gstar_one:
forall a b, gstep a (Expr b) -> gsteps a (Expr b).
Proof.
eauto using steps.
Qed.

Lemma gstar_trans:
forall a b, gsteps a (Expr b) -> forall c, gsteps b (Expr c) -> gsteps a (Expr c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma gstar_transb:
forall a b, gsteps a (Expr b) -> gsteps b Blame -> gsteps a Blame.
Proof.
  introv red1 red2.
  inductions red1; eauto using gsteps.
Qed.

Hint Resolve star_one star_trans gstar_one gstar_trans gstar_transb : core.




(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).



Lemma ssvalue_lc : forall v,
    ssval v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.



Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
  forwards*: ssvalue_lc H. 
Qed.



Lemma walue_lc : forall v,
    walue v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
  forwards*: value_lc H. 
Qed.



Lemma val_wal : forall v,
    value v ->  walue v.
Proof.
  introv H.
  induction* H.
Qed.



Hint Resolve value_lc ssvalue_lc val_wal : core.


Lemma ssvalue_blame: forall (v:exp),
    ssval v -> not(step v Blame).
Proof.
  introv sval.
  unfold not;intros nt. 
  inductions sval;inverts nt;
  try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  inverts H1; try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  inverts H4; try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  destruct E; unfold simpl_fill in H; inverts* H.
  -
  destruct E; unfold simpl_fill in H; inverts* H.
Qed.

Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros.
  - inverts* H; try solve[inverts H1].
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    forwards*:ssvalue_blame H4.
    inverts* H5.
    inverts H1;inverts* H3.
    inverts H1;inverts* H3.
Qed.


Lemma step_not_walue: forall (v:exp),
    walue v -> irred v.
Proof.
  introv wal.
  unfold irred.
  inductions wal; intros.
  forwards*: step_not_value H.
  unfold not; intros nt; inverts* nt; 
  destruct E; unfold simpl_fill in H0; inverts* H0.
Qed.


Lemma sfill_appl : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addl : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addr : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxR e1) e2).
Proof.
  intros. eauto.
Qed.



Lemma sfill_prol : forall e1 e2,
  (e_pro e1 e2) = (simpl_fill (sproCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_pror : forall e1 e2,
  (e_pro e1 e2) = (simpl_fill (sproCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma sfill_l : forall e1,
  (e_l e1) = (simpl_fill (slCtx) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_r : forall e1,
(e_r e1) = (simpl_fill (srCtx) e1).
Proof.
  intros. eauto.
Qed.


Lemma multi_red_app : forall v t t',
    walue v -> t ->* (Expr t') -> (e_app v t) ->* (Expr (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sappCtxR v)). eauto.
  forwards*: do_step H0 H.
  -
  forwards*: IHRed.
  assert(simpl_wf (sappCtxR v)). eauto.
  forwards*: do_step H1 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_app t1 t2) ->* (Expr (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sappCtxL t2)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (sappCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma wmulti_red_pro : forall v t t',
    walue v -> t ->* (Expr t') -> (e_pro v t) ->* (Expr (e_pro v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sproCtxR v)). eauto.
  forwards*: do_step H0 H.
  -
  forwards*: IHRed.
  assert(simpl_wf (sproCtxR v)). eauto.
  forwards*: do_step H1 H.
Qed.

Lemma multi_red_pro : forall v t t',
    value v -> t ->* (Expr t') -> (e_pro v t) ->* (Expr (e_pro v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sproCtxR v)). eauto.
  forwards*: do_step H0 H.
  -
  forwards*: IHRed.
  assert(simpl_wf (sproCtxR v)). eauto.
  forwards*: do_step H1 H.
Qed.

Lemma multi_red_pro2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_pro t1 t2) ->* (Expr (e_pro t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sproCtxL t2)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (sproCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_red_l : forall t1 t1',
     t1 ->* (Expr t1') -> (e_l t1) ->* (Expr (e_l t1')).
Proof.
  introv Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (slCtx)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (slCtx)). eauto.
  forwards*: do_step H0 H.
Qed.


Lemma multi_red_r : forall t1 t1',
     t1 ->* (Expr t1') -> (e_r t1) ->* (Expr (e_r t1')).
Proof.
  introv Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (srCtx)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (srCtx)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma step_not_ssval: forall e e', 
 step e (Expr e') ->
 not(ssval e').
Proof.
  introv red.
  inductions red; try solve[unfold not;intros nt;inverts* nt].
  -
  destruct E; unfold simpl_fill;unfold not;intros nt;inverts* nt.
  -
  unfold not;intros nt;inverts* nt.
  inverts red; try solve[
    destruct E; unfold simpl_fill in *;inverts* H0
  ].
  inverts* H2.
  -
  inverts* H0.
  unfold not;intros nt;inverts* nt; try solve[inverts H3].
  -
  inverts H.
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  inverts H2. inverts H4.
  -
  inverts H.
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  inverts H2. inverts H5.
  (* -
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  -
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  inverts H0; inverts H3.
  inverts H1. *)
Qed.



Lemma multi_red_add : forall v t t',
    value v -> t ->* (Expr t') -> (e_add v t) ->* (Expr (e_add v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (saddCtxR v)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (saddCtxR v)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_red_add2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_add t1 t2) ->* (Expr (e_add t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (saddCtxL t2)). eauto.
  forwards*: do_step H0 H.
  -
  assert(simpl_wf (saddCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.


Lemma multi_red_anno : forall A t t',
    not (value (e_anno t A)) ->
    t ->* (Expr t') -> (e_anno t A) ->* (Expr (e_anno t' A)).
Proof.
  introv nt Red.
  inductions Red; eauto.
  assert(step (e_anno e A) (Expr (e_anno e' A))). eauto.
  forwards*: IHRed.
  unfold not; intros.
  apply nt.
  inverts H1.
  forwards*: step_not_ssval H.
Qed.


Lemma gmulti_red_app : forall v t t',
    gvalue v -> t ->** (Expr t') -> (e_app v t) ->** (Expr (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v)). eauto.
  forwards*: gdo_step H1 H.
Qed.

Lemma multi_blame_app : forall v t,
    gvalue v -> t ->** (Blame) -> (e_app v t) ->** (Blame).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (appCtxR v)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (appCtxR v)). eauto.
  forwards*: gblame_step H0 H.
Qed.


Lemma gmulti_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->** (Expr t1') -> (e_app t1 t2) ->** (Expr (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: gdo_step H0 H.
Qed.




Lemma multi_blame_app2 : forall t1 t2 ,
    lc_exp t2 -> t1 ->** Blame -> (e_app t1 t2) ->** Blame.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: gblame_step H0 H.
Qed.

Lemma gmulti_red_anno : forall A t t',
    t ->** (Expr t') -> (e_anno t A) ->** (Expr (e_anno t' A)).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (annoCtx A)). eauto.
  forwards*: gdo_step H1 H.
Qed.


Lemma multi_blame_anno : forall t A ,
    t ->** Blame -> (e_anno t A) ->** Blame.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (annoCtx A)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (annoCtx A)). eauto.
  forwards*: gblame_step H0 H.
Qed.