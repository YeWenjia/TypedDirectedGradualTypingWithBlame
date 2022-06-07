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
forall a b l b1, gsteps a (Expr b) -> gsteps b (Blame l b1) -> gsteps a (Blame l b1).
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




Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
Qed.

Lemma gvalue_lc : forall v,
    gvalue v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.

Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros.
  - inverts H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    inverts* H5. inverts* H5. inverts* H6.
  - inverts* H.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
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


Lemma multi_red_anno : forall A t t' l b,
    not (value (e_anno t l b A)) ->
    t ->* (Expr t') -> (e_anno t l b A) ->* (Expr (e_anno t' l b A)).
Proof.
  introv nt Red.
  inductions Red; eauto.
  assert(step (e_anno e l b A) (Expr (e_anno e' l b A))). eauto.
  forwards*: IHRed.
  unfold not; intros.
  apply nt.
  inverts H1.
  inverts* H.
  destruct E; unfold simpl_fill in H1; inverts* H1.
  inverts* H2.
  inverts* H.
  destruct E; unfold simpl_fill in H1; inverts* H1.
  inverts* H5.
  destruct E; unfold simpl_fill in H; inverts* H.
  inverts* H1.
  inverts* H2; try solve[inverts* H1].
Qed.

Lemma multi_red_app : forall v t t' l b,
    walue v -> t ->* (Expr t') -> (e_app v l b t) ->* (Expr (e_app v l b t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(simpl_wf (sappCtxR v l b)). eauto.
  forwards*: do_step H1 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1' l b,
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_app t1 l b t2) ->* (Expr (e_app t1' l b t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(simpl_wf (sappCtxL t2 l b)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_red_add2 : forall t1 t2 t1' l1 b1 l2 b2,
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_add t1 l1 b1 t2 l2 b2) ->* (Expr (e_add t1' l1 b1 t2 l2 b2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(simpl_wf (saddCtxL l1 b1 t2 l2 b2)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_red_add : forall v t t' l1 b1 l2 b2,
    value v -> t ->* (Expr t') -> (e_add v l1 b1 t l2 b2) ->* (Expr (e_add v l1 b1 t' l2 b2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(simpl_wf (saddCtxR l1 b1 v l2 b2)). eauto.
  forwards*: do_step H1 H.
Qed.



Lemma gmulti_red_app : forall v t t' l b,
    gvalue v -> t ->** (Expr t') -> (e_app v l b t) ->** (Expr (e_app v l b t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v l b)). eauto.
  forwards*: gdo_step H1 H.
Qed.

Lemma multi_blame_app : forall v t l1 b1 l2 b2,
    gvalue v -> t ->** (Blame l1 b1) -> (e_app v l2 b2 t) ->** (Blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (appCtxR v l2 b2)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (appCtxR v l2 b2)). eauto.
  forwards*: gblame_step H0 H.
Qed.


Lemma gmulti_red_app2 : forall t1 t2 t1' l b,
    lc_exp t2 -> t1 ->** (Expr t1') -> (e_app t1 l b t2) ->** (Expr (e_app t1' l b t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2 l b)). eauto.
  forwards*: gdo_step H0 H.
Qed.

Lemma multi_blame_app2 : forall t1 t2 l b l0 b0 ,
    lc_exp t2 -> t1 ->** (Blame l b) -> (e_app t1 l0 b0 t2) ->** (Blame l b).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (appCtxL t2 l0 b0)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (appCtxL t2 l0 b0)). eauto.
  forwards*: gblame_step H0 H.
Qed.

Lemma gmulti_red_anno : forall A t t' l b,
    t ->** (Expr t') -> (e_anno t l b A) ->** (Expr (e_anno t' l b A)).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (annoCtx l b A)). eauto.
  forwards*: gdo_step H1 H.
Qed.


Lemma multi_blame_anno : forall t A l b l0 b0,
    t ->** (Blame l b) -> (e_anno t l0 b0 A) ->** (Blame l b).
Proof.
  introv Red.
  inductions Red; eauto.
  eapply gstep_nb.
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: gdo_step H0 H.
  simpl. forwards*: IHRed.
  apply gstep_b. 
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: gblame_step H0 H.
Qed.