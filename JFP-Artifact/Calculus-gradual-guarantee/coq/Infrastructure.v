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


Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).


Notation "t ->** r" := (steps t r) (at level 68).


Lemma stars_one:
forall a b, step a (e_exp b) -> steps a (e_exp b).
Proof.
eauto using steps.
Qed.

Lemma stars_trans:
forall a b, steps a (e_exp b) -> forall c, steps b (e_exp c) -> steps a (e_exp c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Hint Resolve stars_one stars_trans : core.


Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : term => fv_term x) in
  constr:(A `union` B `union` C `union` D `union` F `union` G).



Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.



Lemma walue_lc : forall v,
    walue v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.


Lemma walue_value: forall v,
 walue v ->
 value v.
Proof.
  introv val.
  inductions val; eauto.
  eapply value_fanno; eauto. reflexivity.
Qed.

Hint Resolve walue_value  value_lc walue_lc : core.


Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0;
  inverts* H3;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fill in H; inverts* H].
Qed.

Lemma step_not_walue: forall (v:exp),
    walue v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0;
  inverts* H3;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fill in H; inverts* H].
Qed.


Lemma multi_rred_app : forall v t t',
    value v -> t ->** (e_exp t') -> (e_app v t) ->** (e_exp (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v)). eauto.
  forwards*: do_step H1 H.
Qed.


Lemma multi_bblame_app : forall v t,
    value v -> t ->** (e_blame) -> (e_app v t) ->** (e_blame).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appCtxR v)). eauto.
  forwards*: do_step H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appCtxR v)). eauto.
  forwards*: blame_step H0 H.
Qed.


Lemma multi_rred_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->** (e_exp t1') -> (e_app t1 t2) ->** (e_exp (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.


Lemma multi_bblame_app2 : forall t1 t2 ,
    lc_exp t2 -> t1 ->** e_blame -> (e_app t1 t2) ->** e_blame.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: do_step H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: blame_step H0 H.
Qed.

Lemma multi_rred_anno : forall t t' A,
    t ->** (e_exp t') -> (e_anno t A) ->** (e_exp (e_anno t' A )).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformed (annoCtx A)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_bblame_anno : forall t A,
    t ->** e_blame -> (e_anno t A) ->** e_blame.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (annoCtx A)). eauto.
  forwards*: do_step H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (annoCtx A)). eauto.
  forwards*: blame_step H0 H.
Qed.