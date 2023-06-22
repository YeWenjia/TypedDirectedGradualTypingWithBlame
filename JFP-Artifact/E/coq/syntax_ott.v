Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition i : Set := nat.
Definition b : Set := bool.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_dyn : typ (*r dynamic type *)
 | t_pro (A:typ) (B:typ).

Inductive st : Set :=  (*r input type or projection label *)
 | st_ty (A:typ).

 Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_pro (e1:exp) (e2:exp)
 | e_l (e:exp) 
 | e_r (e:exp)
 | e_val (e:exp) (A: typ).

 Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

 Definition ctx : Set := list ( atom * typ ).

 Definition ls : Set := list st.
 
 (* EXPERIMENTAL *)
 (** auxiliary functions on the new list types *)
 (** library functions *)
 (** subrules *)
 (** arities *)
 (** opening up abstractions *)
 Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
    match e__6 with
    | (e_var_b nat) => 
        match lt_eq_lt_dec nat k with
          | inleft (left _) => e_var_b nat
          | inleft (right _) => e_5
          | inright _ => e_var_b (nat - 1)
        end
    | (e_var_f x) => e_var_f x
    | (e_lit i5) => e_lit i5
    | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
    | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
    | (e_pro e1 e2) => e_pro (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_l e) => e_l (open_exp_wrt_exp_rec k e_5 e)
    | (e_r e) => e_r (open_exp_wrt_exp_rec k e_5 e)
    | e_val e t => e_val (open_exp_wrt_exp_rec k e_5 e) t
  end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (e:exp),
      ( forall x , lc_exp  (open_exp_wrt_exp e (e_var_f x))  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_pro : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_pro e1 e2))
 | lc_e_l : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_l e))
 | lc_e_r : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_r e))
 | lc_e_val : forall (e:exp) t,
    (lc_exp e) ->
    (lc_exp (e_val e t)).



(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | (e_pro e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_l e) => (fv_exp e)
  | (e_r e) => (fv_exp e)
  | e_val e t => (fv_exp e)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_pro e1 e2) => e_pro (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_l e) => e_l (subst_exp e_5 x5 e)
  | (e_r e) => e_r (subst_exp e_5 x5 e)
  | (e_val e t) => e_val (subst_exp e_5 x5 e) t
end.


(* principal types for values*)
Fixpoint dynamic_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_anno e A) => A
  | (e_pro v1 v2) => t_pro (dynamic_type v1) (dynamic_type v2)
  | e_val e t => t
  | _ => t_dyn
  end.



Inductive pval : exp -> Prop :=    
 | pval_abs : forall (e:exp) A1 A2 B1 B2,
     lc_exp (e_abs e) ->
     pval  (e_anno (e_anno (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))
 | pval_lit : forall (i5:i),
     pval (e_lit i5) 
 | pval_pro : forall u1 u2,
     pval u1 ->
     pval u2 ->
     pval  (e_pro u1 u2).




(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_anno : forall p A,
    pval p ->
    value (e_val p A).



(* defns Consistency *)
Inductive sim : typ -> typ -> Prop :=    (* defn sim *)
 | S_i : 
     sim t_int t_int
 | S_arr : forall (A B C D:typ),
     sim C A ->
     sim B D ->
     sim (t_arrow A B) (t_arrow C D)
 | S_dynl : forall (A:typ),
     sim t_dyn A
 | S_dynr : forall (A:typ),
     sim A t_dyn
 | S_pro : forall (A B C D:typ),
     sim A C ->
     sim B D ->
     sim (t_pro A B) (t_pro C D).


Inductive pattern : typ -> typ -> Prop :=    
 | pa_fun : forall A1 A2,
    pattern (t_arrow A1 A2) (t_arrow A1 A2)
 | pa_dyn : 
    pattern t_dyn (t_arrow t_dyn t_dyn).


Inductive pattern_pro : typ -> typ -> Prop :=    
 | ppa_fun : forall A1 A2,
    pattern_pro (t_pro A1 A2) (t_pro A1 A2)
 | ppa_dyn : 
    pattern_pro t_dyn (t_pro t_dyn t_dyn).



(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    (* defn sim *)
 | tp_i : 
     tpre t_int t_int
 | tp_dyn : forall (A:typ),
     tpre A t_dyn
 | tp_abs : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_arrow A B) (t_arrow C D)
 | tp_pro : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_pro A B) (t_pro C D).


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) A0 (A:typ) (e:exp) B,
      pattern A0 (t_arrow A B) ->
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs e) Chk A0
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A A1 A2:typ),
     Typing G e1 Inf A ->
     pattern A (t_arrow A1 A2) ->
     Typing G e2 Chk A1 ->
     Typing G (e_app e1 e2) Inf A2
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     Typing G e Chk B 
 | Typ_pro : forall (G:ctx) (e1 e2:exp) (A1 A2:typ),
     Typing G e1 Inf A1 ->
     Typing G e2 Inf A2 ->
     Typing G (e_pro e1 e2) Inf (t_pro A1 A2)
 | Typ_l : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G (e_l e) Inf A1
 | Typ_r : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G  (e_r e)  Inf A2
 | Typ_val : forall (G:ctx) (p:exp) A,
      uniq  G  ->
     pval p ->
     Typing nil p Chk A ->
     tpre (dynamic_type p) A -> 
     Typing G (e_val p A) Inf A
 | Typ_absv : forall (G:ctx) L (e e2:exp) A B,
     ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G e2 Inf A ->
     Typing G (e_app (e_abs e) e2) Chk B.


Inductive simpl_item : Type :=
     | sappCtxL : exp -> simpl_item
     | sappCtxR : exp -> simpl_item
     | sproCtxL : exp -> simpl_item
     | sproCtxR : exp -> simpl_item
     | slCtx : simpl_item
     | srCtx : simpl_item
     | sannoCtx : typ -> simpl_item.


Inductive simpl_wf : simpl_item -> Prop :=
     | swf_appl : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (sappCtxL e)
     | swf_appr : forall e,
                    simpl_wf (sappCtxR (e_abs e))
     | swf_prol : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (sproCtxL e)
     | swf_pror : forall (v : exp),
                    value v ->
                    simpl_wf (sproCtxR v)
     | swf_l : 
                    simpl_wf (slCtx)
     | swf_r : 
                    simpl_wf (srCtx)
     | swf_anno : forall t,
                    simpl_wf (sannoCtx t).

Definition simpl_fill (EE : simpl_item) (e : exp) : exp :=
     match EE with
     | sappCtxL e2 => e_app e e2
     | sappCtxR v1 => e_app v1 e
     | sproCtxL e2 => e_pro e e2
     | sproCtxR v1 => e_pro v1 e
     | slCtx => e_l e
     | srCtx => e_r e
     | sannoCtx t => e_anno e t
     end.

Inductive res : Type :=
     | Expr  : exp -> res
     | Blame :  res.


Inductive meet : typ -> typ -> typ -> Prop :=    
  | me_int : 
     meet t_int t_int t_int 
  | me_arrow : forall A1 B1 A2 B2 A3 B3,
     meet A2 A1 A3 ->
     meet B1 B2 B3 ->
     meet (t_arrow A1 B1) (t_arrow A2 B2) (t_arrow A3 B3)
  | me_pro : forall A1 B1 A2 B2 A3 B3,
     meet A1 A2 A3 ->
     meet B1 B2 B3 ->
     meet (t_pro A1 B1) (t_pro A2 B2) (t_pro A3 B3)
 | me_dynl : forall A,
     meet A t_dyn A 
 | me_dynr : forall A,
     meet t_dyn A A 
.


Fixpoint erase (v:exp) : exp :=
  match v with
  | (e_anno p A) => p
  | _ => v
  end.



Inductive Cast : exp -> typ -> typ -> res -> Prop :=    
 | Cast_lit : forall i (A:typ) (B:typ) A',
     Cast (e_lit i)  A A' (Expr (e_val (e_lit i) A'))
 | Cast_abs : forall e A B C D D', 
    sim (t_arrow A B) D ->
    Cast (e_anno (e_anno (e_abs e) (t_arrow A B)) C) D D' (Expr (e_val (e_anno (e_anno (e_abs e) (t_arrow A B)) D) D'))
 | Cast_absp : forall e A B C D D', 
    not(sim (t_arrow A B) D) ->
    Cast (e_anno (e_anno (e_abs e) (t_arrow A B)) C) D D' Blame
 | Cast_pro: forall p1 p2 A1 A2 p1' p2' B B1 B2,
    pattern_pro B (t_pro B1 B2) ->
    Cast p1 A1 B1 (Expr (e_val p1' B1)) ->
    Cast p2 A2 B2 (Expr (e_val p2' B2)) ->
    Cast (e_pro p1 p2) (t_pro A1 A2) B (Expr (e_val (e_pro p1' p2') B))
 | Cast_prol: forall p1 p2 A1 A2 B B1 B2,
    pattern_pro B (t_pro B1 B2) ->
    Cast p1 A1 B1 Blame ->
    Cast (e_pro p1 p2) (t_pro A1 A2) B Blame
 | Cast_pror: forall p1 p2 A1 A2 B B1 B2,
    pattern_pro B (t_pro B1 B2) ->
    Cast p2 A2 B2 Blame ->
    Cast (e_pro p1 p2) (t_pro A1 A2) B Blame
.


(* Inductive Cast : exp -> typ -> typ -> res -> Prop :=    
 | cast_exp : forall p A B A' p' C,
     meet A B A' ->
     sim (dynamic_type p) A' ->
     Cast p A' (Expr p') ->
     Cast  (e_val p A) B C (Expr (e_val p' C))
 | cast_expp : forall p A B A' C,
     meet A B A' ->
     sim (dynamic_type p) A' ->
     Cast p A' Blame ->
     Cast  (e_val p A) B C Blame
 | cast_blame : forall p (A:typ) A' (B:typ) C,
     meet A B A' ->
     not(sim (dynamic_type p) A') ->
     Cast  (e_val p A) B C Blame
. *)


(* Inductive TypeLists : exp -> list typ -> res -> Prop :=  
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
. *)


Inductive step : exp -> res -> Prop :=
   | Step_abs : forall e A0 A B,
      lc_exp (e_abs e) ->
      pattern A0  (t_arrow A B) ->
      step (e_anno (e_abs e) A0) (Expr (e_val (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow A B)) A0))
   | Step_lit : forall i,
      step (e_lit i) (Expr (e_val (e_lit i) t_int))
   | Step_pro : forall p1 p2 t1 t2,
       pval p1 ->
       pval p2 ->
      step (e_pro (e_val p1 t1) (e_val p2 t2)) (Expr (e_val (e_pro p1 p2) (t_pro t1 t2)))
  | Step_eval E e1 e2 :
    simpl_wf E ->
    step e1 ( Expr e2 ) ->
    step (simpl_fill E e1) (Expr (simpl_fill E e2))
  | Step_blame E e1 :
    simpl_wf E ->
    step e1 Blame ->
    step (simpl_fill E e1) Blame
  | Step_nbeta : forall (e:exp) v,
    lc_exp (e_abs e) ->
     value v ->
     step (e_app (e_abs e) v)  (Expr (open_exp_wrt_exp  e v ))
  | Step_beta : forall A  B D D1 D2 C1 C2 (e:exp) e2,
     lc_exp (e_abs e) ->
     pattern D (t_arrow D1 D2) ->
     step (e_app (e_val (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow C1 C2)) D) e2) 
     (Expr (e_anno (e_anno (e_anno (e_app (e_abs e) (e_anno (e_anno (e_anno e2 D1) C1) A)) B) C2) D2)    )
  | Step_dyn : forall p1 e2 A,
     not(sim (dynamic_type p1) (t_arrow t_dyn t_dyn)) ->
     pval p1 ->
     step (e_app (e_val p1 A) e2)  Blame
  | Step_annov : forall p (A:typ) B r A',
     Cast p A' B r ->
     meet (dynamic_type p) B A' ->
     pval p ->
     step (e_anno (e_val p A) B) r
  | Step_annop : forall p (A:typ) B,
     not(sim (dynamic_type p) B) ->
      pval p ->
     step (e_anno (e_val p A) B) Blame
  | Step_lp : forall p A,
       not(sim (dynamic_type p) (t_pro t_dyn t_dyn)) ->
       pval p ->
      step (e_l (e_val p A)) Blame
  | Step_l : forall p1 p2 A A1 A2,
      pattern_pro A (t_pro A1 A2) ->
       pval p1 ->
       pval p2 ->
      step (e_l (e_val (e_pro p1 p2) A)) (Expr (e_val p1 A1))
  | Step_rp : forall p A,
      not(sim (dynamic_type p) (t_pro t_dyn t_dyn)) ->
       pval p ->
      step (e_r (e_val p A)) Blame
  | Step_r : forall p1 p2 A A1 A2,
      pattern_pro A (t_pro A1 A2) ->
       pval p1 ->
       pval p2 ->
      step (e_r (e_val (e_pro p1 p2) A)) (Expr (e_val p2 A2))
.



Inductive epre : exp -> exp -> Prop :=    
 | ep_var : forall (x:var),
    epre (e_var_f x) (e_var_f x)
 | ep_i i:
    epre (e_lit i) (e_lit i)  
 | ep_abs : forall (e1 e2:exp) (L:vars),
     ( forall x , x \notin  L  ->  
     epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
     epre (e_abs e1) (e_abs e2)
 | ep_app : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_pro : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_pro e1 e2) (e_pro e1' e2')
 | ep_l : forall  (e1 e2:exp),
     epre e1 e2 ->
     epre (e_l e1) (e_l e2)
 | ep_r : forall  (e1 e2:exp),
     epre e1 e2 ->
     epre (e_r e1) (e_r e2)
 | ep_val: forall p1 p2 t1 t2,
    pval p2 ->
    epre p1 p2 ->
    tpre t1 t2 ->
    tpre (dynamic_type p2) t2 ->
    epre (e_val p1 t1) (e_val p2 t2).



(* Inductive steps : exp -> res -> Prop :=
  | step_refl e e':
    step e (Expr e') ->
    steps e (Expr e')
  | step_n e t' e':   
    step e (Expr e') ->
    steps e' (Expr t') ->
    steps e  (Expr t')
  | step_nb e e':
    step e (Expr e') ->
    steps e' Blame ->
    steps e  Blame

  | step_b e:
    step e (Blame) ->
    steps e (Blame). *)



Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (Expr e)

  | step_n e t' e':   
    step e (Expr e') ->
    steps e' (Expr t') ->
    steps e  (Expr t')
  | step_nb e e':
    step e (Expr e') ->
    steps e' Blame ->
    steps e  Blame

  | step_b e:
    step e (Blame) ->
    steps e (Blame).

Definition diverge e := not ((exists v, steps e (Expr v) /\ value v) \/ steps e Blame).

(** infrastructure *)
Hint Constructors Cast meet pattern pattern_pro pval value sim Cast 
simpl_wf step steps tpre epre Typing lc_exp : core.


