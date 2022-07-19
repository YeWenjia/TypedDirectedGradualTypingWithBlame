
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntaxb_ott.


Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_add : exp (*r addition *)
 | e_addl (i5:i) (*r addl *)
 | e_appv (e1:exp) (e2:exp) (*r applications *).

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

Definition ctx : Set := list ( atom * typ ).

Definition ls : Set := list st.


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
  | e_add => e_add 
  | (e_addl i5) => e_addl i5
  | (e_appv e1 e2) => e_appv (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
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
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_add : 
     (lc_exp e_add)
 | lc_e_addl : forall (i5:i),
     (lc_exp (e_addl i5))
 | lc_e_appv : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_appv e1 e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | e_add => {}
  | (e_addl i5) => {}
  | (e_appv e1 e2) => (fv_exp e1) \u (fv_exp e2)
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
  | e_add => e_add 
  | (e_addl i5) => e_addl i5
  | (e_appv e1 e2) => e_appv (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_anno e A) => A
  | (e_abs e) => (t_arrow t_dyn t_dyn)
  | (e_add) => (t_arrow t_int (t_arrow t_int t_int))
  | (e_addl i5) => (t_arrow t_int t_int)
  | _ => t_dyn
  end.



(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_add : 
     value e_add
 | value_addl : forall (i5:i),
     value  ( (e_addl i5) ) 
 | value_abs : forall e ,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | value_fanno : forall (v:exp) (A B C D:typ),
     value v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     value (e_anno v (t_arrow A B))
 | value_dyn : forall (v:exp),
     Ground   (principal_type  v )   ->
     value v ->
     value  ( (e_anno v t_dyn) ) .


Inductive walue : exp -> Prop :=    (* defn value *)
 | walue_lit : forall (i5:i),
     walue (e_lit i5)
 | walue_add : 
     walue e_add
 | walue_addl : forall (i5:i),
     walue  ( (e_addl i5) ) 
 | walue_abs : forall e (A B :typ),
     lc_exp (e_abs e) ->
     walue (e_anno (e_abs e) (t_arrow A B))
 | walue_adyn : forall e,
     lc_exp (e_abs e) ->
     walue (e_anno (e_abs e) t_dyn)
 | walue_fanno : forall (v:exp) (A B C D:typ),
     walue v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     walue (e_anno v (t_arrow A B))
 | walue_dyn : forall (v:exp),
     Ground   (principal_type  v )   ->
     walue v ->
     walue  ( (e_anno v t_dyn) ) .


Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)).


Inductive pattern : typ -> typ -> Prop :=
 | pa_abs : forall A B,
   pattern (t_arrow A B) (t_arrow A B)
 | pa_dyn:
   pattern t_dyn (t_arrow t_dyn t_dyn).


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs e) Chk (t_arrow A B)
 | Typ_absd : forall (L:vars) (G:ctx) (e:exp),
      ( forall x , x \notin  L  -> Typing  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn )  ->
     Typing G (e_abs e) Chk t_dyn
 | Typ_sugar : forall (L:vars) (G:ctx) (e:exp),
     ( forall x , x \notin  L  -> Typing  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn )  ->
    Typing G (e_abs e) Inf (t_arrow t_dyn t_dyn)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A1 A2 A:typ),
     pattern A (t_arrow A1 A2) ->
     Typing G e1 Inf A ->
     Typing G e2 Chk A1 ->
     Typing G (e_app e1 e2) Inf A2
 | Typ_add : forall (G:ctx),
     uniq  G  ->
     Typing G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) )
 | Typ_addl : forall (G:ctx) (i1:i),
     uniq  G  ->
     Typing G (e_addl i1) Inf (t_arrow t_int t_int)
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     not(exists e', e = (e_abs e')) ->
     Typing G e Chk B
 | Typ_appv : forall (G:ctx) (v1 v2:exp) (A1 A2:typ),
     uniq G ->
     value v1 ->
     walue v2 ->
     Typing nil v1 Inf (t_arrow A1 A2) ->
     Typing nil v2 Inf A1 ->
     Typing G (e_appv v1 v2) Inf A2.


Inductive ttyping : ctx -> exp -> dirflag -> typ -> term -> Prop :=    (* defn Typing *)
 | ttyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     ttyping G (e_lit i5) Inf t_int (trm_lit i5)
 | ttyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     ttyping G (e_var_f x) Inf A (trm_var_f x)
 | ttyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ) (t:term),
      ( forall x , x \notin  L  -> ttyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B ( open_term_wrt_term t (trm_var_f x) ))  ->
     ttyping G (e_abs e) Chk (t_arrow A B) (trm_abs A t)
 | ttyp_absd : forall (L:vars) (G:ctx) (e:exp) (t:term),
      ( forall x , x \notin  L  -> ttyping  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn ( open_term_wrt_term t (trm_var_f x) ))  ->
     ttyping G (e_abs e) Chk t_dyn (trm_cast (trm_abs t_dyn t) (t_arrow t_dyn t_dyn) t_dyn) 
 | ttyp_sugar : forall (L:vars) (G:ctx) (e:exp) (t:term),
     ( forall x , x \notin  L  -> ttyping  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn ( open_term_wrt_term t (trm_var_f x) ))  ->
    ttyping G (e_abs e) Inf (t_arrow t_dyn t_dyn) (trm_abs t_dyn t)
 | ttyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ) (t1 t2:term),
     ttyping G e1 Inf (t_arrow A B) t1 ->
     ttyping G e2 Chk A t2 ->
     ttyping G (e_app e1 e2) Inf B (trm_app t1 t2)
 | ttyp_add : forall (G:ctx),
      uniq  G  ->
     ttyping G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) ) trm_add
 | ttyp_addl : forall (G:ctx) (i1:i),
      uniq  G  ->
     ttyping G (e_addl i1) Inf (t_arrow t_int t_int) (trm_addl i1)
 | ttyp_anno : forall (G:ctx) (e:exp) (A:typ) (t:term),
     ttyping G e Chk A t ->
     ttyping G  ( (e_anno e A) )  Inf A t
 | ttyp_sim : forall (G:ctx) (e:exp) (B A:typ) (t:term),
     ttyping G e Inf A t ->
     sim A B ->
     not(exists e', e = (e_abs e')) ->
     ttyping G e Chk B (trm_cast t A B)
 | ttyp_appv : forall (G:ctx) (v1 v2:exp) (A1 A2:typ) t1 t2,
     uniq G ->
     value v1 ->
     walue v2 ->
     ttyping nil v1 Inf (t_arrow A1 A2) t1 ->
     ttyping nil v2 Inf A1 t2 ->
     ttyping G (e_appv v1 v2) Inf A2 (trm_app t1 t2).


Inductive ctx_item : Type :=
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | annoCtx : typ -> ctx_item.
   
   
Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                   lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    value v ->
                    wellformed (appCtxR v)
     | wf_annoCtx : forall (A : typ),
                    wellformed (annoCtx A).
   

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | annoCtx A => e_anno e A
     end.

   
Inductive res : Type :=
     | e_exp  : exp -> res
     | e_blame : res.    


(* defns Semantics *)
Inductive TypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | TReduce_abs: forall v A B C D,
   sim (t_arrow C D) (t_arrow A B) ->
   principal_type v = (t_arrow C D) ->
   TypedReduce v (t_arrow A B) (e_exp (e_anno v (t_arrow A B)))
  | TReduce_v : forall (v:exp),
   Ground(principal_type v) ->
   TypedReduce v t_dyn (e_exp (e_anno v t_dyn))
 | TReduce_lit : forall (i5:i),
     TypedReduce (e_lit i5) t_int (e_exp (e_lit i5))
 | TReduce_dd : forall (v:exp),
     lc_exp v ->
     TypedReduce  ( (e_anno v t_dyn) )  t_dyn  (e_exp  (e_anno v t_dyn) ) 
 | TReduce_anyd : forall (v:exp),
      FLike (principal_type  v )  ->
     TypedReduce v t_dyn  (e_exp (e_anno  ( (e_anno v (t_arrow t_dyn t_dyn)) )  t_dyn) ) 
 | TReduce_adyn : forall e (A:typ),
    FLike A ->
    TypedReduce  ( (e_anno (e_abs e) t_dyn) )  A  (e_exp (e_anno (e_anno (e_abs e) (t_arrow t_dyn t_dyn)) A))
 | TReduce_absd : forall e,
    TypedReduce  ( (e_anno (e_abs e) t_dyn) )  (t_arrow t_dyn t_dyn)  (e_exp (e_anno (e_abs e) (t_arrow t_dyn t_dyn)))
 | TReduce_dyna : forall (v:exp) (A:typ),
      FLike A ->
     sim (principal_type v) A ->
     not(exists e, (v = e_abs e)) ->
    TypedReduce  ( (e_anno v t_dyn) )  A  (e_exp (e_anno v A) ) 
 | TReduce_vany : forall (v:exp),
   not(exists e, (v = e_abs e)) ->
   TypedReduce (e_anno v t_dyn) (principal_type  v) (e_exp v)
 | TReduce_blame : forall (v:exp) (A:typ),
      not (sim A (principal_type  v ))  ->
     TypedReduce (e_anno v t_dyn) A e_blame.


Inductive step : exp -> res -> Prop :=   
  | do_step E e1 e2 :
       wellformed E ->
       step e1 (e_exp e2 ) ->
      step (fill E e1) (e_exp (fill E e2))
  | blame_step E e1:
      wellformed E ->
      step e1 e_blame ->
      step (fill E e1) e_blame
  | Step_nbeta : forall (e:exp) (v  : exp),
    lc_exp (e_abs e) ->
    walue v ->
    step (e_appv (e_abs e) v)  (e_exp (e_anno (open_exp_wrt_exp  e v) t_dyn) ) 
 | Step_beta : forall (A:typ) (e:exp) (B:typ) (v : exp),
    lc_exp (e_abs e) ->
    walue v ->
    step (e_appv (e_anno (e_abs e) (t_arrow A B)) v)  (e_exp (e_anno (open_exp_wrt_exp  e v) B) )  
 | Step_addL : forall (A:typ) (e:exp) (B:typ) v,
    walue v ->
    step (e_appv (e_anno (e_add) (t_arrow A B)) v)  (e_exp (e_anno (e_app e_add v) B) )  
 | Step_addR : forall (A:typ) (e:exp) (B:typ) (v : exp)  i,
    walue v ->
    step (e_appv (e_anno (e_addl i) (t_arrow A B)) v)  (e_exp (e_anno (e_app (e_addl i) v) B) )  
 | Step_betap : forall (v1:exp) (A B:typ) (v2:exp),
     value v1  ->
     value v2 ->
     principal_type (v1) = (t_arrow A B) ->
     TypedReduce v2 A e_blame ->
    step (e_app v1 v2) e_blame
 | Step_betad : forall (v1:exp) (v2:exp),
    value  ( (e_anno v1 t_dyn) )  ->
    value v2 ->
    step (e_app (e_anno v1 t_dyn) v2) (e_exp (e_app (e_anno (e_anno v1 t_dyn) (t_arrow t_dyn t_dyn)) v2))
 | Step_annov : forall (v:exp) (A:typ) (v':res),
     value v ->
     TypedReduce v A v' ->
     not (value (e_anno v A)) ->
     step (e_anno v A) v'
 | Step_addl : forall (i1:i) (i2:i),
     step (e_appv (e_addl i1)  (e_lit i2))  (e_exp (e_lit ( i1  +  i2 )))
 | Step_abeta : forall (v1:exp) (A B C D:typ) (v2:exp),
     value (e_anno v1 (t_arrow A B))  ->
     walue v2 ->
     step (e_appv (e_anno (e_anno v1 (t_arrow A B)) (t_arrow C D))  v2) (e_exp (e_anno (e_app (e_anno v1 (t_arrow A B)) v2) D))
 | Step_equal : forall (v1:exp) (A B:typ) (v2 v2':exp),
     value v1  ->
     value v2 ->
     principal_type (v1) = (t_arrow A B) ->
     TypedReduce v2 A (e_exp v2') ->
     step (e_app v1 v2) (e_exp (e_appv v1 v2'))
 | Step_add : forall (i1:i),
     step (e_appv (e_add)  (e_lit i1))  (e_exp (e_addl i1 )).


Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (e_exp e)

  | step_n e t' e':   
    step e (e_exp e') ->
    steps e' (e_exp t') ->
    steps e  (e_exp t')

  | step_nb e e':
    step e (e_exp e') ->
    steps e' e_blame ->
    steps e  e_blame

  | step_b e:
    step e (e_blame) ->
    steps e (e_blame).


(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    (* defn tpre *)
 | tp_i : 
     tpre t_int t_int
 | tp_dyn : forall (A:typ),
     tpre A t_dyn
 | tp_abs : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_arrow A B) (t_arrow C D).

(* defns expression precision *)
Inductive epre : exp -> exp -> Prop :=    (* defn epre *)
 | ep_var : forall (x:var),
    epre (e_var_f x) (e_var_f x)
 | ep_i i:
    epre (e_lit i) (e_lit i)  
 | ep_abs : forall (e1 e2:exp) (L:vars) A1 B1 A2 B2,
     ( forall x , x \notin  L  -> 
      epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
      tpre (t_arrow A1 B1) (t_arrow A2 B2) ->
     epre (e_anno (e_abs e1) (t_arrow A1 B1)) (e_anno (e_abs e2) (t_arrow A2 B2))
 | ep_app : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_annor : forall (A:typ) (e1 e2:exp) B1 B2,
   Typing nil e1 Inf B1 ->
   Typing nil e2 Inf B2 ->
   epre e1 e2 ->
   tpre B1 A ->
   tpre B1 B2 ->
   epre e1 (e_anno e2 A)
 | ep_annol : forall (A:typ) (e1 e2:exp) B1 B2,
   Typing nil e1 Inf B1 ->
   Typing nil e2 Inf B2 ->
   epre e1 e2 ->
   tpre A B2 ->
   tpre B1 B2 ->
   epre (e_anno e1 A) e2.

(** infrastructure *)
Hint Constructors pattern epre tpre Ground walue value sim TypedReduce step steps wellformed Typing ttyping lc_exp : core.

