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
 | e_add (e1:exp) (e2:exp) (*r additions *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_pro (e1:exp) (e2:exp)
 | e_l (e:exp) 
 | e_r (e:exp).

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
    | (e_add e1 e2) => e_add (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_pro e1 e2) => e_pro (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_l e) => e_l (open_exp_wrt_exp_rec k e_5 e)
    | (e_r e) => e_r (open_exp_wrt_exp_rec k e_5 e)
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
 | lc_e_add : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_add e1 e2))
 | lc_e_pro : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_pro e1 e2))
 | lc_e_l : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_l e))
 | lc_e_r : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_r e)).

Inductive nlam : exp -> Prop :=   
 | nl_var_f : forall (x:var),
     nlam (e_var_f x)
 | nl_lit : forall (i5:i),
     nlam (e_lit i5)
 | nl_app : forall (e1 e2:exp),
     nlam (e_app e1 e2)
 | nl_anno : forall (e:exp) (A:typ),
     nlam (e_anno e A)
 | nl_add : forall (e1 e2:exp),
     nlam (e_add e1 e2)
 | nl_pro : forall (e1 e2:exp),
     nlam (e_pro e1 e2)
 | nl_l : forall (e:exp),
     nlam (e_l e)
 | nl_r : forall (e:exp),
     nlam (e_r e).


(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | (e_add e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_pro e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_l e) => (fv_exp e)
  | (e_r e) => (fv_exp e)
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
  | (e_add e1 e2) => e_add (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_pro e1 e2) => e_pro (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_l e) => e_l (subst_exp e_5 x5 e)
  | (e_r e) => e_r (subst_exp e_5 x5 e)
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_anno e A) => A
  | (e_abs e) => (t_arrow t_dyn t_dyn)
  | (e_pro v1 v2) => t_pro (principal_type v1) (principal_type v2)
  | _ => t_dyn
  end.

(* Fixpoint trans (e:exp) : exp :=
    match e with
    | (e_var_b nat) => e_var_b nat
    | (e_var_f x) => (e_var_f x)
    | (e_lit i5) => e_lit i5
    | (e_abs e) => e_abs (trans (e))
    | (e_anno e1 A) => (e_anno (trans e1) A)
    | (e_app e1 e2) => e_app (trans e1) (trans e2)
    | (e_add e1 e2) => e_add (trans e1) (trans e2)
    end. *)

    
Inductive sval : exp -> Prop :=    (* defn fval *)
 | sval_abs : forall (e:exp) A B,
     lc_exp (e_abs e) ->
     sval  (e_anno (e_abs e) (t_arrow A B)).


Inductive ssval : exp -> Prop :=    (* defn fval *)
 | ssval_abs : forall (e:exp) A B,
     lc_exp (e_abs e) ->
     ssval  (e_anno (e_abs e) (t_arrow A B))
 | ssval_lit : forall (i5:i),
     ssval (e_lit i5) 
 | ssval_pro : forall s1 s2,
     ssval s1 ->
     ssval s2 ->
     ssval  (e_pro s1 s2).


Inductive ssvalue : exp -> Prop :=   
  | ssvalue_abs : forall (e:exp) A B,
     lc_exp (e_abs e) ->
     ssvalue  (e_anno (e_abs e) (t_arrow A B))
 | ssvalue_lit : forall (i5:i),
     ssvalue (e_lit i5) 
 | ssvalue_absd : forall (e:exp),
     lc_exp (e_abs e) ->
     ssvalue  (e_anno (e_abs e) t_dyn)
 | ssvalue_pro : forall s1 s2,
     ssvalue s1 ->
     ssvalue s2 ->
     ssvalue  (e_pro s1 s2)
.

(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_pro : forall s A,
    ssval s ->
    value (e_anno s A).

Inductive walue : exp -> Prop :=    
 | walue_val : forall v,
     value v ->
     walue v
 | walue_abs : forall e ,
     lc_exp (e_abs e) ->
     walue (e_abs e).


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


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A2 )  ->
      pattern A (t_arrow A1 A2) ->
     Typing G (e_abs e) Chk A
 | Typ_sugar : forall (L:vars) (G:ctx) (e:exp),
     ( forall x , x \notin  L  -> Typing  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn )  ->
    Typing G (e_abs e) Inf (t_arrow t_dyn t_dyn)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A A1 A2:typ),
     Typing G e1 Inf A ->
     pattern A (t_arrow A1 A2) ->
     Typing G e2 Chk A1 ->
     Typing G (e_app e1 e2) Inf A2
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_add : forall (G:ctx) (e1 e2:exp),
     Typing G e1 Chk t_int ->
     Typing G e2 Chk t_int ->
     Typing G (e_add e1 e2) Inf t_int
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     nlam e ->
     Typing G e Chk B 
 | Typ_pro : forall (G:ctx) (e1 e2:exp) (A1 A2:typ),
     Typing G e1 Inf A1 ->
     Typing G e2 Inf A2 ->
     Typing G (e_pro e1 e2) Inf (t_pro A1 A2)
 | Typ_l : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G  ( (e_l e) )  Inf A1
 | Typ_r : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G  ( (e_r e) )  Inf A2.



Inductive gtyping : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | gtyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
      gtyping G (e_lit i5) Inf t_int
 | gtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      gtyping G (e_var_f x) Inf A
 | gtyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> gtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      gtyping G (e_abs e) Chk (t_arrow A B)
 | gtyp_sugar : forall (L:vars) (G:ctx) (e:exp),
      ( forall x , x \notin  L  -> gtyping  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn )  ->
     gtyping G (e_abs e) Inf (t_arrow t_dyn t_dyn)    
 | gtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     gtyping G e1 Inf (t_arrow A B) ->
     gtyping G e2 Chk A ->
     gtyping G (e_app e1 e2) Inf B
 | gtyp_anno : forall (G:ctx) (e:exp) (A:typ),
     gtyping G e Chk A ->
     gtyping G  ( (e_anno e A) )  Inf A
 | gtyp_sim : forall (G:ctx) (e:exp) (B A:typ),
     gtyping G e Inf A ->
     sim A B ->
     nlam e ->
     gtyping G e Chk B.


Inductive simpl_item : Type :=
     | sappCtxL : exp -> simpl_item
     | sappCtxR : exp -> simpl_item
     | saddCtxL : exp -> simpl_item
     | saddCtxR : exp -> simpl_item
     | sproCtxL : exp -> simpl_item
     | sproCtxR : exp -> simpl_item
     | slCtx : simpl_item
     | srCtx : simpl_item.

   
Inductive ctx_item : Type :=
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | annoCtx : typ -> ctx_item.
   

Inductive simpl_wf : simpl_item -> Prop :=
     | swf_appl : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (sappCtxL e)
     | swf_appr : forall (v : exp),
                    walue v ->
                    simpl_wf (sappCtxR v)
     | swf_addl : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (saddCtxL e)
     | swf_addr : forall (v : exp),
                    value v ->
                    simpl_wf (saddCtxR v)
     | swf_prol : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (sproCtxL e)
     | swf_pror : forall (v : exp),
                    walue v ->
                    simpl_wf (sproCtxR v)
     | swf_l : 
                    simpl_wf (slCtx)
     | swf_r : 
                    simpl_wf (srCtx).

Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)).

Inductive Ground : typ -> Prop :=    (* defn Ground *)
 | Ground_lit : 
     Ground t_int
 | Ground_dyn : 
     Ground  (t_arrow t_dyn t_dyn) .


(* defns Values *)
Inductive gvalue : exp -> Prop :=    (* defn value *)
 | gvalue_lit : forall (i5:i),
     gvalue (e_lit i5)
 | gvalue_abs : forall  (e:exp),
     lc_exp (e_abs e) ->
     gvalue (e_abs e)
 | gvalue_fanno : forall (v:exp) (A B C D:typ),
     gvalue v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     gvalue (e_anno v (t_arrow A B))
 | gvalue_dyn : forall (v:exp),
     Ground   (principal_type  v )   ->
     gvalue v ->
     gvalue  ( (e_anno v t_dyn) ).


Inductive gwalue : exp -> Prop :=    
| gwalue_val : forall v,
    gvalue v ->
    gwalue v
| gwalue_abs : forall e ,
    lc_exp (e_abs e) ->
    gwalue (e_abs e).

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    gvalue v ->
                    wellformed (appCtxR v)
     | wf_annoCtx : forall (A : typ),
                    wellformed (annoCtx A).

Definition simpl_fill (EE : simpl_item) (e : exp) : exp :=
     match EE with
     | sappCtxL e2 => e_app e e2
     | sappCtxR v1 => e_app v1 e
     | saddCtxL e2 => e_add e e2
     | saddCtxR v1 => e_add v1 e
     | sproCtxL e2 => e_pro e e2
     | sproCtxR v1 => e_pro v1 e
     | slCtx => e_l e
     | srCtx => e_r e
     end.

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | annoCtx A => e_anno e A
     end.

Inductive res : Type :=
     | Expr  : exp -> res
     | Blame :  res.

(* defns Semantics *)


Inductive TypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | TReduce_sim : forall (e:exp) (A:typ) (B:typ),
     lc_exp e ->
     ssval e ->
     sim (principal_type e) B ->
     TypedReduce  ( (e_anno e A) ) B  (Expr (e_anno e B) )
 | TReduce_simp : forall (e:exp) (A:typ) (B:typ),
     lc_exp e ->
     ssval e ->
     not(sim (principal_type e) B) ->
     TypedReduce  ( (e_anno e A) ) B  Blame.


Inductive TypeLists : exp -> list typ -> res -> Prop :=    (* defn TypeLists *)
 | TLists_base : forall (v v':exp) (A:typ),
     lc_exp v ->
     TypedReduce v A (Expr v') ->
     TypeLists  v (cons A nil)  (Expr v')
 | TLists_baseb : forall (A:typ) (v:exp),
     lc_exp v ->
     TypedReduce v A Blame ->
     TypeLists  v (cons A nil) Blame
 | TLists_cons : forall (A:typ) (B: list typ) v1 v2 r,
     lc_exp v1 ->
     TypedReduce v1 A (Expr v2) ->
     TypeLists  v2 B r ->
     TypeLists  v1 (cons A B) r 
 | TLists_consb : forall (A:typ) (B: list typ) v1,
     lc_exp v1 ->
     TypedReduce v1 A Blame ->
     TypeLists  v1 (cons A B) Blame.

Inductive gTypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | gTReduce_abs: forall v A B C D,
   sim (t_arrow C D) (t_arrow A B) ->
   principal_type v = (t_arrow C D) ->
   gTypedReduce v (t_arrow A B) (Expr (e_anno v (t_arrow A B)))
  | gTReduce_v : forall (v:exp),
   Ground(principal_type v) ->
   gTypedReduce v t_dyn (Expr (e_anno v t_dyn))
 | gTReduce_lit : forall (i5:i),
     gTypedReduce (e_lit i5) t_int (Expr (e_lit i5))
 | gTReduce_dd : forall (v:exp),
     lc_exp v ->
     gTypedReduce  ( (e_anno v t_dyn) )  t_dyn  (Expr  (e_anno v t_dyn) ) 
 | gTReduce_anyd : forall (v:exp),
      FLike (principal_type  v )  ->
     gTypedReduce v t_dyn  (Expr (e_anno  ( (e_anno v (t_arrow t_dyn t_dyn)) )  t_dyn) ) 
 | gTReduce_dyna : forall (v:exp) (A:typ),
      FLike A ->
     sim (principal_type v) A ->
    gTypedReduce  ( (e_anno v t_dyn) )  A  (Expr (e_anno v A) ) 
 | gTReduce_vany : forall (v:exp),
   gTypedReduce (e_anno v t_dyn) (principal_type  v) (Expr v)
 | gTReduce_blame : forall (v:exp) (A:typ),
      not (sim A (principal_type  v ))  ->
     gTypedReduce (e_anno v t_dyn) A Blame.


Inductive gTypeLists : exp -> list typ -> res -> Prop :=    (* defn TypeLists *)
 | gTLists_base : forall (v v':exp) (A:typ),
     lc_exp v ->
     gTypedReduce v A (Expr v') ->
     gTypeLists  v (cons A nil)  (Expr v')
 | gTLists_baseb : forall (A:typ) (v:exp),
     lc_exp v ->
     gTypedReduce v A Blame ->
     gTypeLists  v (cons A nil) Blame
 | gTLists_cons : forall (A:typ) (B: list typ) v1 v2 r,
     lc_exp v1 ->
     gTypedReduce v1 A (Expr v2) ->
     gTypeLists  v2 B r ->
     gTypeLists  v1 (cons A B) r 
 | gTLists_consb : forall (A:typ) (B: list typ) v1,
     lc_exp v1 ->
     gTypedReduce v1 A Blame ->
     gTypeLists  v1 (cons A B) Blame.


Fixpoint erase (v:exp) : exp :=
  match v with
  | (e_abs e) => (e_anno (e_abs e) (t_arrow t_dyn t_dyn))
  | (e_anno s A) => s
  | _ => v
  end.


Inductive step : exp -> res -> Prop :=
   | Step_abs : forall e A B,
      lc_exp (e_abs e) ->
      step (e_anno (e_abs e) (t_arrow A B)) (Expr (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow A B)))
   | Step_lit : forall i,
      step (e_lit i) (Expr (e_anno (e_lit i) t_int))
   | Step_absd : forall e,
      lc_exp (e_abs e) ->
      step (e_anno (e_abs e) t_dyn) (Expr (e_anno (e_anno (e_abs e) (t_arrow t_dyn t_dyn)) t_dyn))
   (* | Step_pro : forall s1 s2 A B,
      ssval s1 ->
      ssval s2 ->
      step (e_pro (e_anno s1 A) (e_anno s2 B)) (Expr (e_anno (e_pro s1 s2) (t_pro A B))) *)
   | Step_pro : forall v1 v2,
      walue v1 ->
      walue v2 ->
      step (e_pro v1 v2) (Expr (e_anno (e_pro (erase v1) (erase v2)) (t_pro (principal_type v1) (principal_type v2))))
   | do_step E e1 e2 :
    simpl_wf E ->
    step e1 ( Expr e2 ) ->
    step (simpl_fill E e1) (Expr (simpl_fill E e2))
  | blame_step E e1 :
    simpl_wf E ->
    step e1 Blame ->
    step (simpl_fill E e1) Blame
   | Step_anno : forall (e e':exp ) (A: typ),
     step e (Expr e') ->
     not (value (e_anno e A)) -> 
     step (e_anno e A) (Expr (e_anno e' A))
   | Step_annob : forall (e:exp ) (A: typ),
     step e Blame ->
     step (e_anno e A) Blame
   | Step_absr : forall (e:exp) v A1 A B,
     lc_exp (e_abs e) ->
     principal_type v = A1 ->
     pattern A1 (t_arrow A B) ->
     walue v ->
     step (e_app v (e_abs e))  (Expr (e_app v (e_anno (e_abs e) A)))
   | Step_beta : forall A (A1 A2:typ) (e:exp) (B1 B2:typ) (v v': exp),
     lc_exp (e_abs e) ->
     walue v ->
     TypeLists v (cons A2 (cons A1 nil)) (Expr v') ->
     pattern A (t_arrow A2 B2) ->
     step (e_app (e_anno (e_anno (e_abs e) (t_arrow A1 B1)) A)  v)  (Expr (e_anno (e_anno (open_exp_wrt_exp  e v' ) B1) B2) )
  | Step_dyn : forall v1 (v: exp),
     value v ->
     walue v1 ->
     TypedReduce v1 (t_arrow t_dyn t_dyn) Blame ->
     step (e_app v1 v)  Blame
   | Step_betap : forall A (A1 A2:typ) (e:exp) (B1 B2:typ) (v: exp),
     lc_exp (e_abs e) ->
     walue v ->
     TypeLists v (cons A2 (cons A1 nil)) Blame ->
     pattern A (t_arrow A2 B2) ->
     step (e_app (e_anno (e_anno (e_abs e) (t_arrow A1 B1)) A) v)  Blame
  | Step_annov : forall (v:exp) (A:typ) r,
     walue v ->
     TypedReduce v A r ->
     step (e_anno v A) r
  | Step_addl : forall v1 v2,
     walue v1 ->
     walue v2 ->
     TypedReduce v1 t_int Blame ->
     step (e_add v1 v2) Blame 
   | Step_addr : forall i5 v2 A,
     walue v2 ->
     TypedReduce v2 t_int Blame ->
     step (e_add (e_anno (e_lit i5) A) v2) Blame
  | Step_addb : forall i1 i2 A B,
     step (e_add (e_anno (e_lit i1) A) (e_anno (e_lit i2) B)) (Expr (e_anno (e_lit (i1 + i2)) t_int))
  | Step_lp : forall v,
      walue v ->
      TypedReduce v (t_pro t_dyn t_dyn) Blame ->
      step (e_l v) Blame
  | Step_l : forall s1 s2 A A1 A2,
      value (e_anno (e_pro s1 s2) A) -> 
      pattern_pro A (t_pro A1 A2) ->
      step (e_l (e_anno (e_pro s1 s2) A)) (Expr (e_anno s1 A1))
  | Step_rp : forall v,
      walue v ->
      TypedReduce v (t_pro t_dyn t_dyn) Blame ->
      step (e_r v) Blame
  | Step_r : forall s1 s2 A A1 A2,
      value (e_anno (e_pro s1 s2) A) -> 
      pattern_pro A (t_pro A1 A2) ->
      step (e_r (e_anno (e_pro s1 s2) A)) (Expr (e_anno s2 A2))
  (* | Step_al : forall e e2,
      lc_exp (e_abs e) ->
      step (e_pro (e_abs e) e2) (Expr (e_pro (e_anno (e_anno (e_abs e) (t_arrow t_dyn t_dyn)) (t_arrow t_dyn t_dyn)) e2))
  | Step_ar : forall e v1,
      lc_exp (e_abs e) ->
      value v1 ->
      step (e_pro v1 (e_abs e)) (Expr (e_pro v1 (e_anno (e_abs e) (t_arrow t_dyn t_dyn)))) *)
  | Step_nbeta : forall  (e:exp) (v v': exp),
      lc_exp (e_abs e) ->
      walue v ->
      TypedReduce v t_dyn (Expr v') ->
      step (e_app (e_abs e)  v)  (Expr (e_anno (open_exp_wrt_exp  e v' ) t_dyn) ).


Inductive gstep : exp -> res -> Prop :=    (* defn step *)
  | gdo_step E e1 e2 :
       wellformed E ->
       gstep e1 (Expr e2 ) ->
      gstep (fill E e1) (Expr (fill E e2))
  | gblame_step E e1:
      wellformed E ->
      gstep e1 Blame ->
      gstep (fill E e1) Blame
  | gStep_nbeta : forall (e:exp) (v v' : exp),
    lc_exp (e_abs e) ->
    gvalue v ->
    gTypedReduce v t_dyn (Expr v') ->
    gstep (e_app (e_abs e) v)  (Expr (e_anno (open_exp_wrt_exp  e v' ) t_dyn) ) 
 | gStep_beta : forall (A:typ) (e:exp) (B:typ) (v v' : exp),
      lc_exp (e_abs e) ->
      gvalue v ->
      gTypedReduce v A (Expr v') ->
      gstep (e_app (e_anno (e_abs e) (t_arrow A B)) v)  (Expr (e_anno (open_exp_wrt_exp  e v' ) B) )  
 | gStep_betap : forall (v1:exp) (A B:typ) (v2 v2':exp),
      gvalue  ( (e_anno v1 (t_arrow A B)) )  ->
      gTypedReduce v2 A Blame ->
      gvalue v2 ->
      gstep (e_app (e_anno v1 (t_arrow A B)) v2) Blame
 | gStep_annov : forall (v:exp) (A:typ) (v':res),
     gvalue v ->
     gTypedReduce v A v' ->
     not (gvalue (e_anno v A)) -> 
     gstep (e_anno v A) v'
 | gStep_abeta : forall (v1:exp) (A B C D:typ) (v2 v2':exp),
     gvalue (e_anno v1 (t_arrow A B))  ->
     gTypedReduce v2 C (Expr v2') ->
     gvalue v2 ->
     gstep (e_app (e_anno (e_anno v1 (t_arrow A B)) (t_arrow C D))  v2) (Expr (e_anno (e_app (e_anno v1 (t_arrow A B)) v2') D)).



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

(* defns expression precision *)
Inductive epre : exp -> exp -> Prop :=    (* defn sim *)
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
 | ep_add : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_add e1 e2) (e_add e1' e2')
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
     epre (e_r e1) (e_r e2).



Inductive steps : exp -> res -> Prop :=
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
    steps e (Blame).



(* Inductive steps : exp -> res -> Prop :=
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
    steps e (Blame). *)

Inductive gsteps : exp -> res -> Prop :=
  | gstep_refl e:
    gsteps e (Expr e)

  | gstep_n e t' e':   
    gstep e (Expr e') ->
    gsteps e' (Expr t') ->
    gsteps e  (Expr t')

  | gstep_nb e e':
    gstep e (Expr e') ->
    gsteps e' Blame ->
    gsteps e  Blame

  | gstep_b e:
    gstep e (Blame) ->
    gsteps e (Blame).

(** infrastructure *)
Hint Constructors ssvalue pattern pattern_pro ssval value nlam walue gvalue Ground gvalue gwalue sval sim TypedReduce gTypedReduce 
TypeLists gTypeLists wellformed simpl_wf step gstep steps gsteps tpre epre Typing gtyping lc_exp : core.


