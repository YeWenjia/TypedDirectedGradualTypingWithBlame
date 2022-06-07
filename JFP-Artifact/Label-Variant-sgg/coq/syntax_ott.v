Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition i : Set := nat.
Definition b : Set := bool.
Parameter ignore : atom.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_dyn : typ (*r dynamic type *).

Inductive typs : Set :=  
 | t_typs : typ -> var -> bool -> typs.

 Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp) (*r abstractions *)
 | e_app (e1:exp) (l:var) (b:bool) (e2:exp) (*r applications *)
 | e_add (e1:exp)  (l1:var) (b1:bool) (e2:exp) (l2:var) (b2:bool) (*r additions *)
 | e_anno (e:exp)  (l:var) (b:bool) (A:typ) (*r annotation *).

 Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

 Definition ctx : Set := list ( atom * typ ).

 Definition lts : Set := list typs.
 

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
    | (e_abs e ) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e) 
    | (e_app e1 l b e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) l b (open_exp_wrt_exp_rec k e_5 e2)
    | (e_anno e l b A) => e_anno (open_exp_wrt_exp_rec k e_5 e) l b A
    | (e_add e1 l1 b1 e2 l2 b2) => e_add (open_exp_wrt_exp_rec k e_5 e1) l1 b1 (open_exp_wrt_exp_rec k e_5 e2) l2 b2
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
 | lc_e_app : forall (e1 e2:exp) l b ,
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 l b e2))
 | lc_e_anno : forall (e:exp) (A:typ) l b,
     (lc_exp e) ->
     (lc_exp (e_anno e l b A))
 | lc_e_add : forall (e1 e2:exp) l1 b1 l2 b2,
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_add e1 l1 b1 e2 l2 b2)).


(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 l b e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e l b A) => (fv_exp e)
  | (e_add e1 l1 b1 e2 l2 b2) => (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 l b e2) => e_app (subst_exp e_5 x5 e1) l b (subst_exp e_5 x5 e2)
  | (e_anno e l b A) => e_anno (subst_exp e_5 x5 e) l b A
  | (e_add e1 l1 b1 e2 l2 b2) => e_add (subst_exp e_5 x5 e1) l1 b1 (subst_exp e_5 x5 e2) l2 b2
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_anno e l b A) => A
  | (e_abs e) => (t_arrow t_dyn t_dyn)
  | _ => t_dyn
  end.

Fixpoint trans (e:exp) : exp :=
    match e with
    | (e_var_b nat) => e_var_b nat
    | (e_var_f x) => (e_var_f x)
    | (e_lit i5) => e_lit i5
    | (e_abs e) => e_abs (trans (e))
    | (e_anno e l b A) => e_anno (trans e) l b A
    (* | (e_save e l b A B) => e_anno (e_anno (trans e) l b (t_arrow t_dyn t_dyn)) l b (t_arrow A B) *)
    | (e_app e1 l b e2) => e_app (trans e1) l b (trans e2)
    | (e_add e1 l1 b1 e2 l2 b2) => e_add (trans e1) l1 b1 (trans e2) l2 b2
    end.

    
Inductive sval : exp -> Prop :=    (* defn fval *)
 | sval_abs : forall (A:typ) (e:exp) (B:typ) l b,
     lc_exp (e_abs e) ->
     sval  (e_anno (e_abs e ) l b (t_arrow A B)).

(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_lit : forall (i5:i) l b A,
     value (e_anno (e_lit i5) l b A)
 | value_abs : forall (A:typ) (e:exp) (B C:typ) l1 b1 l2 b2 ,
     lc_exp (e_abs e) ->
     value (e_anno  (e_anno (e_abs e) l1 b1 (t_arrow A B)) l2 b2 C).

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
     sim A C ->
     sim B D ->
     sim (t_arrow A B) (t_arrow C D)
 | S_dynl : forall (A:typ),
     sim t_dyn A
 | S_dynr : forall (A:typ),
     sim A t_dyn.


Inductive nlam : exp -> Prop :=   
 | nl_var_f : forall (x:var),
     nlam (e_var_f x)
 | nl_lit : forall (i5:i),
     nlam (e_lit i5)
 | nl_app : forall (e1 e2:exp) l b ,
     nlam (e_app e1 l b e2)
 | nl_anno : forall (e:exp) (A:typ) l b ,
     nlam (e_anno e l b A)
 | nl_add : forall (e1 e2:exp) l1 b1 l2 b2,
     nlam (e_add e1 l1 b1 e2 l2 b2).


Inductive pattern : typ -> typ -> Prop :=    
 | pa_fun : forall A1 A2,
    pattern (t_arrow A1 A2) (t_arrow A1 A2)
 | pa_dyn : 
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
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (A1 A2:typ),
     ( forall x , x \notin  L  -> Typing  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A2 )  ->
     pattern A (t_arrow A1 A2) ->
    Typing G (e_abs e) Chk A
 | Typ_sugar : forall (L:vars) (G:ctx) (e:exp),
     ( forall x , x \notin  L  -> Typing  (cons ( x , t_dyn )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk t_dyn )  ->
    Typing G (e_abs e) Inf (t_arrow t_dyn t_dyn)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A A1 A2:typ) l b,
     Typing G e1 Inf A ->
     pattern A (t_arrow A1 A2) ->
     Typing G e2 Chk A1 ->
     Typing G (e_app e1 l b e2) Inf A2
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ) l b ,
     Typing G e Chk A ->
     Typing G  ( (e_anno e l b A) )  Inf A
 | Typ_add : forall (G:ctx) (e1 e2:exp) l1 b1 l2 b2,
     Typing G e1 Chk t_int ->
     Typing G e2 Chk t_int ->
     Typing G (e_add e1 l1 b1 e2 l2 b2) Inf t_int
 | Typ_save : forall (G:ctx) (e:exp) (A B C:typ) l b,
      uniq  G  ->
     sval e ->
     Typing  nil  e Inf C ->
      not (  sim C (t_arrow A B) )  ->
     Typing G  ( (e_anno e l b (t_arrow A B)) )  Inf (t_arrow A B)
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     nlam e ->
     Typing G e Chk B.


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
 | gtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ) l b,
     gtyping G e1 Inf (t_arrow A B) ->
     gtyping G e2 Chk A ->
     gtyping G (e_app e1 l b e2) Inf B
 | gtyp_anno : forall (G:ctx) (e:exp) (A:typ) l b,
     gtyping G e Chk A ->
     gtyping G  ( (e_anno e l b A) )  Inf A
 | gtyp_sim : forall (G:ctx) (e:exp) (B A:typ),
     gtyping G e Inf A ->
     sim A B ->
     nlam e ->
     gtyping G e Chk B.


Inductive simpl_item : Type :=
     | sappCtxL : exp -> var -> bool -> simpl_item
     | sappCtxR : exp -> var -> bool -> simpl_item
     | saddCtxL : var -> bool -> exp -> var -> bool -> simpl_item
     | saddCtxR : var -> bool -> exp -> var -> bool -> simpl_item.

   
Inductive ctx_item : Type :=
     | appCtxL : exp -> var -> bool -> ctx_item
     | appCtxR : exp -> var -> bool -> ctx_item
     | annoCtx : var -> bool -> typ -> ctx_item.
   

Inductive simpl_wf : simpl_item -> Prop :=
     | swf_appl : forall (e : exp) l b,
                     lc_exp e ->
                    simpl_wf (sappCtxL e l b)
     | swf_appr : forall (v : exp) l b,
                    walue v ->
                    simpl_wf (sappCtxR v l b)
     | swf_addl : forall (e : exp) l1 b1 l2 b2,
                     lc_exp e ->
                    simpl_wf (saddCtxL l1 b1 e l2 b2)
     | swf_addr : forall (v : exp) l1 b1 l2 b2,
                    value v ->
                    simpl_wf (saddCtxR l1 b1 v l2 b2).

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
 | gvalue_fanno : forall (v:exp) (A B C D:typ) l b,
     gvalue v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     gvalue (e_anno v l b (t_arrow A B))
 | gvalue_dyn : forall (v:exp) l b,
     Ground   (principal_type  v )   ->
     gvalue v ->
     gvalue  ( (e_anno v l b t_dyn) ) .

Inductive gwalue : exp -> Prop :=    
    | gwalue_val : forall v,
        gvalue v ->
        gwalue v
    | gwalue_abs : forall e ,
        lc_exp (e_abs e) ->
        gwalue (e_abs e).

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp) l b,
                    lc_exp e ->
                    wellformed (appCtxL e l b)
     | wf_appCtxR : forall (v : exp) l b,
                    gvalue v ->
                    wellformed (appCtxR v l b)
     | wf_annoCtx : forall (A : typ) l b,
                    wellformed (annoCtx l b A).

Definition simpl_fill (EE : simpl_item) (e : exp) : exp :=
     match EE with
     | sappCtxL e2 l b => e_app e l b e2
     | sappCtxR v1 l b => e_app v1 l b e
     | saddCtxL l1 b1 e2 l2 b2 => e_add e l1 b1 e2 l2 b2
     | saddCtxR l1 b1 v1 l2 b2 => e_add v1 l1 b1 e l2 b2
     end.

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 l b => e_app e l b e2
     | appCtxR v1 l b => e_app v1 l b e
     | annoCtx l b A => e_anno e l b A
     end.

Inductive res : Type :=
     | Expr  : exp -> res
     | Blame :  var -> bool -> res.


Inductive ssval : exp -> Prop :=    (* defn fval *)
 | ssval_abs : forall (e:exp) A B l b,
     lc_exp (e_abs e) ->
     ssval  (e_anno (e_abs e) l b (t_arrow A B))
 | ssval_lit : forall (i5:i),
     ssval (e_lit i5).



(* defns Semantics *)
Inductive TypedReduce : exp -> var -> bool -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | TReduce_sim : forall (e:exp) (A:typ) (B:typ) l1 b1 l2 b2,
     lc_exp e ->
     ssval e ->
     sim (principal_type e) B ->
     TypedReduce  ( (e_anno e l1 b1 A) ) l2 b2 B  (Expr (e_anno e l2 b2 B) )
 | TReduce_i : forall (A:typ) (B:typ) i l0 b0 l b,
      not (  sim t_int B  )  ->
     TypedReduce  ( (e_anno (e_lit i) l0 b0 A) ) l b B  (Blame l b)
 | TReduce_save : forall e A1 A2 l0 b0 (A C D:typ) l1 b1 l2 b2,
     TypedReduce  ( (e_anno (e_anno (e_abs e) l0 b0 (t_arrow A1 A2)) l1 b1 A) ) l2 b2 (t_arrow C D) (Expr (e_anno (e_anno (e_abs e) l0 b0 (t_arrow A1 A2)) l2 b2 (t_arrow C D) ))
 | TReduce_p : forall (e:exp) (A B C:typ) l1 b1 l2 b2 l3 b3,
     TypedReduce  (e_anno (e_anno (e_abs e) l1 b1 (t_arrow A B)) l2 b2 C)  l3 b3 t_int (Blame l3 b3).


Inductive TypeLists : exp -> lts -> res -> Prop :=    (* defn TypeLists *)
 | TLists_base : forall (v v':exp) (A:typ) l b,
     lc_exp v ->
     TypedReduce v l b A (Expr v') ->
     TypeLists  v (cons (t_typs A l b) nil)  (Expr v')
 | TLists_baseb : forall (A:typ) (v:exp) l b,
     lc_exp v ->
     TypedReduce v l b A (Blame l b) ->
     TypeLists  v (cons (t_typs A l b) nil) (Blame l b)
 | TLists_cons : forall (A:typ) B v1 v2 r l b,
     lc_exp v1 ->
     TypedReduce v1 l b A (Expr v2) ->
     TypeLists  v2 B r ->
     TypeLists  v1 (cons (t_typs A l b) B) r 
 (* | TLists_abs : forall C B t1 t2 r e l1 b1 l2 b2 l3 b3,
     TypedReduce (e_anno (e_anno (e_abs e) l1 b1 (t_arrow t1 t2)) l2 b2 B) l3 b3 C r ->
     TypeLists  (e_abs e) (cons (t_typs (t_arrow t1 t2) l1 b1) (cons (t_typs B l2 b2) (cons (t_typs C l3 b3) nil))) r  *)
 | TLists_consb : forall (A:typ) B v1 l b,
     lc_exp v1 ->
     TypedReduce v1 l b A (Blame l b) ->
     TypeLists  v1 (cons (t_typs A l b) B) (Blame l b). 


Inductive gTypedReduce : exp -> var -> bool -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | gTReduce_abs: forall v A B C D l b,
   sim (t_arrow C D) (t_arrow A B) ->
   principal_type v = (t_arrow C D) ->
   gTypedReduce v l b (t_arrow A B) (Expr (e_anno v l b (t_arrow A B)))
  | gTReduce_v : forall (v:exp) l b,
   Ground(principal_type v) ->
   gTypedReduce v l b t_dyn (Expr (e_anno v l b t_dyn))
 | gTReduce_lit : forall (i5:i) l b,
     gTypedReduce (e_lit i5) l b t_int (Expr (e_lit i5))
 | gTReduce_dd : forall (v:exp) l1 b1 l2 b2,
     lc_exp v ->
     gTypedReduce  ( (e_anno v l1 b1 t_dyn) ) l2 b2 t_dyn  (Expr  (e_anno v l1 b1 t_dyn) ) 
 | gTReduce_anyd : forall (v:exp) l b,
      FLike (principal_type  v )  ->
     gTypedReduce v l b t_dyn  (Expr (e_anno  ( (e_anno v l b (t_arrow t_dyn t_dyn)) ) l b t_dyn) ) 
 | gTReduce_dyna : forall (v:exp) (A:typ) l1 b1 l2 b2,
      FLike A ->
     sim (principal_type v) A ->
    gTypedReduce  ( (e_anno v l1 b1 t_dyn) ) l2 b2 A  (Expr (e_anno v l2 b2 A) ) 
 | gTReduce_vany : forall (v:exp) l1 b1 l2 b2,
   gTypedReduce (e_anno v l1 b1 t_dyn) l2 b2 (principal_type  v) (Expr v)
 | gTReduce_blame : forall (v:exp) (A:typ) l1 b1 l2 b2,
      not (sim A (principal_type  v ))  ->
     gTypedReduce (e_anno v l1 b1 t_dyn) l2 b2 A (Blame l2 b2).


Inductive gTypeLists : exp -> lts -> res -> Prop :=    (* defn TypeLists *)
 | gTLists_base : forall (v v':exp) (A:typ) l b,
     lc_exp v ->
     gTypedReduce v l b A (Expr v') ->
     gTypeLists  v (cons (t_typs A l b) nil)  (Expr v')
 | gTLists_baseb : forall (A:typ) (v:exp) l b,
     lc_exp v ->
     gTypedReduce v l b A (Blame l b) ->
     gTypeLists  v (cons (t_typs A l b) nil) (Blame l b)
 | gTLists_cons : forall (A:typ) B v1 v2 r l b,
     lc_exp v1 ->
     gTypedReduce v1 l b A (Expr v2) ->
     gTypeLists  v2 B r ->
     gTypeLists  v1 (cons (t_typs A l b) B) r 
 | gTLists_consb : forall (A:typ) B v1 l b,
     lc_exp v1 ->
     gTypedReduce v1 l b A (Blame l b) ->
     gTypeLists  v1 (cons (t_typs A l b) B) (Blame l b).  


Inductive step : exp -> res -> Prop :=
  | Step_absd : forall(e:exp) l b,
      lc_exp (e_abs e) ->
      step (e_anno (e_abs e) l b t_dyn) (Expr (e_anno (e_anno (e_abs e) l b (t_arrow t_dyn t_dyn)) l b t_dyn))
   | Step_abs : forall (A:typ) (e:exp) (B:typ) l b,
      lc_exp (e_abs e) ->
      step (e_anno (e_abs e) l b (t_arrow A B)) (Expr (e_anno (e_anno (e_abs e) l b (t_arrow A B)) l b (t_arrow A B)))
   | Step_i : forall (i5:i),
      step (e_lit i5) (Expr (e_anno (e_lit i5) ignore true t_int))
   | do_step E e1 e2 :
     simpl_wf E ->
     step e1 ( Expr e2 ) ->
     step (simpl_fill E e1) (Expr (simpl_fill E e2))
   | blame_step E e1 l b:
     simpl_wf E ->
     step e1 (Blame l b) ->
     step (simpl_fill E e1) (Blame l b)
   | Step_anno : forall (e e':exp ) (A: typ) l b,
     step e (Expr e') ->
     not (value (e_anno e l b A)) -> 
     step (e_anno e l b A) (Expr (e_anno e' l b A))
   | Step_annob : forall (e:exp ) (A: typ) l b l1 b1,
     step e (Blame l1 b1) ->
     not (value (e_anno e l b A)) -> 
     step (e_anno e l b A) (Blame l1 b1)
   | Step_absr : forall (e:exp) w A B l b,
     lc_exp (e_abs e) ->
     principal_type w = (t_arrow A B) ->
     walue w ->
     step (e_app w l b (e_abs e))  (Expr (e_app w l b (e_anno (e_abs e) l (negb b) A)))
   | Step_nbeta : forall (e:exp) (v v': exp) l b,
     lc_exp (e_abs e) ->
     value v ->
     TypedReduce v l b t_dyn (Expr v') ->
     step (e_app (e_abs e) l b v)  (Expr (e_anno (open_exp_wrt_exp  e v' ) ignore true t_dyn) )
   | Step_beta : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v: exp) l1 b1 l2 b2 l3 b3 v',
     lc_exp (e_abs e) ->
     value v ->
     TypeLists v (cons (t_typs A2 l3 (negb b3)) ((cons (t_typs A1 l2 (negb b2)) nil))) (Expr v') ->
     step (e_app (e_anno (e_anno (e_abs e) l1 b1 (t_arrow A1 B1)) l2 b2 (t_arrow A2 B2)) l3 b3 v)  (Expr (e_anno (e_anno (e_anno (open_exp_wrt_exp  e v' ) l1 b1 B1) l2 b2 t_dyn) l2 b2 B2) ) 
   | Step_dyn : forall (e:exp) (v: exp) l1 b1 l2 b2,
     walue v ->
     value (e_anno e l1 b1 t_dyn) ->
     step (e_app (e_anno e l1 b1 t_dyn) l2 b2 v)  (Expr (e_app (e_anno (e_anno e l1 b1 t_dyn) l1 b1 (t_arrow t_dyn t_dyn)) l2 b2 v))
   | Step_betap : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v: exp) l1 b1 l2 b2 l3 b3 l b,
     lc_exp (e_abs e) ->
     value v ->
     TypeLists v (cons (t_typs A2 l3 (negb b3)) ((cons (t_typs A1 l2 (negb b2)) nil))) (Blame l b) ->
     step (e_app (e_anno (e_anno (e_abs e) l1 b1 (t_arrow A1 B1)) l2 b2 (t_arrow A2 B2)) l3 b3 v)  (Blame l b) 
  | Step_annov : forall (v:exp) (A:typ) r l b,
     value v ->
     TypedReduce v l b A r ->
     step (e_anno v l b A) r
  | Step_addl : forall v1 v2 l1 b1 l2 b2,
     value v1 ->
     value v2 ->
     TypedReduce v1 l1 b1 t_int (Blame l1 b1) ->
     step (e_add v1 l1 b1 v2 l2 b2) (Blame l1 b1)
  | Step_addr : forall i5 v2 A l0 b0 l1 b1 l2 b2 ,
     value v2 ->
     TypedReduce v2 l2 b2 t_int (Blame l2 b2) ->
     step (e_add (e_anno (e_lit i5) l0 b0 A) l1 b1 v2 l2 b2) (Blame l2 b2)
  | Step_addb : forall i1 i2 A B l0 b0 l1 b1 l2 b2 l b,
     step (e_add (e_anno (e_lit i1) l0 b0 A) l1 b1 (e_anno (e_lit i2) l b B) l2 b2) (Expr (e_anno (e_lit (i1 + i2)) l b t_int)).


Inductive gstep : exp -> res -> Prop :=    (* defn step *)
  | gdo_step E e1 e2 :
       wellformed E ->
       gstep e1 (Expr e2 ) ->
      gstep (fill E e1) (Expr (fill E e2))
  | gblame_step E e1 l b:
      wellformed E ->
      gstep e1 (Blame l b) ->
      gstep (fill E e1) (Blame l b)
  | gStep_nbeta : forall (e:exp) (v v' : exp) p b,
    lc_exp (e_abs e) ->
    gvalue v ->
    gTypedReduce v p (negb b) t_dyn (Expr v') ->
    gstep (e_app (e_abs e) p b v)  (Expr (e_anno (open_exp_wrt_exp  e v' ) ignore true t_dyn) ) 
  | gStep_beta : forall (A:typ) (e:exp) (B:typ) (v v' : exp) l2 b2 l1 b1,
    lc_exp (e_abs e) ->
    gvalue v ->
    gTypedReduce v l2 (negb b2) A (Expr v') ->
    gstep (e_app (e_anno (e_abs e) l1 b1 (t_arrow A B)) l2 b2 v)  (Expr (e_anno  (  (open_exp_wrt_exp  e v' )  )  l1 b1 B) )
 | gStep_betap : forall (A:typ) (e:exp) (B:typ) v1 v2 (l2:var) b2 l1 b1,
    gvalue  ( (e_anno v1 l1 b1 (t_arrow A B)) )  ->
    gvalue v2 ->
    gTypedReduce v2 l2 (negb b2) A (Blame l2 (negb b2)) ->
    gstep (e_app (e_anno v1 l1 b1 (t_arrow A B)) l2 b2 v2)  (Blame l2 (negb b2))
 | gStep_annov : forall (v:exp) (A:typ) (v':res) (l:var) b,
     gvalue v ->
     gTypedReduce v l b A v' ->
     not (gvalue (e_anno v l b A)) -> 
     gstep (e_anno v l b A) v'
 | gStep_abeta : forall (v1:exp) (A B:typ) C D (v2 v2':exp) l0 b0 l1 b1 l2 b2 ,
     gvalue  ( (e_anno v1 l0 b0 (t_arrow C D)) )  ->
     gvalue v1 ->
     gTypedReduce v2 l2 (negb b2) A (Expr v2') ->
     gvalue v2 ->
     gstep (e_app (e_anno (e_anno v1 l0 b0 (t_arrow C D)) l1 b1 (t_arrow A B)) l2 b2 v2) (Expr (e_anno  ( (e_app (e_anno v1 l0 b0 (t_arrow C D)) l1 b1 v2') ) l1 b1 B)).

(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    (* defn sim *)
 | tp_i : 
     tpre t_int t_int
 | tp_dyn : forall (A:typ),
     tpre A t_dyn
 | tp_abs : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_arrow A B) (t_arrow C D).

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
 | ep_app : forall (e1 e2 e1' e2':exp) l1 b1 l2 b2,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 l1 b1 e2) (e_app e1' l2 b2 e2')
 | ep_add : forall (e1 e2 e1' e2':exp) l1 b1 l2 b2 l3 b3 l4 b4,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_add e1 l1 b1 e2 l2 b2) (e_add e1' l3 b3 e2' l4 b4)
 | ep_anno : forall (A B:typ) (e1 e2:exp) l1 b1 l2 b2,
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 l1 b1 A) (e_anno e2 l2 b2 B).

Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (Expr e)

  | step_n e t' e':   
    step e (Expr e') ->
    steps e' (Expr t') ->
    steps e  (Expr t')
  | step_nb e e' l b:
    step e (Expr e') ->
    steps e' (Blame l b) ->
    steps e  (Blame l b)

  | step_b e l b:
    step e (Blame l b) ->
    steps e (Blame l b).

Inductive gsteps : exp -> res -> Prop :=
  | gstep_refl e:
    gsteps e (Expr e)

  | gstep_n e t' e':   
    gstep e (Expr e') ->
    gsteps e' (Expr t') ->
    gsteps e  (Expr t')

  | gstep_nb e e' l b:
    gstep e (Expr e') ->
    gsteps e' (Blame l b) ->
    gsteps e  (Blame l b)

  | gstep_b e l b:
    gstep e (Blame l b) ->
    gsteps e (Blame l b).

(** infrastructure *)
Hint Constructors pattern ssval nlam value walue Ground gvalue gwalue sval sim TypedReduce gTypedReduce gTypeLists TypeLists wellformed simpl_wf step steps gsteps tpre epre Typing gtyping lc_exp : core.


