Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntax_ott.
Require Import syntaxb_ott.



Inductive eexp : Set :=  (*r eexpressions *)
 | ee_var_b (_:nat) (*r variables *)
 | ee_var_f (x:var) (*r variables *)
 | ee_lit (i5:i) (*r lit *)
 | ee_abs (e:eexp) (p:var) (b:bool) (*r abstractions *)
 | ee_app (e1:eexp) (p:var) (b:bool) (e2:eexp) (*r applications *)
 | ee_anno (e:eexp) (p:var) (b:bool) (A:typ) (*r annotation *)
 | ee_add : eexp (*r addition *)
 | ee_addl (i5:i) (*r addl *).


 Inductive dirflag2 : Set :=  (*r checking direction *)
 | Inf2 : dirflag2
 | Chk2 (p:var) (b:bool) (A:typ): dirflag2.


 Fixpoint open_eexp_wrt_eexp_rec (k:nat) (e_5:eexp) (e__6:eexp) {struct e__6}: eexp :=
  match e__6 with
  | (ee_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => ee_var_b nat
        | inleft (right _) => e_5
        | inright _ => ee_var_b (nat - 1)
      end
  | (ee_var_f x) => ee_var_f x
  | (ee_lit i5) => ee_lit i5
  | (ee_abs e l b) => ee_abs (open_eexp_wrt_eexp_rec (S k) e_5 e) l b
  | (ee_app e1 p b e2) => ee_app (open_eexp_wrt_eexp_rec k e_5 e1) p b (open_eexp_wrt_eexp_rec k e_5 e2)
  | (ee_anno e p b A) => ee_anno (open_eexp_wrt_eexp_rec k e_5 e) p b A
  | ee_add => ee_add 
  | (ee_addl i5) => ee_addl i5
end.

Definition open_eexp_wrt_eexp e_5 e__6 := open_eexp_wrt_eexp_rec 0 e__6 e_5.



Inductive lc_eexp : eexp -> Prop :=    (* defn lc_eexp *)
 | lc_ee_var_f : forall (x:var),
     (lc_eexp (ee_var_f x))
 | lc_ee_lit : forall (i5:i),
     (lc_eexp (ee_lit i5))
 | lc_ee_abs : forall (e:eexp) l b,
      ( forall x , lc_eexp  ( open_eexp_wrt_eexp e (ee_var_f x) )  )  ->
     (lc_eexp (ee_abs e l b))
 | lc_ee_app : forall (e1 e2:eexp) p b ,
     (lc_eexp e1) ->
     (lc_eexp e2) ->
     (lc_eexp (ee_app e1 p b e2))
 | lc_ee_anno : forall (e:eexp)  (p:var) (A:typ) b,
     (lc_eexp e) ->
     (lc_eexp (ee_anno e p b A))
 | lc_ee_add : 
     (lc_eexp ee_add)
 | lc_ee_addl : forall (i5:i),
     (lc_eexp (ee_addl i5)).

(** free variables *)
Fixpoint fv_eexp (e_5:eexp) : vars :=
  match e_5 with
  | (ee_var_b nat) => {}
  | (ee_var_f x) => {{x}}
  | (ee_lit i5) => {}
  | (ee_abs e l b) => (fv_eexp e)
  | (ee_app e1 p b e2) => (fv_eexp e1) \u (fv_eexp e2)
  | (ee_anno e p b A) => (fv_eexp e)
  | ee_add => {}
  | (ee_addl i5) => {}
end.

(** substitutions *)
Fixpoint subst_eexp (ee_5:eexp) (x5:var) (e__6:eexp) {struct e__6} : eexp :=
  match e__6 with
  | (ee_var_b nat) => ee_var_b nat
  | (ee_var_f x) => (if eq_var x x5 then ee_5 else (ee_var_f x))
  | (ee_lit i5) => ee_lit i5
  | (ee_abs e l b) => ee_abs (subst_eexp ee_5 x5 e) l b
  | (ee_app e1 p b e2) => ee_app (subst_eexp ee_5 x5 e1) p b (subst_eexp ee_5 x5 e2)
  | (ee_anno e p b A) => ee_anno (subst_eexp ee_5 x5 e) p b A
  | ee_add => ee_add 
  | (ee_addl i5) => (ee_addl i5)
end.



Fixpoint erase (e:eexp) : exp :=
  match e with
  | (ee_var_b nat) => e_var_b nat
  | (ee_var_f x) => (e_var_f x)
  | (ee_lit i5) => (e_lit i5)
  | (ee_anno e p b A) => (e_anno (erase e) A)
  | (ee_abs e l b ) => (e_abs (erase e))
  | (ee_add) => e_add
  | (ee_app e1 p b e2) => e_app (erase e1) (erase e2)
  | (ee_addl i5) => e_addl i5
  end.



Inductive nnlam : eexp -> Prop :=   
  | nnl_var_b : forall nat,
    nnlam (ee_var_b nat)
 | nnl_var_nat : forall (x:var),
     nnlam (ee_var_f x)
 | nnl_var_f : forall (x:var),
     nnlam (ee_var_f x)
 | nnl_lit : forall (i5:i),
     nnlam (ee_lit i5)
 | nnl_app : forall (e1 e2:eexp) l b ,
     nnlam (ee_app e1 l b e2)
 | nnl_anno : forall (e:eexp) (A:typ) l b ,
     nnlam (ee_anno e l b A)
 | nnl_add : 
     nnlam (ee_add)
 | nnl_addl : forall i,
     nnlam (ee_addl i).


Inductive TTyping : ctx -> eexp -> dirflag -> typ -> Prop :=    (* defn TTyping *)
 | TTyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     TTyping G (ee_lit i5) Inf t_int
 | TTyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     TTyping G (ee_var_f x) Inf A
 | TTyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:eexp) (B:typ) l b,
      ( forall x , x \notin  L  -> TTyping  (cons ( x , A )  G )   ( open_eexp_wrt_eexp e (ee_var_f x) )  Chk B )  ->
     TTyping G (ee_abs e l b ) Chk (t_arrow A B)
 | TTyp_absd : forall (L:vars) (G:ctx) (e:eexp) l b,
     ( forall x , x \notin  L  -> TTyping  (cons ( x , t_dyn )  G )   ( open_eexp_wrt_eexp e (ee_var_f x) )  Chk t_dyn )  ->
    TTyping G (ee_abs e l b ) Chk t_dyn
 | TTyp_sugar : forall (L:vars) (G:ctx) (e:eexp) l b,
    ( forall x , x \notin  L  -> TTyping  (cons ( x , t_dyn )  G )   ( open_eexp_wrt_eexp e (ee_var_f x) )  Chk t_dyn )  ->
   TTyping G (ee_abs e l b) Inf (t_arrow t_dyn t_dyn)
 | TTyp_app : forall (G:ctx) (e1 e2:eexp) (A1 A2 A:typ) l b,
     pattern A (t_arrow A1 A2) ->
     TTyping G e1 Inf A ->
     TTyping G e2 Chk A1 ->
     TTyping G (ee_app e1 l b e2) Inf A2
 | TTyp_anno : forall (G:ctx) (e:eexp) (p:var) b (A:typ),
     TTyping G e Chk A ->
     TTyping G  ( (ee_anno e p b A) )  Inf A
 | TTyp_sim : forall (G:ctx) (e:eexp) (B A:typ),
     TTyping G e Inf A ->
     sim A B ->
     nnlam e ->
     TTyping G e Chk B
 | TTyp_add : forall (G:ctx),
     uniq  G  ->
     TTyping G ee_add Inf (t_arrow t_int  (t_arrow t_int t_int) )
 | TTyp_addl : forall (G:ctx) (i1:i),
     uniq  G  ->
     TTyping G (ee_addl i1) Inf (t_arrow t_int t_int).

Inductive rres : Type :=
     | ee_exp  : eexp -> rres
     | ee_blame : var -> bool -> rres.  

Fixpoint eraser (r:rres) : res :=
  match r with
  | (ee_exp e) => e_exp (erase e)
  | ee_blame l b => e_blame
  end.

Inductive cctx_item : Type :=
     | eappCtxL : eexp -> var -> bool -> cctx_item
     | eappCtxR : eexp -> var -> bool -> cctx_item
     | eannoCtx : var -> bool -> typ -> cctx_item.

Fixpoint pprincipal_type (v:eexp) : typ :=
  match v with
  | (ee_lit i5) => t_int
  | (ee_anno e p b A) => A
  | (ee_abs e l b ) => (t_arrow t_dyn t_dyn)
  | (ee_add) => (t_arrow t_int (t_arrow t_int t_int))
  | (ee_addl i5) => (t_arrow t_int t_int)
  | _ => t_dyn
  end.

(* defns Values *)
Inductive evalue : eexp -> Prop :=    (* defn value *)
 | evalue_lit : forall (i5:i),
     evalue (ee_lit i5)
 | evalue_abs : forall e l b,
     lc_eexp (ee_abs e l b) ->
     evalue (ee_abs e l b)
 | evalue_fanno : forall (v:eexp) (A B C D:typ) (p:var) b,
     evalue v ->
      (t_arrow C D)  =   (pprincipal_type   ( v )  )   ->
     evalue (ee_anno v p b (t_arrow A B))
 | evalue_dyn : forall (v:eexp) (p:var) b,
     Ground   (pprincipal_type  v )   ->
     evalue v ->
     evalue  ( (ee_anno v p b t_dyn) )
 | evalue_add : 
     evalue ee_add
 | evalue_addl : forall (i5:i),
     evalue  ( (ee_addl i5) ).

   
Inductive wwellformed : cctx_item -> Prop :=
     | wwf_appCtxL : forall (e : eexp) p b,
                   lc_eexp e ->
                    wwellformed (eappCtxL e p b )
     | wf_appCtxR : forall (v : eexp) p b A B,
                    pprincipal_type v = (t_arrow A B) ->
                    evalue v ->
                    wwellformed (eappCtxR v p b)
     | wf_annoCtx : forall (A : typ)  (p:var) b,
                    wwellformed (eannoCtx p b A).
   
Definition ffill (E : cctx_item) (e : eexp) : eexp :=
     match E with
     | eappCtxL e2 p b  => ee_app e p b e2
     | eappCtxR v1 p b => ee_app v1 p b e
     | eannoCtx p b A => ee_anno e p b A
     end.


Inductive TTypedReduce : eexp -> var -> bool -> typ -> rres -> Prop :=    (* defn TTypedReduce *)
 | TTReduce_abs: forall v A B C D p b,
   sim (t_arrow C D) (t_arrow A B) ->
   pprincipal_type v = (t_arrow C D) ->
   TTypedReduce v p b (t_arrow A B) (ee_exp (ee_anno v p b (t_arrow A B)))
  | TTReduce_v : forall (v:eexp)  (p:var) b,
   Ground(pprincipal_type v) ->
   TTypedReduce v p b t_dyn (ee_exp (ee_anno v p b t_dyn))
 | TTReduce_lit : forall (i5:i) b (p:var),
     TTypedReduce (ee_lit i5) p b t_int (ee_exp (ee_lit i5))
 | TTReduce_dd : forall (v:eexp) (p:var) (q:var) b1 b2,
     lc_eexp v ->
     TTypedReduce  ( (ee_anno v q b1 t_dyn) ) p b2 t_dyn  (ee_exp  (ee_anno v q b1 t_dyn) ) 
 | TTReduce_anyd : forall (v:eexp) (p:var) b,
      FLike (pprincipal_type  v )  ->
     TTypedReduce v p b t_dyn  (ee_exp (ee_anno  ( (ee_anno v p b (t_arrow t_dyn t_dyn)) ) p b t_dyn) ) 
 | TTReduce_adyn : forall e (A:typ) l1 b1 l2 b2 l0 b0,
     FLike A ->
     TTypedReduce  ( (ee_anno (ee_abs e l0 b0) l1 b1 t_dyn) ) l2 b2 A  (ee_exp (ee_anno (ee_anno (ee_abs e l0 b0) l1 b1 (t_arrow t_dyn t_dyn)) l2 b2 A))
 | TTReduce_absd : forall e l1 b1 l2 b2 l0 b0,
     TTypedReduce  ( (ee_anno (ee_abs e l0 b0) l1 b1 t_dyn) )  l2 b2 (t_arrow t_dyn t_dyn)  (ee_exp (ee_anno (ee_abs e l0 b0) l1 b1 (t_arrow t_dyn t_dyn)))
 | TTReduce_dyna : forall (v:eexp) (A:typ) (p:var) b1 b2 (q:var),
      FLike A ->
     sim (pprincipal_type v) A ->
     nnlam v ->
    TTypedReduce  ( (ee_anno v q b1 t_dyn) ) p b2 A  (ee_exp (ee_anno v p b2 A) ) 
 | TTReduce_vany : forall (v:eexp) (p:var)  (q:var) b1 b2,
    nnlam v ->
   TTypedReduce (ee_anno v q b1 t_dyn) p b2 (pprincipal_type  v) (ee_exp v)
 | TTReduce_blame : forall (v:eexp) (A:typ) (p:var) b1 b2 (q:var),
      not (sim A (pprincipal_type  v ))  ->
     TTypedReduce (ee_anno v q b1 t_dyn) p b2 A (ee_blame p b2).


Inductive waluee : eexp -> Prop :=    (* defn value *)
 | waluee_lit : forall (i5:i),
     waluee (ee_lit i5)
 | waluee_absd : forall e l b l0 b0,
     lc_eexp (ee_abs e l0 b0) ->
     waluee (ee_anno (ee_abs e l0 b0) l b t_dyn)
 | walueee_absa : forall e l b t1 t2 l0 b0,
     lc_eexp (ee_abs e l0 b0) ->
     waluee (ee_anno (ee_abs e l0 b0) l b (t_arrow t1 t2))
 | walueee_fanno : forall (v:eexp) (A B C D:typ) l b,
     waluee v ->
      (t_arrow C D)  =   (pprincipal_type   ( v )  )   ->
     waluee (ee_anno v l b (t_arrow A B))
 | walueee_dyn : forall (v:eexp) l b,
     Ground   (pprincipal_type  v )   ->
     waluee v ->
     waluee  ( (ee_anno v l b t_dyn) )
 | walueee_add : 
     waluee ee_add
 | walueee_addl : forall (i5:i),
     waluee  ( (ee_addl i5) ) .


Inductive sstep : eexp -> rres -> Prop :=    (* defn step *)
  | sdo_step E e1 e2 : 
       wwellformed E ->
       sstep e1 (ee_exp e2 ) ->
      sstep (ffill E e1) (ee_exp (ffill E e2))
  | sblame_step E e1 l b:
      wwellformed E ->
      sstep e1 (ee_blame l b) ->
      sstep (ffill E e1) (ee_blame l b)
 | sStep_beta : forall (A:typ) (e:eexp) (B:typ) (v : eexp) l1 b1 l2 b2 v' l0 b0,
    lc_eexp (ee_abs e l0 b0) ->
    evalue v ->
    TTypedReduce v l2 b2 A (ee_exp v') ->
    sstep (ee_app (ee_anno (ee_abs e l0 b0) l1 b1 (t_arrow A B)) l2 b2 v)  (ee_exp (ee_anno  (  (open_eexp_wrt_eexp  e v' )  )  l1 b1 B) )
 | sStep_betap : forall (A:typ) (e:eexp) (B:typ) v1 v2  l b l1 b1,
    evalue  ( (ee_anno v1 l b (t_arrow A B)) )  ->
    evalue v2 ->
    pprincipal_type (v1) = (t_arrow A B) ->
    TTypedReduce v2 l1 b1 A (ee_blame l1 b1) ->
    sstep (ee_app (ee_anno v1 l b (t_arrow A B)) l1 b1 v2)  (ee_blame l1 b1)
 | sStep_annov : forall (v:eexp) (A:typ) (v':rres) (l:var) b,
     evalue v ->
     TTypedReduce v l b A v' ->
     not (evalue (ee_anno v l b A)) -> 
     sstep (ee_anno v l b A) v'
 | sStep_abeta : forall (v1:eexp) (A B:typ) (v2 :eexp) l1 b1 C D v2' l b l0 b0,
     evalue  ( (ee_anno v1 l0 b0 (t_arrow C D)) )  ->
     evalue v1 ->
     evalue v2 ->     
     TTypedReduce v2 l b A (ee_exp v2') ->
     sstep (ee_app (ee_anno (ee_anno v1 l0 b0 (t_arrow C D)) l1 b1 (t_arrow A B)) l b v2) (ee_exp (ee_anno (ee_app (ee_anno v1 l0 b0 (t_arrow C D)) l1 (negb b1) v2' ) l1 b1 B))
 | sStep_betad : forall (v1:eexp) (v2:eexp) l1 b1 l2 b2 ,
    evalue  ( (ee_anno v1 l1 b1 t_dyn) )  ->
    lc_eexp v2 ->
    sstep (ee_app (ee_anno v1 l1 b1 t_dyn) l2 b2 v2) (ee_exp (ee_app (ee_anno (ee_anno v1 l1 b1 t_dyn) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 v2))
 | sStep_nbeta : forall (e:eexp) (v : eexp) l b v' l0 b0,
    lc_eexp (ee_abs e l0 b0) ->
    evalue v ->
    TTypedReduce v l b t_dyn (ee_exp v') ->
    sstep (ee_app (ee_abs e l0 b0) l b v)  (ee_exp (ee_anno (open_eexp_wrt_eexp  e v') l0 b0 t_dyn) ).

Hint Constructors sstep nnlam wwellformed evalue TTyping lc_eexp TTypedReduce waluee: core.