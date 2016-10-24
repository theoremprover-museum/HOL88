% mk_Pterm1.ml

  Theory of HOL-proofs: Pterms
%

new_theory  `Pterm`;;
%
load_library `finite_sets`;;
load_library `more_lists`;;
new_parent `Type`;;
load_library `string`;;
load_library `taut`;;
loadf `defs/defs`;;
%

% --- The terms --- %

let Pterm = define_type `Pterm`
  `Pterm = Const string Type
        | Var string#Type
        | App Pterm Pterm
        | Lam string#Type Pterm`;;
let Pterm_induct =
 save_thm(`Pterm_induct`,prove_induction_thm Pterm);;
let Pterm_distinct =
 save_thm(`Pterm_distinct`,prove_constructors_distinct Pterm);;
let Pterm_11 =
 save_thm(`Pterm_11`,prove_constructors_one_one Pterm);;
let Pterm_cases =
 save_thm(`Pterm_cases`,prove_cases_thm Pterm_induct);;

% Pterm destructors %
let Is_Const_DEF = new_recursive_definition false Pterm `Is_Const_DEF`
  "(Is_Const (Const s ty) = T) /\
   (Is_Const (Var x) = F) /\
   (Is_Const (App t1 t2) = F) /\
   (Is_Const (Lam x t) = F)";;
let Is_Var_DEF = new_recursive_definition false Pterm `Is_Var_DEF`
  "(Is_Var (Const s ty) = F) /\
   (Is_Var (Var x) = T) /\
   (Is_Var (App t1 t2) = F) /\
   (Is_Var (Lam x t) = F)";;
let Is_App_DEF = new_recursive_definition false Pterm `Is_App_DEF`
  "(Is_App (Const s ty) = F) /\
   (Is_App (Var x) = F) /\
   (Is_App (App t1 t2) = T) /\
   (Is_App (Lam x t) = F)";;
let Is_Lam_DEF = new_recursive_definition false Pterm `Is_Lam_DEF`
  "(Is_Lam (Const s ty) = F) /\
   (Is_Lam (Var x) = F) /\
   (Is_Lam (App t1 t2) = F) /\
   (Is_Lam (Lam x t) = T)";;

let Const_nam_DEF = new_recursive_definition false Pterm `Const_nam_DEF`
  "(Const_nam (Const s ty) = s) /\
   (Const_nam (Var x) = @y.T) /\
   (Const_nam (App t1 t2) = @y.T) /\
   (Const_nam (Lam x t) = @y.T)";;
let Const_ty_DEF = new_recursive_definition false Pterm `Const_ty_DEF`
  "(Const_ty (Const s ty) = ty) /\
   (Const_ty (Var x) = @y.T) /\
   (Const_ty (App t1 t2) = @y.T) /\
   (Const_ty (Lam x t) = @y.T)";;
let Var_var_DEF = new_recursive_definition false Pterm `Var_var_DEF`
  "(Var_var (Const s ty) = @y.T) /\
   (Var_var (Var x) = x) /\
   (Var_var (App t1 t2) = @y.T) /\
   (Var_var (Lam x t) = @y.T)";;
let App_fun_DEF = new_recursive_definition false Pterm `App_fun_DEF`
  "(App_fun (Const s ty) = @y.T) /\
   (App_fun (Var x) = @y.T) /\
   (App_fun (App t1 t2) = t1) /\
   (App_fun (Lam x t) = @y.T)";;
let App_arg_DEF = new_recursive_definition false Pterm `App_arg_DEF`
  "(App_arg (Const s ty) = @y.T) /\
   (App_arg (Var x) = @y.T) /\
   (App_arg (App t1 t2) = t2) /\
   (App_arg (Lam x t) = @y.T)";;
let Lam_var_DEF = new_recursive_definition false Pterm `Lam_var_DEF`
  "(Lam_var (Const s ty) = @y.T) /\
   (Lam_var (Var x) = @y.T) /\
   (Lam_var (App t1 t2) = @y.T) /\
   (Lam_var (Lam x t) = x)";;
let Lam_bod_DEF = new_recursive_definition false Pterm `Lam_bod_DEF`
  "(Lam_bod (Const s ty) = @y.T) /\
   (Lam_bod (Var x) = @y.T) /\
   (Lam_bod (App t1 t2) = @y.T) /\
   (Lam_bod (Lam x t) = t)";;


% --- basic functions on Pterm --- %

% Ptype_of t  is the type of the term t %
let Ptype_of_DEF = new_recursive_definition false Pterm `Ptype_of_DEF`
 "(Ptype_of (Const s ty) = ty) /\
  (Ptype_of (Var x) = SND x) /\
  (Ptype_of (App t1 t2) = HD(TL(Tyop_tyl(Ptype_of t1)))) /\
  (Ptype_of (Lam x t) = Tyop `fun` [SND x;Ptype_of t])";;

% Pboolean t holds if t has type Tyop`bool`[] %
let Pboolean_DEF = new_definition(`Pboolean_DEF`,
 "Pboolean t = (Ptype_of t = Tyop `bool` [])");;

% Pwell_typed t  holds if t is well_typed with respect to the Theory type
  list Tyl and constant list Conl %
let Pwell_typed_DEF = new_recursive_definition false Pterm `Pwell_typed_DEF`
 "(Pwell_typed Typl Conl (Const s ty) = 
     mem1 s Conl /\ Type_OK Typl ty /\ Type_compat ty (corr1 s Conl) /\
     nocontr (Type_instl ty (corr1 s Conl)) ) /\
  (Pwell_typed Typl Conl (Var x) =  Type_OK Typl (SND x) ) /\
  (Pwell_typed Typl Conl (App t1 t2) = 
     Pwell_typed Typl Conl t1 /\ Pwell_typed Typl Conl t2 /\
     Is_Tyop(Ptype_of t1) /\ (Tyop_nam(Ptype_of t1) = `fun`) /\
     (LENGTH(Tyop_tyl(Ptype_of t1)) = 2) /\
     (HD(Tyop_tyl(Ptype_of t1)) = Ptype_of t2) ) /\
  (Pwell_typed Typl Conl (Lam x t) = 
     Pwell_typed Typl Conl t /\ Type_OK Typl (SND x) )";;
new_constant(`Xwell_typed`,":*->bool");;

% Pfree x t holds if x is free in t 
  Pbound x t holds if x is bound in t
  Poccurs x t holds if x occurs in t %
let Pfree_DEF = new_recursive_definition false Pterm `Pfree_DEF`
 "(Pfree x (Const s ty) = F) /\
  (Pfree x (Var y)  = (y=x)) /\
  (Pfree x (App t1 t2) = Pfree x t1 \/ Pfree x t2) /\
  (Pfree x (Lam y t) = ~(y=x) /\ Pfree x t)";;
new_constant(`Xfree`,":string#Type->*->bool");;
let Pbound_DEF = new_recursive_definition false Pterm `Pbound_DEF`
 "(Pbound x (Const s ty) = F) /\
  (Pbound x (Var y)  = F) /\
  (Pbound x (App t1 t2) = Pbound x t1 \/ Pbound x t2) /\
  (Pbound x (Lam y t) = (y=x) \/ Pbound x t)";;
new_constant(`Xbound`,":string#Type->*->bool");;
let Poccurs_DEF = new_definition(`Poccurs_DEF`,
  "Poccurs x t = Pfree x t \/ Pbound x t");;
new_constant(`Xoccurs`,":string#Type->*->bool");;

% list-versions of negated free, bound, occurs %
let Plnotfree_DEF = new_list_rec_definition(`Plnotfree_DEF`,
 "(Plnotfree [] t = T) /\
  (Plnotfree (CONS x xl) t = (~Pfree x t) /\ Plnotfree xl t)");;
let Plnotbound_DEF = new_list_rec_definition(`Plnotbound_DEF`,
 "(Plnotbound [] t = T) /\
  (Plnotbound (CONS x xl) t = (~Pbound x t) /\ Plnotbound xl t)");;
let Plnotoccurs_DEF = new_definition(`Plnotoccurs_DEF`,
 "Plnotoccurs xl t = Plnotfree xl t /\ Plnotbound xl t");;

% versions of negated free for a set of terms  %
let Pallnotfree_SPEC = new_definition(`Pallnotfree_SPEC`,
 "Pallnotfree x tms = !t. t IN tms ==> (~Pfree x t)");;
let Pallnotfree_DEF = save_thm(`Pallnotfree_DEF`,prove
 ("(!x. Pallnotfree x {} = T) /\
   (!x tm tms. Pallnotfree x (tm INSERT tms) 
= (~Pfree x tm) /\ Pallnotfree x tms)",
   CONJ_TAC THENL
   [LRT[Pallnotfree_SPEC;NOT_IN_EMPTY]
   ;REPEAT GEN_TAC THEN LRT[Pallnotfree_SPEC;IN_INSERT] THEN EQ_TAC THENL
    [STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM (ACCEPT_TAC o( RR[] o (SPEC "tm:Pterm")))
     ;GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
   ]]) );;
let Plallnotfree_SPEC = new_definition(`Plallnotfree_SPEC`,
 "Plallnotfree xl tms = !t. t IN tms ==> Plnotfree xl t");;
let Plallnotfree_DEF = save_thm(`Plallnotfree_DEF`,prove
 ("(!xl. Plallnotfree xl {} = T) /\
   (!xl tm tms. Plallnotfree xl (tm INSERT tms) = 
                 (Plnotfree xl tm) /\ Plallnotfree xl tms)",
   CONJ_TAC THENL
   [LRT[Plallnotfree_SPEC;NOT_IN_EMPTY]
   ;REPEAT GEN_TAC THEN LRT[Plallnotfree_SPEC;IN_INSERT] THEN EQ_TAC THENL
    [STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM (ACCEPT_TAC o( RR[] o (SPEC "tm:Pterm")))
     ;GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
   ]]) );;


% --- functions for alpha and beta --- %

% Palreplace1 t' tvl t holds if t' is the result of replacing in t 
  according to tvl, with alpha-renaming
  tvl is a list of pairs (term,(varname,vartype)) 
  the aux-version has extra parameter vvl with alpha-changes  %
let Palreplace1_DEF = new_recursive_definition false Pterm `Palreplace1_DEF`
 "(Palreplace1 t' vvl tvl (Const s ty) = (t' = Const s ty)) /\
  (Palreplace1 t' vvl tvl (Var x) =
    ((Is_Var t' /\ mem1 (Var_var t') vvl) => (x = (corr1 (Var_var t') vvl))
      | (~mem1 x vvl /\
           (mem2 x tvl => (t' = corr2 x tvl)
             | (t' = Var x) ) ) )) /\
  (Palreplace1 t' vvl tvl (App t1 t2) =
     Is_App t' /\
     Palreplace1 (App_fun t') vvl tvl t1 /\
     Palreplace1 (App_arg t') vvl tvl t2) /\
  (Palreplace1 t' vvl tvl (Lam x t1) =
     Is_Lam t' /\ (SND(Lam_var t') = SND x) /\
     Palreplace1 (Lam_bod t') (CONS(Lam_var t',x)vvl) tvl t1)";;
let Palreplace_DEF = new_definition(`Palreplace_DEF`,
   "Palreplace t' tvl t = Palreplace1 t' [] tvl t");;
new_constant(`Xalreplace`,":*->(**#string#Type)list->*->bool");;

% Palpha t' t holds if t' is an alpha-variant of t %
let Palpha_DEF = new_definition(`Palpha_DEF`,
   "Palpha t' t = Palreplace t' [] t");;
new_constant(`Xalpha`,":*->*->bool");;


% Psubst t' ttvl td t means that
   ttvl contains triples (ti', ti, pi), i=1..n, correctly typed
   td is t but with dummies pi replacing some ti
   t' comes from td by alpha-renaming and replacing pi with ti %
let Psubst_triples_DEF = new_list_rec_definition(`Psubst_triples_DEF`,
  "(Psubst_triples [] = T) /\
   (Psubst_triples (CONS (ttv:Pterm#Pterm#(string#Type)) ttvl) =
     (Ptype_of (FST ttv) = Ptype_of (FST(SND ttv))) /\
     (Ptype_of (FST ttv) = SND(SND(SND ttv))) /\
     Psubst_triples ttvl )");;
let list13_DEF = new_list_rec_definition(`list13_DEF`,
  "(list13 ([]:(*#**#***)list) = []) /\
   (list13 (CONS xyz xyzl) = CONS (FST xyz,SND(SND xyz)) (list13 xyzl))");;
let Psubst_DEF = new_definition(`Psubst_DEF`,
 "Psubst Typl Conl t' ttvl td t = 
   Psubst_triples ttvl /\ Pwell_typed Typl Conl td /\
   Plnotoccurs (MAP (SND o SND) ttvl) t /\
   Palreplace t (MAP SND ttvl) td /\
   Palreplace t' (list13 ttvl) td");;
new_constant(`Xsubst`,":*->(**#**#string#Type)list->*->*->bool");;

% Pbeta t x t1 t2 holds if t is the result of beta-reducing (\x.t1)t2 %
let Pbeta_DEF = new_definition(`Pbeta_DEF`,
 "Pbeta t' x t1 t2 = Palreplace t' [t2,x] t1");;
new_constant(`Xbeta`,":**->string#Type->**->*->bool");;


% --- functions needed in type instantiation %

% Pty_occurs a t holds if the type variable a occurs in the term t %
let Pty_occurs_DEF = new_recursive_definition false Pterm `Pty_occurs_DEF`
 "(Pty_occurs a (Const s ty) = Type_occurs a ty) /\
  (Pty_occurs a (Var x)  = Type_occurs a (SND x)) /\
  (Pty_occurs a (App t1 t2) = Pty_occurs a t1 \/ Pty_occurs a t2) /\
  (Pty_occurs a (Lam x t1) =  Type_occurs a(SND x) \/ Pty_occurs a t1)";;

% Pty_snotoccurs a tml holds if tyvar a doesn't occur anywhere in the set tms %
let Pty_snotoccurs_SPEC = new_definition(`Pty_snotoccurs_SPEC`,
 "Pty_snotoccurs a tms = !t. t IN tms ==> ~Pty_occurs a t");;
let Pty_snotoccurs_DEF = save_thm(`Pty_snotoccurs_DEF`,prove
 ("(!s. Pty_snotoccurs s {} = T) /\
   (!s tm tms. Pty_snotoccurs s (tm INSERT tms) = 
       ~Pty_occurs s tm /\ Pty_snotoccurs s tms)",
   CONJ_TAC THENL
   [LRT[Pty_snotoccurs_SPEC;NOT_IN_EMPTY]
   ;REPEAT GEN_TAC THEN LRT[Pty_snotoccurs_SPEC;IN_INSERT] THEN EQ_TAC THENL
    [STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM (ACCEPT_TAC o( RR[] o (SPEC "tm:Pterm")))
     ;GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
   ]]) );;

% Plty_snotoccurs tyl tms holds if no tyvars in tyl occur anywhere in the set tms %
let Plty_snotoccurs_DEF = new_list_rec_definition(`Plty_snotoccurs_DEF`,
 "(Plty_snotoccurs [] tms = T) /\
  (Plty_snotoccurs (CONS h t) tml =
    Pty_snotoccurs h tml /\ Plty_snotoccurs t tml)");;

% Pnewfree t' t is a list of name differences in t' compared to t 
  may contain lots of duplicates %
let Pnewfree1_DEF = new_recursive_definition false Pterm `Pnewfree1_DEF`
 "(Pnewfree1 t bl (Const s ty) = []) /\
  (Pnewfree1 t bl (Var x)  = 
    (mem x bl \/ (FST(Var_var t) = FST x)) => [] | [Var_var t,x] ) /\
  (Pnewfree1 t bl (App t1 t2) =
     APPEND (Pnewfree1 (App_fun t) bl t1) (Pnewfree1 (App_arg t) bl t2) ) /\
  (Pnewfree1 t bl (Lam x t1) = Pnewfree1 (Lam_bod t) (CONS x bl) t1)";;
let Pnewfree_DEF = new_definition(`Pnewfree_DEF`,
   "Pnewfree t' t = Pnewfree1 t' [] t");;

% Ptyinst as t' tyl t holds if t' is the result of replacing types in t 
  according to tyl, with alpha-renaming and renaming of free variables
  according to fvl, and with no replacements for type variables occurring
  in the assumption set as
  the aux-version has extra parameter bvl with alpha-changes  %
let Ptyinst1_DEF = new_recursive_definition false Pterm `Ptyinst1_DEF`
 "(Ptyinst1 t bvl fvl tyl (Const s ty) =
      (t = Const s (Type_replace tyl ty))) /\
  (Ptyinst1 t bvl fvl tyl (Var x) =
     mem1 (Var_var t) bvl => (Is_Var t /\ (x = corr1 (Var_var t) bvl) /\
                              (SND(Var_var t) = Type_replace tyl(SND x)))
      | mem2 x fvl => (t = Var(FST(corr2 x fvl),Type_replace tyl(SND x)))
             | (t = Var(FST x,Type_replace tyl(SND x))) ) /\
  (Ptyinst1 t bvl fvl tyl (App t1 t2) =
     Is_App t /\
     Ptyinst1 (App_fun t) bvl fvl tyl t1 /\
     Ptyinst1 (App_arg t) bvl fvl tyl t2) /\
  (Ptyinst1 t bvl fvl tyl (Lam x t1) =
     Is_Lam t /\
     ~(mem1 (Lam_var t) fvl) /\ (SND(Lam_var t) = Type_replace tyl(SND x)) /\
     Ptyinst1 (Lam_bod t) (CONS(Lam_var t,x)bvl) fvl tyl t1)";;
let Ptyinst_DEF = new_definition(`Ptyinst_DEF`,
   "Ptyinst as t' tyl t =
       Ptyinst1 t' [] (Pnewfree t' t) tyl t /\
       Plallnotfree (MAP SND(Pnewfree t' t)) as");;


