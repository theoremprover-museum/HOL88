% mk_inference1.ml

  Theory of HOL-proofs: inferences
%

new_theory `inference`;;
%
load_library `finite_sets`;;
load_library `more_lists`;;
new_parent `Pterm`;;
load_library `string`;;
load_library `taut`;;
loadf `defs/defs`;;
%

% --- sequents and primitive inferences --- %


let Psequent = define_type `Psequent`
  `Psequent = Pseq (Pterm)set Pterm`;;
let Pseq_assum_DEF = new_recursive_definition false Psequent `Pseq_assum_DEF`
 "Pseq_assum (Pseq as t) = as";;
let Pseq_concl_DEF = new_recursive_definition false Psequent `Pseq_concl_DEF`
 "Pseq_concl (Pseq as t) = t";;
let Pseq_induct = save_thm(`Pseq_induct`,prove_induction_thm Psequent);;
let Pseq_cases = save_thm(`Pseq_cases`,prove_cases_thm Pseq_induct);;
let Pseq_11 = save_thm(`Pseq_11`,prove_constructors_one_one Psequent);;

% PEQ t1 t2 is the equality term t1=t2 %
let PEQ_DEF = new_definition(`PEQ_DEF`,
  "PEQ t1 t2 =
     App (App (Const `=` (Tyop `fun`[Ptype_of t1;Tyop `fun`
                            [Ptype_of t1;Tyop `bool`[]]]))
              t1)
         t2");;

% PIMP t1 t2 is the implication term t1==>t2 %
let PIMP_DEF = new_definition(`PIMP_DEF`,
 "PIMP t1 t2 = 
   App (App (Const `==>` (Tyop `fun`[Tyop `bool`[];Tyop `fun`
                            [Tyop `bool`[];Tyop `bool`[]]]))
            t1)
       t2");;

% Is_EQtm tests whether a term is an equality %
let Is_EQtm_DEF = new_definition(`Is_EQtm_DEF`,
 "Is_EQtm t = Is_App t /\ Is_App(App_fun t) /\
   (App_fun(App_fun t) = Const `=`(Tyop `fun`[Ptype_of(App_arg t);Tyop `fun`
                                    [Ptype_of(App_arg t);Tyop `bool`[]]]))");;

% Boolean and well-typed sequents %
let Pseq_boolean_DEF = new_recursive_definition false Psequent
 `Pseq_boolean_DEF`
 "Pseq_boolean (Pseq as t) = SEVERY Pboolean as /\ Pboolean t";;
let Pseq_well_typed_DEF = new_recursive_definition false Psequent
 `Pseq_well_typed_DEF`
 "Pseq_well_typed Typl Conl (Pseq as t) =
   SEVERY (Pwell_typed Typl Conl) as /\ Pwell_typed Typl Conl t";;

% Characterisations of the eight primitive inferences %
let PASSUME_DEF = new_recursive_definition false Psequent `PASSUME_DEF`
 "PASSUME Typl Conl (Pseq as t) tm = 
   Pwell_typed Typl Conl tm /\ Pboolean tm /\ (t = tm) /\ (as={tm})";;

let PREFL_DEF = new_recursive_definition false Psequent `PREFL_DEF`
 "PREFL Typl Conl (Pseq as t) tm = 
   Pwell_typed Typl Conl tm /\ (as = {}) /\ (t = PEQ tm tm)";;

let PBETA_CONV_DEF = new_recursive_definition false Psequent `PBETA_CONV_DEF`
 "PBETA_CONV Typl Conl (Pseq as t) tm = 
   Pwell_typed Typl Conl tm /\ 
   (as={}) /\ Is_App tm /\ Is_Lam(App_fun tm) /\
   (t = PEQ tm (App_arg t)) /\
   Pbeta(App_arg t)(Lam_var(App_fun tm))(Lam_bod(App_fun tm))(App_arg tm)";;

% Psubst_newlist deconstructs equalities in a list of (equality,dummyvar) %
let Psubst_newlist_DEF = new_list_rec_definition(`Psubst_newlist_DEF`,
 "(Psubst_newlist [] = []) /\
  (Psubst_newlist (CONS (h:Psequent#string#Type) t) = 
    CONS (App_arg(Pseq_concl(FST h)),App_arg(App_fun(Pseq_concl(FST h))),SND h)
         (Psubst_newlist t) )");;
let PSUBST_DEF = new_recursive_definition false Psequent `PSUBST_DEF`
 "PSUBST Typl Conl (Pseq as t) thdl td th = 
   Pwell_typed Typl Conl td /\
   EVERY Is_EQtm (MAP Pseq_concl(MAP FST thdl)) /\
   Psubst Typl Conl t (Psubst_newlist thdl) td (Pseq_concl th) /\
   (as = (Pseq_assum th) UNION (LUNION (MAP Pseq_assum(MAP FST thdl))))";;

let PABS_DEF = new_recursive_definition false Psequent `PABS_DEF`
 "PABS Typl Conl (Pseq as t) tm th = 
   Pwell_typed Typl Conl tm /\ Is_EQtm(Pseq_concl th) /\
   Is_Var tm /\ Type_OK Typl (SND(Var_var tm)) /\ 
   (t = PEQ
      (Lam (Var_var tm) (App_arg(App_fun(Pseq_concl th))))
      (Lam (Var_var tm) (App_arg(Pseq_concl th))) ) /\
   (as = Pseq_assum th) /\ Pallnotfree (Var_var tm) as";;

let PINST_TYPE_DEF = new_recursive_definition false Psequent `PINST_TYPE_DEF`
 "PINST_TYPE Typl (Pseq as t) tyl th =
   EVERY (Type_OK Typl) (MAP FST tyl) /\
   Ptyinst as t tyl (Pseq_concl th) /\
   Plty_snotoccurs (MAP SND tyl) as /\
   (as = Pseq_assum th)";;

let PDISCH_DEF = new_recursive_definition false Psequent `PDISCH_DEF`
 "PDISCH Typl Conl (Pseq as t) tm th = 
   Pwell_typed Typl Conl tm /\ Pboolean tm /\
   (t = PIMP tm (Pseq_concl th)) /\ (as = (Pseq_assum th) DELETE tm)";;

let PMP_DEF = new_recursive_definition false Psequent `PMP_DEF`
 "PMP (Pseq as t) th1 th2 =
   (Pseq_concl th1 = PIMP (Pseq_concl th2) t) /\
   (as = (Pseq_assum th1) UNION (Pseq_assum th2))";;


% --- the type of inferences --- %

let Inference = define_type `Inference`
  `Inference = AX_inf Psequent
              | AS_inf Psequent Pterm
              | RE_inf Psequent Pterm
              | BE_inf Psequent Pterm
              | SU_inf Psequent (Psequent#string#Type)list Pterm Psequent
              | AB_inf Psequent Pterm Psequent
              | IN_inf Psequent (Type#string)list Psequent
              | DI_inf Psequent Pterm Psequent
              | MP_inf Psequent Psequent Psequent`;;
let Inf_induct = save_thm(`Inf_induct`,prove_induction_thm Inference);;
let Inf_cases = save_thm(`Inf_cases`,prove_cases_thm Inf_induct);;

% the conclusion of an inference %
let Inf_concl_DEF = new_recursive_definition false Inference `Inf_concl_DEF`
 "(Inf_concl (AX_inf s) = s) /\
  (Inf_concl (AS_inf s t) = s) /\
  (Inf_concl (RE_inf s t) = s) /\
  (Inf_concl (BE_inf s t) = s) /\
  (Inf_concl (SU_inf s tdl t s1) = s) /\
  (Inf_concl (AB_inf s t s1) = s) /\
  (Inf_concl (IN_inf s tyl s1) = s) /\
  (Inf_concl (DI_inf s t s1) = s) /\
  (Inf_concl (MP_inf s s1 s2) = s)";;

% the hypotheses of an inference %
let Inf_hyps_DEF = new_recursive_definition false Inference `Inf_hyps_DEF`
 "(Inf_hyps (AX_inf s) = []) /\
  (Inf_hyps (AS_inf s t) = []) /\
  (Inf_hyps (RE_inf s t) = []) /\
  (Inf_hyps (BE_inf s t) = []) /\
  (Inf_hyps (SU_inf s sdl t s1) = CONS s1 (MAP FST sdl)) /\
  (Inf_hyps (AB_inf s t s1) = [s1]) /\
  (Inf_hyps (IN_inf s tyl s1) = [s1]) /\
  (Inf_hyps (DI_inf s t s1) = [s1]) /\
  (Inf_hyps (MP_inf s s1 s2) = [s1;s2])";;

% a correct primitive inference %
let OK_Inf_DEF = new_recursive_definition false Inference `OK_Inf_DEF`
 "(OK_Inf Typl Conl Axil (AX_inf s) = mem s Axil) /\
  (OK_Inf Typl Conl Axil (AS_inf s t) = PASSUME Typl Conl s t) /\
  (OK_Inf Typl Conl Axil (RE_inf s t) = PREFL Typl Conl s t) /\
  (OK_Inf Typl Conl Axil (BE_inf s t) = PBETA_CONV Typl Conl s t) /\
  (OK_Inf Typl Conl Axil (SU_inf s tdl t s1) = PSUBST Typl Conl s tdl t s1) /\
  (OK_Inf Typl Conl Axil (AB_inf s t s1) = PABS Typl Conl s t s1) /\
  (OK_Inf Typl Conl Axil (IN_inf s tyl s1) = PINST_TYPE Typl s tyl s1) /\
  (OK_Inf Typl Conl Axil (DI_inf s t s1) = PDISCH Typl Conl s t s1) /\
  (OK_Inf Typl Conl Axil (MP_inf s s1 s2) = PMP s s1 s2)";;


% extras for pretty-printing of results %
let Xsequent = define_type `Xsequent`
  `Xsequent = Xseq (bool)set bool`;;
new_type 0 `Xinference`;;
new_constant (`AX_Xinf`,":Xsequent->Xinference");;
new_constant (`AS_Xinf`,":Xsequent->*->Xinference");;
new_constant (`RE_Xinf`,":Xsequent->*->Xinference");;
new_constant (`BE_Xinf`,":Xsequent->*->Xinference");;
new_constant (`SU_Xinf`,":Xsequent->(Xsequent#string#Type)list->bool->Xsequent
                           ->Xinference");;
new_constant (`AB_Xinf`,":Xsequent->*->Xsequent->Xinference");;
new_constant (`IN_Xinf`,":Xsequent->(Type#string)list->Xsequent->Xinference");;
new_constant (`DI_Xinf`,":Xsequent->bool->Xsequent->Xinference");;
new_constant (`MP_Xinf`,":Xsequent->Xsequent->Xsequent->Xinference");;

