%----------------------------------------------------------------

   File:         abs_theory.ml

   Description:  

   Defines ML functions for defining generic structures.  This is
   a refinement of the abstract.ml package.

   Author:       (c) P. J. Windley 1991

   Date:         07 NOV 91

   Modification History:

   07NOV91 --- [PJW] Original file.

   22JAN92 --- [PJW] Changed make_abs_goal to account for different 
               type instantiations.  This allows proof of goals about
               more than one instance of a generic object.

   07JUN92 --- [PJW] Added sections to hide internal functions.  
               Changed new_theory_obligation to take only one
               thob instead of a list of thobs.
               Added definition of STRIP_THOBS_THEN and redefined
               STRIP_THOBS_TAC in terms of it.
               Changed implementation of instantiate_abstract_theorems
               to allow the use of explicit theory obligations.

----------------------------------------------------------------%

%----------------------------------------------------------------

   To Do:

   Extending absract representations---
       This is difficult since HOL doesn't handle subtypes.  

----------------------------------------------------------------%

print_newline();;
message(`loading abs_theory`);;

%----------------------------------------------------------------
 Extend the help search path 
----------------------------------------------------------------%
tty_write `Extending help search path`;
let path = library_pathname()^`/abs_theory/help/entries/` in
    set_help_search_path (union [path] (help_search_path()));;


begin_section abs_theory;;

%----------------------------------------------------------------

 load the patch to concat if the following ml statement prints a 
 number less than 5000 and HOL version <= 2.00.

 lisp `(print call-arguments-limit)`;;


let test_string n = 
    letrec aux s i = 
        (i = 0) => s | aux (`x`^s) (i-1) in
    aux `` n;;

----------------------------------------------------------------%

% message `patching concat`;loadf `concat-patch`;; %

%----------------------------------------------------------------
 define some general list functions
----------------------------------------------------------------%

let int_to_term = (((C (curry mk_const)) ":num") o string_of_int) and
    term_to_int = (int_of_string o fst o dest_const);;

letrec for n lst = 
    (n=0) => []
           | (hd lst).(for (n-1) (tl lst));;

% function composition over a list of functions %
letrec ol lst = null(lst) => I | (hd lst) o (ol (tl lst)) ;;

%----------------------------------------------------------------
 General purpose inference rules
----------------------------------------------------------------%
let X_SPEC tm v thm =
    let tml = (fst o strip_forall o concl) thm in
    letrec SPEC1_aux tml sthm =
        (tml = []) => sthm |
        ((hd tml) = tm) =>
           (SPEC v sthm) |
           (GEN (hd tml) (SPEC1_aux (tl tml) (SPEC (hd tml) sthm))) in
    SPEC1_aux tml thm;;

letrec CONJ_IMP th =
    let w = concl th in
    if is_imp w then
        let ante,conc = dest_imp w in
        if is_conj ante then
            let a,b = dest_conj ante in
            CONJ_IMP
            (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))
        else (DISCH ante (CONJ_IMP (UNDISCH th)))
   else th;;

%----------------------------------------------------------------
 define auxilliary functions for new_abstract_representation
----------------------------------------------------------------%

let abs_type_info = (type_of o snd o dest_comb o fst o dest_eq o snd o 
                     strip_forall o snd o dest_abs o snd o dest_comb o 
                     snd o strip_forall o concl) ;;

let dest_all_type ty = 
     is_vartype ty => (dest_vartype ty,[]:(type)list) | dest_type ty;;

let string_from_type ty =
    letrec string_aux ty = 
	let s,tl = dest_all_type ty in
	null tl => s |
	let sl = map string_aux tl in
	`(`^(itlist (\x y. x^`,`^y) (butlast sl) (last sl))^`)`^s in
    (string_aux ty)^` `;;


let ty_str name lst = 
      name^` = `^name^` `^
        (itlist (\x y. x^`  `^y) (map string_from_type lst) ``);;

letref def_prefix = `abs_def_`;;

%----------------------------------------------------------------
 new_abstract_representation:

 Defines type for representation and selectors on type.
----------------------------------------------------------------%

let new_abstract_representation name lst = 
    let nl,tl = split lst in 
    let ty_axiom = define_type name (ty_str name tl) in
    let cons_term = 
       (snd o dest_comb o fst o dest_eq o snd o strip_forall o snd o 
        dest_abs o snd o dest_comb o snd o strip_forall o concl) ty_axiom in
    let make_rec_def (x, y) =
	new_recursive_definition false ty_axiom (def_prefix^x)
	"^(mk_var (x,mk_type(`fun`,[type_of cons_term;
					     type_of y]))) ^cons_term = ^y" in
    (map2 make_rec_def (nl,(snd o strip_comb) cons_term));ty_axiom;;


let get_abs_defs theory =
    let prefix_len = length o explode in
    map snd (
    mapfilter (\x. (((for (prefix_len def_prefix)) o explode o fst) x) =
                 (explode def_prefix) => x | fail)
               (definitions theory));;


let instantiate_abstract_definition th_name def_name defn2 inst_list =
    let def = definition th_name def_name in
    let inst_def =
        GEN_ALL (
        BETA_RULE (
        REWRITE_RULE (get_abs_defs th_name) (
        ol (map (\(x,y).INST_TY_TERM (match x y)) inst_list)
                 (SPEC_ALL def)))) in
    let new_def =
        GEN_ALL (
        BETA_RULE (
        REWRITE_RULE (get_abs_defs th_name) (
        ol (map (\(x,y).INST_TY_TERM (match x y)) inst_list)
                 (SPEC_ALL defn2)))) in
    BETA_RULE (ONCE_REWRITE_RULE [inst_def] new_def);;


%----------------------------------------------------------------
 Auxilliary definitions for theory obligations
----------------------------------------------------------------%

letref thobs = []:(type#thm)list;;

let thobs_prefix = `thobs_`;;

let new_theory_obligations stm_pair = 
    let get_thob_type thm = 
	 ((type_of o rand o fst o dest_eq o 
           snd o strip_forall o concl) thm) in 
    let is_not_pred_def tm = 
        not((type_of o snd o dest_eq o 
             snd o strip_forall o snd) tm = ":bool") in
%    let not_bool_list = (filter is_not_pred_def stm_pair) in %
    let make_def (x,y) = (
        let new_def = new_definition (thobs_prefix^x, y) in
        (get_thob_type new_def,new_def)) in
    (is_not_pred_def stm_pair) => 
        failwith `NON PREDICATE TERMS IN THEORY OBLIGATIONS` |
        (thobs := [make_def stm_pair] @ thobs);();;


let get_thobs theory = 
    let prefix_len = length o explode in
    let get_thob_type thm = 
	 ((type_of o rand o fst o dest_eq o 
           snd o strip_forall o concl) thm) in 
    let the_thobs = 
        filter (\x. (((for (prefix_len thobs_prefix)) o explode o fst) x) = 
		       (explode thobs_prefix))
		 (definitions theory) in
    thobs := (map (\(x,y). (get_thob_type y, y)) the_thobs) @ thobs;
    thobs;;


%----------------------------------------------------------------
 Functions for proving abstract goals.
----------------------------------------------------------------%

let orelsef f g x = (f x) ? (g x);;

ml_curried_infix `orelsef`;;

let D (f,g) x = (f x,g x);;

ml_paired_infix `D`;;

let make_abs_goal (hyps,go) = 
    if null(thobs) then failwith `No theory obligations defined.` else
    let vl,pred = strip_forall go in
    let ql = union vl (frees pred) in
    let type_cons_of = fst o (dest_type orelsef (dest_vartype D \x.[])) in
    let thob_types = map (type_cons_of o fst) thobs in
    let tmp_goal = list_mk_forall 
	  (filter (\x. not(mem ((type_cons_of o type_of) x) thob_types)) ql,
	   pred) in
    let vars = filter (\x. mem ((type_cons_of o type_of) x) thob_types) ql in
    let make_hyps var = 
	let get_thob_var tm = 
	    ((rand o fst o dest_eq o snd o strip_forall ) tm) in
	let thob = snd (((assoc o type_cons_of o type_of) var) 
                        (map (type_cons_of # I) thobs)) in
	(conjuncts o snd o dest_eq o concl o 
			 (INST_TY_TERM (match ((get_thob_var o concl) thob) 
                                              var)) o 
			 SPEC_ALL) thob in
    (hyps@(flat (map make_hyps vars)), tmp_goal);;

%Prove and store an abstract theorem%
let prove_abs_thm(tok, w, tac:tactic) =
    let gl,prf = tac (make_abs_goal ([],w)) in
    if null gl then save_thm (tok, prf[])
    else
       (message (`Unsolved goals:`);
        map print_goal gl;
        print_newline();
        failwith (`prove_thm -- could not prove ` ^ tok));;


% ABS_TAC_PROOF (g,tac) uses tac to prove the abstract goal g     %
let ABS_TAC_PROOF : (goal # tactic) -> thm =
    set_fail_prefix `ABS_TAC_PROOF`
       (\(g,tac). 
           let new_g = (make_abs_goal g) in
           let gl,p = tac new_g in
           if null gl then p[]
           else (
              message (`Unsolved goals:`);
              map print_goal gl;
              print_newline();
              failwith `unsolved goals`));;


%Set the top-level goal, initialize %
let set_abs_goal g = 
           let new_g = (make_abs_goal g) in
           change_state (abs_goals (new_stack new_g));;

let g = \t. set_abs_goal([],t);;

let STRIP_THOBS_THEN ttac =
    if null(thobs) then failwith `No theory obligations defined.` else (
    REPEAT GEN_TAC THEN
    STRIP_GOAL_THEN 
      (ttac o (REWRITE_RULE (map snd thobs))));;


let STRIP_THOBS_TAC ((asl,thm):goal) = 
     STRIP_THOBS_THEN STRIP_ASSUME_TAC(asl,thm);;


%----------------------------------------------------------------
  Functions for USING an abstract theory
----------------------------------------------------------------%

let new_abstract_parent s = 
    new_parent s;
    get_thobs s;
    ();;

let EXPAND_THOBS_TAC name = 
    REWRITE_TAC ((map snd thobs) @ get_abs_defs name);;


let instantiate_abstract_theorem th_name thm_name inst_list lemma_list =
    let thm =  (theorem th_name thm_name) in
    let inst_thm =
        CONJ_IMP ( 
	BETA_RULE (
	REWRITE_RULE ((map snd thobs) @ get_abs_defs th_name) (
	(ol (map (\(x,y).INST_TY_TERM (match x y)) inst_list))(
	(DISCH_ALL o (ol (map (\l.(X_SPEC (fst l) (fst l))) inst_list)))
         thm)))) in
    let mk_thm_list = 
         CONJUNCTS o BETA_RULE o 
          (REWRITE_RULE ((map snd thobs) @ get_abs_defs th_name)) in
    let thm_list = 
	map (\y. find (\x.(concl x) = y) 
		 (flat (map mk_thm_list lemma_list)))
	    ((hyp o UNDISCH_ALL o CONJ_IMP) inst_thm) in
    LIST_MP thm_list inst_thm;;

%----------------------------------------------------------------
 Modify the standard commands so that they know about obligation
 lists.  
----------------------------------------------------------------%
let close_theory_orig = close_theory;;

let close_theory x = 
   thobs := [];
   close_theory_orig x;;

let new_theory_orig = new_theory;;

let new_theory x = 
   thobs := [];
   new_theory_orig x;;

%----------------------------------------------------------------
 Bind exportable functions to it
----------------------------------------------------------------%
(
ABS_TAC_PROOF,
EXPAND_THOBS_TAC,
STRIP_THOBS_TAC,
STRIP_THOBS_THEN,
abs_type_info,
close_theory,
g,
instantiate_abstract_definition,
instantiate_abstract_theorem,
new_abstract_parent,
new_abstract_representation,
new_theory,
new_theory_obligations,
prove_abs_thm,
set_abs_goal
);;

end_section abs_theory;;

%----------------------------------------------------------------
 Recover exportable functions from it.
----------------------------------------------------------------%
let (
ABS_TAC_PROOF,
EXPAND_THOBS_TAC,
STRIP_THOBS_TAC,
STRIP_THOBS_THEN,
abs_type_info,
close_theory,
g,
instantiate_abstract_definition,
instantiate_abstract_theorem,
new_abstract_parent,
new_abstract_representation,
new_theory,
new_theory_obligations,
prove_abs_thm,
set_abs_goal
) = it;;

