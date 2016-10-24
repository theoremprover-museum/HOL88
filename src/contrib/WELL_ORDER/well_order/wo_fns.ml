%<
FILE: wo_fns.ml.ml

AUTHOR: Ton Kalker

DATE: 13-9-89

COMMENT: Functions for canonical well_ordering.
    	 
         1) Induction tac

         2) Conversion that transforms a term into
            the appropriat existence theorem.

         3) wo_rec_induction
>% 
%<
load_library `auxiliary`;;

load_theory `transfinite`;; 

autoload_defs_and_thms `transfinite`;;
>%  

let TRANSFIN_INDUCT_TAC (A,t) = 
    (let th = TRANSFIN_INDUCTION in
     let th_tac = ASSUME_TAC in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
     let tac = 
     (MATCH_MP_TAC thm THEN 
      GEN_TAC THEN
      CONV_TAC (RAND_CONV BETA_CONV) THEN
      CONV_TAC (LHS_CONV(BINDER_CONV(RAND_CONV BETA_CONV))) THEN
      REPEAT STRIP_TAC) in
      (tac (A,t))) ? failwith `TRANSFIN_INDUCT`;; 

let WO_CONV tm = 
       (let th = GEN_ALL(CONJUNCT1(EXP_UNIQUE_RULE (SPEC_ALL wo_Axiom))) in
	let lhs,rhs = dest_eq(snd(strip_forall tm)) in
        let obpat = "RESTRICT (y:*) (f:*->**)" in
	let pred  = can (\t.match obpat t) in
	let t1 = hd(find_terms pred tm) in
	let v = genvar(type_of t1) in
	let t2 = subst [v,t1] rhs in
	let t3 = mk_abs(v,t2) in
	let tau = fst(dest_forall(concl th)) in
	let tyi = snd(match tau t3) in
	let th1 = (SPEC t3 (INST_TYPE tyi th)) in
	let th2 = SELECT_RULE th1 in
	let th3 = BETA_RULE th2 in
	let fn,body = dest_exists(concl th1) in
	let gn,l = (strip_comb(rator lhs)) in
	let fsel = list_mk_abs(l,(mk_select(fn,body))) in
	let func = genvar(type_of fsel) in
	let funcexp = list_mk_comb(func,l) in
	let body' = list_mk_forall(l,(subst [funcexp,fn] body)) in
	let w = mk_exists(func,body') in
	let th4 = prove(w,EXISTS_TAC fsel THEN ((length l) TIMES GEN_TAC) THEN
                  BETA_TAC THEN REWRITE_TAC[th3]) in
	let th5 = BETA_RULE(CONV_RULE (GEN_ALPHA_CONV gn) th4) in
        th5) ? failwith `WO_CONV`;;

let wo_rec_definition infix_flag name tm = 
	let thm = WO_CONV tm 
	in
	new_specification
	name
	[(infix_flag=>`infix`|`constant`),
	((fst o dest_var o fst o dest_exists o concl) thm)]
	thm;; 


%<TESTING:

let tm = "(f (A:*->*) (B:*->*) (y:*):*) = A(SND(RESTRICT y (f A B))(FST(RESTRICT y (f A B))))" ;;   

WO_CONV tm;;

wo_rec_definition false `test` tm;;

>%
