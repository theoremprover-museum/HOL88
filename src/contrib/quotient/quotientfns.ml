%
This file defines functions needed for constructing
quotient types.
%

%
AUTHOR: TON KALKER
DATE  : 2 JUNE 1989
%

let check_quotient_def =
   set_fail_prefix `not equivalence theorem!: `
   (\thm. 
   let asl,w = dest_thm thm in
   let t1,t2 = dest_comb w in
   let name,ty = (dest_const t1 ? failwith `operator`) in 
   let base_type = ((hd o snd o dest_type o
                     hd o snd o dest_type) ty ? failwith `types`) in
   if not (asl = []) then failwith `assumptions`
   if not (name = `EQUIVALENCE`) then failwith `not EQUIVALENCE`
   if not (is_const t2) then failwith `operand` 
   else t2,base_type);;

% <name>_ISO_DEF added for new define_new_type_bijections.		%
% TFM 90.04.11 HOL88 Version 1.12					%

let construct_quot_ty(name,thm) = 
             let equi, base_type = check_quotient_def thm in
             let exists_thm = MATCH_MP (DISCH_ALL EXISTS_CLASS) thm and 
                 is_mk_class_thm = MATCH_MP (DISCH_ALL IS_MK_CLASS) thm in
             let w = concl exists_thm in
             let tm = (fst o dest_comb o snd o dest_exists) w in  
             let thm1 = new_type_definition(name,tm,exists_thm) in
	     let ISO = 
	         define_new_type_bijections
		 (name ^ `_ISO_DEF`) (`ABS_` ^ name) (`REP_` ^ name) thm1 in
             let thml = 
	         [prove_abs_fn_one_one ISO; prove_abs_fn_onto ISO] in
             let thm3 = ( GEN_ALL o
                         (REWRITE_RULE[is_mk_class_thm]) o
                         (SPEC "MK_CLASS ^equi (x':^base_type)") o
                         (SPEC "MK_CLASS ^equi (x:^base_type)"))(el 1 thml) in
             let thm4 = (el 2 thml) in 
             let current = current_theory() in
             let [ABS_name] = filter 
                            (\tm.((fst o dest_const) tm) = (`ABS_` ^ name))
                            (constants current) in
             let quot_ty = ((el 2) o snd o dest_type o type_of) ABS_name in
             let PROJ_name = mk_var(`PROJ_` ^ name,":^base_type ->^quot_ty") in
             let proj = new_definition(`PROJ_` ^name, 
                        "^PROJ_name x = ^ABS_name (MK_CLASS ^equi x)") in
             proj,thm3,thm4,base_type,quot_ty,equi;;           
                                    
let prove_proj_onto name thm proj thm4 base_type quot_ty= 
            let surjective_thm = MATCH_MP (DISCH_ALL SURJECTIVE_LEMMA) thm in 
            let PROJ_name = mk_const(`PROJ_` ^ name,":^base_type ->^quot_ty") in 
            let tm = "ONTO ^PROJ_name" in         
            TAC_PROOF(
             ([],tm),
             REWRITE_TAC[ONTO_DEF;proj] THEN 
             STRIP_TAC THEN
             STRIP_ASSUME_TAC (SPEC "y:^quot_ty" thm4) THEN
             ASSUM_LIST
              (\asl.STRIP_ASSUME_TAC (MATCH_MP surjective_thm (hd asl))) THEN
             EXISTS_TAC "x:^base_type" THEN
             ASM_REWRITE_TAC[]);;   

let prove_proj_universal name thm proj thm3 base_type quot_ty equi =
            let universal_thm = MATCH_MP (DISCH_ALL UNIVERSAL_LEMMA) thm in
            let PROJ_name = mk_const(`PROJ_` ^ name,":^base_type ->^quot_ty") in 
            let tm = "!x y.((^PROJ_name x = ^PROJ_name y) = (^equi x y))" in
            TAC_PROOF(
             ([],tm),
             REWRITE_TAC[proj;thm3;universal_thm]);;  

let prove_proj_factor name base_type quot_ty  thml = 
            let thm1 = INST_TYPE[(base_type,":*");(quot_ty,":***")] FACTOR_THM in
            let thm2 = SPEC "f:^base_type -> **" thm1 in 
            let PROJ_name = mk_const(`PROJ_` ^ name,":^base_type ->^quot_ty") in       
            let thm3 = SPEC "^PROJ_name" thm2 in
            let thm4 = GEN_ALL thm3 in
            REWRITE_RULE thml thm4;;

let define_quotient_type(name,thm) =
             let proj,thm3,thm4,base_type,quot_ty,equi = construct_quot_ty(name,thm)
             in
             let string1 = `SURJ_PROJ_` ^ name ^ `_THM` and
                 string2 = `UNIV_PROJ_` ^ name ^ `_THM` and
                 string3 = `FACTOR_PROJ_` ^ name ^ `_THM`
             in
             let thm1 = save_thm(string1,
                        prove_proj_onto name thm proj thm4 base_type quot_ty) and
                 thm2 = save_thm(string2,
                        prove_proj_universal name thm proj thm3 base_type quot_ty equi) 
             in
             let thm3 = save_thm(string3,
                        prove_proj_factor name base_type quot_ty [thm1;thm2])
             in [thm1;thm2;thm3];;

let FACTOR_TAC surj_thml univ_thml =
      MATCH_MP_TAC FACTOR_THM THEN
      REWRITE_TAC([ONTO_SURJ_THM;P;]@surj_thml) THEN
      CONV_TAC (RAND_CONV (ABS_CONV PROD_CONV)) THEN
      CONV_TAC PROD_CONV THEN
      BETA_TAC THEN
      REWRITE_TAC([PAIR_EQ]@univ_thml);;

let new_unique_specification = 
      set_fail_prefix `new_unique_specification`
      (\name [flag,c] thm.
      (
      let thm1 = (BETA_RULE o (CONV_RULE EXISTS_UNIQUE_CONV)) thm
      in                                                         
      let ex_thm,uniq_thm = CONJ_PAIR thm1
      in      
      let thm2 = (new_specification name [flag,c] ex_thm ?
                  (print_string (name ^ ` already defined`);
                   print_newline();
                   definition (current_theory()) name))
      in
      let [newconst] = 
               filter
               (\d.(c = (fst o dest_const) d))
               (constants (current_theory()))
      in
      let thm3 = SPEC newconst uniq_thm 
      in 
      let thm4 = REWRITE_RULE[thm2] thm3
      in
      let x = fst(dest_forall(concl thm4)) 
      in  
      let thm5 = CONV_RULE (GEN_ALPHA_CONV "f:^(type_of x)") thm4 
      in
      let thm6 = (save_thm((name ^ `_UNIQUE`), thm5) ?
                  (print_string (name ^ `_UNIQUE already present`);
                   print_newline();
                   theorem (current_theory()) (name ^ `_UNIQUE`)))
      in
      [thm2;thm6]
      ));;




