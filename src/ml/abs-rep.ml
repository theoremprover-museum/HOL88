%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        abs-rep.ml                                            %
%                                                                             %
%     DESCRIPTION:      Defines derived inference rules for automatic         %
%                       definition of abstraction and representation          %
%                       functions for defined logical types.                  %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.02.26)                               %
%                                                                             %
%     USES FILES:       basic-hol lisp files, BASIC-HOL.th, genfns.ml,        %
%                       hol-syn.ml, hol-rule.ml, hol-drule.ml, drul.ml        %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: 90.04.10                                              %
%=============================================================================%

% --------------------------------------------------------------------- %
% Must be compiled in the presence of certain HOL inference rules.  So  %
% load hol-rule.ml and hol-drule.ml. For this, we need hol-in-out. And  %
% this loads genfns.ml and hol-syn.ml too (which are also needed). The  %
% HOL term parser is also loaded (and needed).				%
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`;
		    loadf `ml/hol-rule`;
		    loadf `ml/hol-drule`;
		    loadf `ml/drul`);;


% Fetch ABS_REP_THM.							%
let ABS_REP_THM = theorem `BASIC-HOL` `ABS_REP_THM`;;

% --------------------------------------------------------------------- %
% NAME: define_new_type_bijections 					%
%									%
% DESCRIPTION: define isomorphism constants based on a type definition. %
%									%
% USAGE: define_new_type_bijections name ABS REP tyax                   %
%									%
% ARGUMENTS: tyax -- a type-defining axiom of the form returned by	%
%		     new_type_definition. For example:			%
%									%
% 			?rep. TYPE_DEFINITION P rep			%
%									%
%            ABS  --- the name of the required abstraction function     %
%									%
%            REP  --- the name of the required representation function  %
%									%
%            name --- the name under which the definition is stored     %
%									%
% SIDE EFFECTS:    Introduces a definition for two constants "ABS" and  %
%                  "REP" by the constant specification:                 %
%									%
%  		   |- ?ABS REP. (!a. ABS(REP a) = a) /\                 %
%                               (!r. P r = (REP(ABS r) = r)             %
%									%
%                  The resulting constant specification is stored under %
%                  the name given as the first argument.                %
%									%
% FAILURE: if    1) ABS or REP are already constants.                   %
%                2) not in draft mode.                                  %
%                3) input theorem of wrong form.			%
%									%
% RETURNS: The defining property of the representation and abstraction  %
%          functions, given by:                                         %
%             								%
%           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	%
% --------------------------------------------------------------------- %

let define_new_type_bijections name ABS REP tyax =
    if (not(draft_mode())) then failwith `not in draft mode` else
    if is_axiom (current_theory(),name) then 	
       failwith `"` ^ name ^ `" already an axiom or definition` else
    if not(null (hyp tyax)) then 
       failwith `input theorem must have no assumptions` else
    if (is_constant ABS) then failwith ABS ^ ` is already a constant` else
    if (is_constant REP) then failwith REP ^ ` is already a constant` else
   ((let _,[P;rep] = strip_comb(snd(dest_exists(concl tyax))) in
     let _,[aty;rty] = dest_type(type_of rep) in
     let eth = MP (SPEC P (INST_TYPE[aty,":**";rty,":*"]ABS_REP_THM)) tyax in
     new_specification name [`constant`,REP;`constant`,ABS] eth) ?
     failwith `define_new_type_bijections`);;

% --------------------------------------------------------------------- %
% NAME: prove_rep_fn_one_one	 					%
%									%
% DESCRIPTION: prove that a type representation function is one-to-one. %
%									%
% USAGE: if th is a theorem of the kind returned by the ML function	%
%        define_new_type_bijections:					%
%									%
%           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	%
%									%
%	 then prove_rep_fn_one_one th will prove and return a theorem	%
%	 stating that the representation function REP is one-to-one:	%
%									%
%	    |- !a a'. (REP a = REP a') = (a = a')			%
%									%
% --------------------------------------------------------------------- %

let prove_rep_fn_one_one th = 
    (let thm = CONJUNCT1 th in
     let A,R = (I # rator) (dest_comb(lhs(snd(dest_forall(concl thm))))) in
     let _,[aty;rty] = dest_type (type_of R) in
     let a = mk_primed_var(`a`,aty) in let a' = variant [a] a in
     let a_eq_a' = mk_eq(a,a') and 
         Ra_eq_Ra' = mk_eq(mk_comb(R,a),mk_comb (R,a')) in
     let th1 = AP_TERM A (ASSUME Ra_eq_Ra') in
     let ga1 = genvar aty and ga2 = genvar aty in
     let th2 = SUBST [SPEC a thm,ga1;SPEC a' thm,ga2] (mk_eq(ga1,ga2)) th1 in
     let th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a')) in
         GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))) ?
     failwith `prove_rep_fn_one_one`;;

% --------------------------------------------------------------------- %
% NAME: prove_rep_fn_onto	 					%
%									%
% DESCRIPTION: prove that a type representation function is onto. 	%
%									%
% USAGE: if th is a theorem of the kind returned by the ML function	%
%        define_new_type_bijections:					%
%									%
%           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	%
%									%
%	 then prove_rep_fn_onto th will prove and return a theorem	%
%	 stating that the representation function REP is onto:		%
%									%
%	    |- !r. P r = (?a. r = REP a)				%
%									%
% --------------------------------------------------------------------- %

let prove_rep_fn_onto th = 
    (let [th1;th2] = CONJUNCTS th in
     let r,eq = (I # rhs)(dest_forall(concl th2)) in
     let RE,ar = dest_comb(lhs eq) and
         sr = (mk_eq o (\x,y.y,x) o dest_eq) eq in
     let a = mk_primed_var (`a`,type_of ar) in
     let sra = mk_eq(r,mk_comb(RE,a)) in
     let ex = mk_exists(a,sra) in
     let imp1 = EXISTS (ex,ar) (SYM(ASSUME eq)) in
     let v = genvar (type_of r) and 
         A = rator ar and 
	 as = AP_TERM RE (SPEC a th1) in
     let th = SUBST[SYM(ASSUME sra),v](mk_eq(mk_comb(RE,mk_comb(A,v)),v))as in
     let imp2 = CHOOSE (a,ASSUME ex) th in
     let swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2) in
     	 GEN r (TRANS (SPEC r th2) swap)) ? 
     failwith `prove_rep_fn_onto`;;

% --------------------------------------------------------------------- %
% NAME: prove_abs_fn_onto	 					%
%									%
% DESCRIPTION: prove that a type absstraction function is onto. 	%
%									%
% USAGE: if th is a theorem of the kind returned by the ML function	%
%        define_new_type_bijections:					%
%									%
%           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	%
%									%
%	 then prove_abs_fn_onto th will prove and return a theorem	%
%	 stating that the abstraction function ABS is onto:		%
%									%
%	    |- !a. ?r. (a = ABS r) /\ P r				%
%									%
% --------------------------------------------------------------------- %

let prove_abs_fn_onto th = 
    (let [th1;th2] = CONJUNCTS th in
     let a,A,R = (I#((I#rator)o dest_comb o lhs))(dest_forall(concl th1)) in
     let thm1 = EQT_ELIM(TRANS (SPEC (mk_comb (R,a)) th2)
	 	               (EQT_INTRO (AP_TERM R (SPEC a th1)))) in
     let thm2 = SYM(SPEC a th1) in
     let r,P = (I # (rator o lhs)) (dest_forall(concl th2)) in
     let ex = mk_exists(r,mk_conj(mk_eq(a,mk_comb(A,r)),mk_comb(P,r))) in
         GEN a (EXISTS(ex,mk_comb(R,a)) (CONJ thm2 thm1))) ?
     failwith `prove_abs_fn_onto`;;
    


% --------------------------------------------------------------------- %
% NAME: prove_abs_fn_one_one	 					%
%									%
% DESCRIPTION: prove that a type abstraction function is one-to-one. 	%
%									%
% USAGE: if th is a theorem of the kind returned by the ML function	%
%        define_new_type_bijections:					%
%									%
%           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	%
%									%
%	 then prove_abs_fn_one_one th will prove and return a theorem	%
%	 stating that the abstraction function ABS is one-to-one:	%
%									%
%	    |- !r r'. P r ==>						%
%		      P r' ==>						%
%		      (ABS r = ABS r') ==> (r = r')			%
%									%
% --------------------------------------------------------------------- %


let prove_abs_fn_one_one th = 
    (let [th1;th2] = CONJUNCTS th in
     let r,P = (I # (rator o lhs)) (dest_forall(concl th2)) and
         A,R = (I # rator) (dest_comb(lhs(snd(dest_forall(concl th1))))) in
     let r' = variant [r] r in
     let as1 = ASSUME(mk_comb(P,r)) and as2 = ASSUME(mk_comb(P,r')) in
     let t1 = EQ_MP (SPEC r th2) as1 and t2 = EQ_MP (SPEC r' th2) as2 in
     let eq = (mk_eq(mk_comb(A,r),mk_comb(A,r'))) in
     let v1 = genvar(type_of r) and v2 = genvar(type_of r) in
     let i1 = DISCH eq
              (SUBST [t1,v1;t2,v2] (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq))) and
         i2 = DISCH (mk_eq(r,r')) (AP_TERM A (ASSUME (mk_eq(r,r')))) in
     let thm = IMP_ANTISYM_RULE i1 i2 in
     let disch =  DISCH (mk_comb(P,r)) (DISCH (mk_comb(P,r')) thm) in
         GEN r (GEN r' disch)) ? 
     failwith `prove_abs_fn_one_one`;;
