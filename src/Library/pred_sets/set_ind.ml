% ===================================================================== %
% FILE		: set_ind.ml						%
% DESCRIPTION   : Induction principle for finite sets.			%
%								        %
% AUTHOR	: Philippe Leveilley					%
%									%
% REWRITTEN     : T Melham						%
% DATE		: 90.03.14 (adapted for pred_sets: January 1992)	%
%									%
% REMARKS	: Dependence on taut library removed. Use of rewriting  %
%		  eliminated.  Optimized for speed.  Simplified. 	%
% ===================================================================== %

% --------------------------------------------------------------------- %
%                                                                       %
%    "!s. FINITE s ==>  P s"                          			%
%   ==========================     SET_INDUCT_TAC 			%
%    P EMPTY     P (x INSERT t)                         		%
%                 [ "FINITE t" ]                       			%
%		  [ "P s"						%
%                 [ "~x IN t"]                           		%
%									%
% --------------------------------------------------------------------- %

let SET_INDUCT_TAC =
    let FINITE_INDUCT = theorem `pred_sets` `FINITE_INDUCT` and
        check = assert \tm. fst(dest_const(rator tm)) = `FINITE` in
    let MK_IMP1 = let IMP = "==>" in \tm. AP_TERM (mk_comb(IMP,tm)) and
        MK_IMP2 = let IMP = "==>" in \th1 th2. MK_COMB(AP_TERM IMP th1,th2) in
    let sconv = 
        let dest = (I # dest_imp) o dest_forall in
	\tm. let s,a,e,h,c = (I # (I # dest)) (dest tm) in
	     let th1 = RAND_CONV BETA_CONV a and th2 = BETA_CONV c in
	         FORALL_EQ s (MK_IMP2 th1 (FORALL_EQ e (MK_IMP1 h th2))) in
    let conv = let CONJ = "/\" in
               \tm. let base,step = dest_conj tm in
	            MK_COMB(AP_TERM CONJ (BETA_CONV base), sconv step) in
    let STAC = GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
               GEN_TAC THEN DISCH_THEN ASSUME_TAC in
    \A,g. (let s,_,conc = (I # ((check # I) o dest_imp)) (dest_forall g) in
           let (_,[ty;_]) = dest_type(type_of s) in
           let inst = INST_TYPE [ty,":*"] FINITE_INDUCT in
           let sv = genvar (type_of s) in
           let pred = mk_abs(sv,(subst [sv,s] conc)) in
           let spec = SPEC s (UNDISCH (SPEC pred inst)) in
           let beta = GEN s (CONV_RULE (RAND_CONV BETA_CONV) spec) in
           let disc = DISCH (hd(hyp beta)) beta in
           let ithm = CONV_RULE (RATOR_CONV(RAND_CONV conv)) disc in
               (MATCH_MP_TAC ithm THEN CONJ_TAC THENL [ALL_TAC; STAC])(A,g)) ?
          failwith `SET_INDUCT_TAC`;;
