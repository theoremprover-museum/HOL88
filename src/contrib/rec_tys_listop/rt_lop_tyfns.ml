%=============================================================================%
%                               HOL 88 Version 2.1                            %
%                                                                             %
%     FILE NAME:        rt_lop_tyfns.ml                                       %
%                       (altered tyfns.ml)                                    %
%                                                                             %
%     DESCRIPTION:      Auxiliary programs for recursive types.               %
%     AUTHOR:           T. F. Melham (87.08.23)                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987                                     %
%                                                                             %
%     REVISION HISTORY: 90.06.28                                              %
%                                                                             %
% 23.03.93 - BtG - MODIFIED FOR USE IN DEFINING EXTENDED RECURSIVE TYPES      %
%=============================================================================%

if compiling then loadf `rt_lop_prim_rec`;;

% ===================================================================== %
% STRUCTURAL INDUCTION							%
% ===================================================================== %
begin_section prove_induction_thm;;

% --------------------------------------------------------------------- %
% Internal function: UNIQUENESS						%
%									%
% This function derives uniqueness from unique existence:		%
% 									%
%        |- ?!x. P[x]							%
% --------------------------------------- 				%
%  |- !v1 v2. P[v1] /\ P[v2] ==> (v1=v2)				%
% 									%
% The variables v1 and v2 are genvars.					%
% --------------------------------------------------------------------- %

let UNIQUENESS =
    let EXISTS_UNIQUE_DEF = definition `bool` `EXISTS_UNIQUE_DEF` in
    let P = "P:*->bool" and v1 = genvar ":*" and v2 = genvar ":*" in
    let th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF) in
    let th2 = CONJUNCT2(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1)))) in
    let imp = GEN P (DISCH "$?! ^P" (SPECL [v1;v2] th2)) in
    let AND = let f = "$/\" in \(e1,e2). MK_COMB((AP_TERM f e1),e2) in
    let conv tm = AND ((BETA_CONV # BETA_CONV) (dest_conj tm)) and
        check = assert \c. (fst(dest_const c) = `?!`) and 
        v = genvar ":bool" in
    \th. let _,(x,body) = (check # dest_abs) (dest_comb (concl th)) in
         let ty = type_of x in
         let uniq = MP (SPEC(mk_abs(x,body)) (INST_TYPE [ty,":*"] imp)) th in
	 let V1,V2 = let i = inst [] [ty,":*"] in (i v1,i v2) in
	 let red = conv (fst(dest_imp(concl uniq))) in
	     GEN V1 (GEN V2(SUBST [red,v] (mk_imp(v,mk_eq(V1,V2))) uniq));;

% --------------------------------------------------------------------- %
% Internal function: DEPTH_FORALL_CONV					%
%									%
% DEPTH_FORALL_CONV conv "!x1...xn. tm" applies the conversion conv to  %
% the term tm to yield |- tm = tm', and then returns:			%
%									%
%    |- (!x1...xn. tm)  =  (!x1...xn. tm')				%
%									%
% --------------------------------------------------------------------- %

let DEPTH_FORALL_CONV conv tm = 
    let vs,th = (I # conv) (strip_forall tm) in itlist FORALL_EQ vs th;;

% --------------------------------------------------------------------- %
% Internal function: CONJS_CONV						%
%									%
% CONJS_CONV conv "t1 /\ t2 /\ ... /\ tn" applies conv to each of the   %
% n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the   %
% results.								%
%									%
% --------------------------------------------------------------------- %

letrec CONJS_CONV conv tm = 
       (let c,cs  = (conv # CONJS_CONV conv) (dest_conj tm) in
            MK_COMB((AP_TERM "$/\" c),cs)) ? conv tm;;

% --------------------------------------------------------------------- %
% Internal function: CONJS_SIMP						%
%									%
% CONJS_SIMP conv "t1 /\ t2 /\ ... /\ tn" applies conv to each of the   %
% n conjuncts t1,t2,...,tn.  This should reduce each ti to "T".  I.e.   %
% executing conv ti should return |- ti = T.  The result returned by    %
% CONJS_SIMP is then: |- (t1 /\ t2 /\ ... /\ tn) = T			%
%									%
% --------------------------------------------------------------------- %

let CONJS_SIMP  = 
    let T_AND_T = CONJUNCT1 (SPEC "T" AND_CLAUSES) in
    letrec simp conv tm = 
           (let c,cs  = (conv # simp conv) (dest_conj tm) in
            (MK_COMB((AP_TERM "$/\" c),cs)) TRANS T_AND_T) ? conv tm in
       simp;;

% --------------------------------------------------------------------- %
% Internal function: T_AND_CONV						%
%									%
% T_AND_CONV "T /\ t" returns |- T /\ t = t				%
%									%
% --------------------------------------------------------------------- %

let T_AND_CONV  = 
    let T_AND = GEN_ALL (CONJUNCT1 (SPEC_ALL AND_CLAUSES)) in
    \tm. let t = snd(dest_conj tm) in SPEC t T_AND;;

% --------------------------------------------------------------------- %
% Internal function: GENL_T						%
%									%
% GENL_T [x1;...;xn] returns |- (!x1...xn.T) = T			%
%									%
% --------------------------------------------------------------------- %

let GENL_T l =
    if (null l) then REFL "T" else
       let gen = list_mk_forall(l,"T") in
       let imp1 = DISCH gen (SPECL l (ASSUME gen)) and
           imp2 = DISCH "T" (GENL l (ASSUME "T")) in
           IMP_ANTISYM_RULE imp1 imp2;;
    
% --------------------------------------------------------------------- %
% Internal theorem: EVERY_I_MAP_THM                                     %
%                                                                       %
% Used by EVERY_I_MAP_CONV to prove that a term reduces to T.           %
%                                                                       %
% 06.04.93 - BtG                                                        %
% --------------------------------------------------------------------- %
let EVERY_I_MAP_THM = PROVE
("!l:(*)list. EVERY I (MAP (\x.T)l) = T",
 LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;I_THM;EVERY_DEF]);;

% --------------------------------------------------------------------- %
% Internal function: EVERY_I_MAP_CONV                                   %
%                                                                       %
% Used by SIMP_CONV to prove that a term reduces to T.                  %
%                                                                       %
% 06.04.93 - BtG                                                        %
% --------------------------------------------------------------------- %
let EVERY_I_MAP_CONV tm =
    let lvar = rand(rand tm) in
    let avar = fst(dest_abs(rand(rator(rand tm)))) in
    let sthm = ISPEC lvar EVERY_I_MAP_THM in
    CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
	       (ALPHA_CONV avar)) sthm;;

% --------------------------------------------------------------------- %
% Internal function: SIMP_CONV						%
%									%
% SIMP_CONV is used by prove_induction_thm to simplify to "T" terms of  %
% the following two forms:						%
%									%
%   1: !x1...xn. (\x.T)v = (\x1...xn.T) x1 ... xn			%
%									%
%   2: !x1...xn. (\x.T)v = 						%
%      (\y1...ym x1..xn. (y1 /\.../\ ym) \/ t) ((\x.T)u1)...((\x.T)um)  %
%      					       x1 ... xn		%
%									%
% If tm, a term of one of these two forms, is the argument to SIMP_CONV %
% then the theorem returned is |- tm = T.				%
%                                                                       %
% 06.04.93 - BtG - the second form of term is generalized to:           %
%                                                                       %
%   2: !x1...xn. (\x.T)v =                                              %
%      (\y1...ym ylst x1...xn. (y1 /\.../\ym/\EVERY I ylst) \/ t)       %
%        ((\x.T)u1)...((\x.T))um (MAP(\x.T)ulst) x1 ... xn              %
%                                                                       %
% --------------------------------------------------------------------- %

let SIMP_CONV = 
    let DISJ_SIMP = 
        let v = genvar ":bool" and tr = "T" in
        let T_OR = GEN v (CONJUNCT1 (SPEC v OR_CLAUSES)) in
        \tm. let cs,ds = (dest_disj tm) in
	     let eqn = SYM(CONJS_SIMP (\x.(BETA_CONV x ? EVERY_I_MAP_CONV x)) cs) in
             SUBST [eqn,v] (mk_eq((mk_disj(v,ds)),tr)) (SPEC ds T_OR) in
    let eq = "$=:bool->bool->bool" and T_EQ_T = EQT_INTRO(REFL "T") in
    \tm. let vs,l,r = (I # dest_eq) (strip_forall tm) in
         let rsimp = (LIST_BETA_CONV THENC (DISJ_SIMP ORELSEC REFL)) r and
	     lsimp = AP_TERM eq (BETA_CONV l) and
	     gent  = GENL_T vs in
         let eqsimp = (MK_COMB(lsimp,rsimp)) TRANS T_EQ_T in
	     (itlist FORALL_EQ vs eqsimp) TRANS gent;;

% --------------------------------------------------------------------- %
% Internal theorem: EVERY_I_MAP_P                                       %
%                                                                       %
% Used by EVERY_I_MAP_P_CONV to simplify a term.                        %
%                                                                       %
% 06.04.93 - BtG                                                        %
% --------------------------------------------------------------------- %
let EVERY_I_MAP_P = PROVE
("!(P:*->bool) (l:(*)list). EVERY I (MAP P l) = EVERY P l",
 GEN_TAC THEN LIST_INDUCT_TAC
 THEN ASM_REWRITE_TAC [MAP;I_THM;EVERY_DEF]);;

% --------------------------------------------------------------------- %
% Internal function: EVERY_I_MAP_P_CONV                                 %
%                                                                       %
% Used by HYP_SIMP to prove that a term reduces to T.                  %
%                                                                       %
% 06.04.93 - BtG                                                        %
% --------------------------------------------------------------------- %
let EVERY_I_MAP_P_CONV  = 
  let Every_I,Map = 
      ((I#(fst o strip_comb))o dest_comb o rand o rator o snd o strip_forall
       o concl) EVERY_I_MAP_P in
  \tm.(let everyi,(mp,P),l = (I # (dest_comb#I))((I # dest_comb)(dest_comb tm)) in
       if ((Every_I = everyi) & can (match Map) mp) then
          ISPECL [P;l] EVERY_I_MAP_P
	  else failwith `EVERY_I_MAP_P_CONV: term has wrong form`) ? REFL tm;;

% --------------------------------------------------------------------- %
% Internal function: HYP_SIMP						%
%									%
% HYP_SIMP is used by prove_induction_thm to simplify induction 	%
% hypotheses according to the following scheme:				%
%									%
%   1: !x1...xn. P t = (\x1...xn.T) x1...xn				%
%									%
%         simplifies to    						%
%									%
%      !x1...xn. P t							%
%									%
%   2: !x1...xn. P t = 							%
%         (\y1..ym x1..xn. y1 /\ ... /\ ym) \/ P t) v1 ... vm x1 ... xn %
%									%
%         simplifies to							%
%									%
%      !x1...xn. (v1 /\ ... /\ vm) ==> P t				%
%									%
%                                                                       %
% 06.04.93 - BtG - the second form of term is generalized to:           %
%                                                                       %
%   2: !x1...xn. P t = 							%
%         (\y1..ym ylst x1..xn. y1 /\ ... /\ ym/\EVERY I ylst) \/ P t)  %
%         v1 ... vm (MAP P vlst) x1 ... xn                              %
%									%
%         simplifies to							%
%									%
%      !x1...xn. (v1 /\ ... /\ vm /\ EVERY P vlst) ==> P t		%
%                                                                       %
% --------------------------------------------------------------------- %

let HYP_SIMP = 
    let R_SIMP = 
        let v = genvar ":bool" and tr = "T" in
        let EQ_T = GEN v (CONJUNCT1 (CONJUNCT2 (SPEC v EQ_CLAUSES))) in
        \tm. let l,r = dest_eq tm in
	     if (r = tr) then SPEC l EQ_T else 
	        let cs = fst(dest_disj r) in SPECL [l;cs] OR_IMP_THM in
    let eq = "$=:bool->bool->bool" in
    \tm. let vs,l,r = (I # dest_eq) (strip_forall tm) in
         let eqsimp = AP_TERM (mk_comb(eq,l)) (LIST_BETA_CONV r) in
         let msimp = ((is_disj o rand o rand o concl) eqsimp)
                     => ( CONV_RULE o RAND_CONV o RAND_CONV o RATOR_CONV
			o RAND_CONV o CONJS_CONV) EVERY_I_MAP_P_CONV eqsimp
                      | eqsimp in
	 let rsimp = CONV_RULE (RAND_CONV R_SIMP) msimp in
	     (itlist FORALL_EQ vs rsimp);;

% --------------------------------------------------------------------- %
% Internal function: ANTE_ALL_CONV					%
%									%
% ANTE_ALL_CONV "!x1...xn. P ==> Q" restricts the scope of as many of	%
% the quantified x's as possible to the term Q.  			%
% --------------------------------------------------------------------- %

let ANTE_ALL_CONV tm = 
    let vs,hy,c = (I # dest_imp) (strip_forall tm) in
    let ov,iv = partition (C free_in hy) vs in
    let thm1 = GENL iv (UNDISCH (SPECL vs (ASSUME tm))) in
    let thm2 = GENL ov (DISCH hy thm1) in
    let asm = concl thm2 in
    let thm3 = SPECL iv (UNDISCH (SPECL ov (ASSUME asm))) in
    let thm4 = GENL vs (DISCH hy thm3) in
        IMP_ANTISYM_RULE (DISCH tm thm2) (DISCH asm thm4);;

% --------------------------------------------------------------------- %
% Internal function: CONCL_SIMP						%
%									%
% CONCL_SIMP "\x.T = P" returns: |- (\x.T = P) = (!y. P y) where y is	%
% an appropriately chosen variable.					%
% --------------------------------------------------------------------- %

let CONCL_SIMP = 
    let v = genvar ":bool" in
    let T_EQ = GEN v (CONJUNCT1 (SPEC v EQ_CLAUSES)) in
    \tm. let eq = FUN_EQ_CONV tm in
         let y,ap,bd = (I # dest_eq)(dest_forall(rhs(concl eq))) in
         let eqn = RATOR_CONV(RAND_CONV BETA_CONV) (mk_eq(ap,bd)) and
             simp = SPEC bd T_EQ in
	 eq TRANS (FORALL_EQ y (eqn TRANS simp));;

% --------------------------------------------------------------------- %
% prove_induction_thm: prove a structural induction theorem from a type %
% axiom of the form returned by define_type.				%
%									%
% EXAMPLE: 								%
%									%
% Input: 								%
% 									%
%    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	%
% 									%
% Output:								%
% 									%
%    |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	%
% 									%
% 06.04.93 - BtG - altered to accept (recursive type)list arguments.    %
%                                                                       %
% --------------------------------------------------------------------- %

let prove_induction_thm = 
    letrec gen n = if (n=0) then [] else (genvar ":bool" . gen (n-1)) in
    letrec genl n = if (n=0) then [] else (genvar ":(bool)list" . genl (n-1)) in
    let mk_fn P ty tm = 
        let body = snd(strip_forall tm) in
        let c,args = (rand # (snd o strip_comb))(dest_eq body) in
        let vars = filter is_var args in
        let n = length(filter (\t.type_of t = ty) vars) in
        let nl = length(filter (\t.type_of t = ":(^ty)list") vars) in
	if ((n=0) & (nl=0)) then list_mk_abs (vars, "T") else
  	    let bools = gen n in
            let lvars = genl nl in
            let lbools = map (curry mk_comb "EVERY I") lvars in
	    let term = mk_disj (list_mk_conj (bools@lbools),mk_comb(P,c)) in
		list_mk_abs((bools @ lvars @ vars),term) in
    let LCONV = RATOR_CONV o RAND_CONV in
    let conv1 = LCONV(CONJS_SIMP SIMP_CONV) THENC T_AND_CONV and
        conv2 = CONJS_CONV (HYP_SIMP THENC TRY_CONV ANTE_ALL_CONV) in
    \th. (let fn,body = dest_abs(rand(snd(strip_forall(concl th)))) in
          let [ty;rty] = snd(dest_type (type_of fn)) in
          let inst = INST_TYPE [":bool",rty] th in
          let P = mk_primed_var(`P`,mk_type(`fun`,[ty;":bool"])) and
	      v = genvar ty and cases = conjuncts body in
          let uniq = let vs,tm = strip_forall(concl inst) in
	             let thm = UNIQUENESS(SPECL vs inst) in
                     GENL vs (SPECL [mk_abs(v,"T");P] thm) in
          let spec = SPECL (map (mk_fn P ty) cases) uniq in
          let simp =  CONV_RULE (LCONV(conv1 THENC conv2)) spec in
	      GEN P (CONV_RULE (RAND_CONV CONCL_SIMP) simp)) ? 
	  failwith `prove_induction_thm`;;

% --------------------------------------------------------------------- %
% Bind the function prove_induction_thm to "it", so as to export it 	%
% outside the current section.						%
% --------------------------------------------------------------------- %
prove_induction_thm;; 

end_section prove_induction_thm;;

% --------------------------------------------------------------------- %
% Save the exported value of prove_induction_thm.			%
% --------------------------------------------------------------------- %
let prove_induction_thm = it;;

% ===================================================================== %
% CASES FOR RECURSIVE TYPES						%
% ===================================================================== %
begin_section prove_cases_thm;;

% --------------------------------------------------------------------- %
% Internal function: NOT_ALL_THENC					%
%									%
% This conversion first moves negation inwards through an arbitrary	%
% number of nested universal quantifiers. It then applies the supplied	%
% conversion to the resulting inner negation.  For example if:		%
%									%
%	conv "~tm" ---> |- ~tm = tm'					%
% then									%
%									%
%       NOT_ALL_THENC conv "~(!x1 ... xn. tm)"				%
%									%
% yields:								%
%									%
%       |- ~(!x1...xn.tm) = ?x1...xn.tm'				%
% --------------------------------------------------------------------- %

letrec NOT_ALL_THENC conv tm = 
       (NOT_FORALL_CONV THENC (RAND_CONV (ABS_CONV (NOT_ALL_THENC conv)))) tm
       ? (conv tm);;

% --------------------------------------------------------------------- %
% Internal function: BASE_CONV						%
%									%
% This conversion does the following simplification:			%
%									%
%    BASE_CONV "~((\x.~tm)y)"  --->  |- ~((\x.~tm)y) = tm[y/x]		%
%									%
% --------------------------------------------------------------------- %

let BASE_CONV = 
    let NOT_NOT = CONJUNCT1 NOT_CLAUSES and neg = "$~" in
    \tm. let beta = BETA_CONV (dest_neg tm) in
    	 let simp = SPEC (rand(rhs(concl beta))) NOT_NOT in
    	     TRANS (AP_TERM neg beta) simp;;

% --------------------------------------------------------------------- %
% Internal function: STEP_CONV						%
%									%
% This conversion does the following simplification:			%
%									%
%    STEP_CONV "~(tm' ==> !x1..xn.(\x.~tm)z"  				%
%									%
% yields:								%
%									%
%   |- ~(tm' ==> !x1..xn.(\x.~tm)z = tm' /\ ?x1..xn.tm[z/x]  		%
% --------------------------------------------------------------------- %

let STEP_CONV = 
    let v1 = genvar ":bool" and v2 = genvar ":bool" in
    \tm. let a,c = dest_imp(dest_neg tm) in
         let th1 = SPEC c (SPEC a NOT_IMP) in
	 let simp = NOT_ALL_THENC BASE_CONV (mk_neg c) in
	     SUBST [simp,v2] (mk_eq(tm,mk_conj(a,v2))) th1;;

% --------------------------------------------------------------------- %
% Internal function: NOT_IN_CONV					%
%									%
% This first conversion moves negation inwards through conjunction and	%
% universal quantification:						%
%									%
%   NOT_IN_CONV  "~(!x1..xn.c1 /\ ... /\ !x1..xm.cn)"			%
%									%
% to transform the input term into:					%
%									%
%   ?x1..xn.~c1 \/ ... \/ ?x1..xm.~cn					%
%									%
% It then applies either BASE_CONV or STEP_CONV to each subterm ~ci.	%
% --------------------------------------------------------------------- %

let NOT_IN_CONV = 
    let DE_MORG = GEN_ALL(CONJUNCT1(SPEC_ALL DE_MORGAN_THM)) and
        cnv = BASE_CONV ORELSEC STEP_CONV and
        v1 = genvar ":bool" and v2 = genvar ":bool" in
    letrec conv tm = 
        (let c,cs = dest_conj(dest_neg tm) in
	 let thm = SPEC cs (SPEC c DE_MORG) in
	 let cth = NOT_ALL_THENC cnv (mk_neg c) and 
	     csth = conv (mk_neg cs) in
	     SUBST [cth,v1;csth,v2] (mk_eq(tm,(mk_disj(v1,v2)))) thm) ? 
	NOT_ALL_THENC cnv tm in
    conv;;

% --------------------------------------------------------------------- %
% Internal function: STEP_SIMP						%
%									%
% This rule does the following simplification:				%
%									%
%    STEP_RULE "?x1..xi. tm1 /\ ?xj..xn. tm2"				%
%									%
% yields:								%
%									%
%   ?x1..xi.tm1 /\ ?xj..xn.tm2 |- ?x1..xn.tm2				%
%									%
% For input terms of other forms, the rule yields:			%
%									%
%   STEP_RULE "tm" ---> tm |- tm					%
% --------------------------------------------------------------------- %

let STEP_SIMP = 
    let EX tm th = EXISTS (mk_exists(tm,concl th),tm) th and
        CH tm th = CHOOSE (tm,ASSUME (mk_exists(tm,hd(hyp th)))) th in
    \tm. (let vs,body = strip_exists tm in
              itlist (\t.CH t o EX t) vs (CONJUNCT2 (ASSUME body))) ? 
 	      ASSUME tm;;

% --------------------------------------------------------------------- %
% Internal function: DISJ_CHAIN						%
%									%
% Suppose that 								%
%									%
%    rule "tmi"  --->   tmi |- tmi'		(for 1 <= i <= n)	%
%									%
% then:									%
%									%
%       |- tm1 \/ ... \/ tmn						%
%    ---------------------------   DISJ_CHAIN rule			%
%      |- tm1' \/ ... \/ tmn' 						%
% --------------------------------------------------------------------- %

letrec DISJS_CHAIN rule th = 
       (let d1,d2 = dest_disj(concl th) in
        let i1 = rule d1 and i2 = DISJS_CHAIN rule (ASSUME d2) in
        DISJ_CASES th (DISJ1 i1 (concl i2)) (DISJ2 (concl i1) i2)) ? 
       MP (DISCH (concl th) (rule (concl th))) th;;

% --------------------------------------------------------------------- %
% prove_cases_thm: prove a cases or "exhaustion" theorem for a concrete %
% recursive type from a structural induction theorem of the form 	%
% returned by prove_induction_thm.					%
%									%
% EXAMPLE: 								%
%									%
% Input: 								%
% 									%
%    |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	%
% 									%
% Output:								%
% 									%
%    |- !l. (l = []) \/ (?t h. l = CONS h t)				%
% 									%
% --------------------------------------------------------------------- %

let prove_cases_thm th = 
    (let x,P = dest_forall(snd(dest_imp(snd(dest_forall(concl th))))) in
     let v = genvar (type_of x) in
     let pred = mk_abs(v,mk_neg(mk_eq(x,v))) in
     let th1 = CONV_RULE BETA_CONV (SPEC x (UNDISCH(SPEC pred th))) in
     let th2 = NOT_INTRO (DISCH_ALL (MP th1 (REFL x))) in
     let th3 = CONV_RULE NOT_IN_CONV th2 in
         GEN x (DISJS_CHAIN STEP_SIMP th3)) ? 
     failwith `prove_cases_thm: invalid input theorem`;;

% --------------------------------------------------------------------- %
% Bind the function prove_cases_thm to "it", so as to export it 	%
% outside the current section.						%
% --------------------------------------------------------------------- %
prove_cases_thm;; 

end_section prove_cases_thm;;

% --------------------------------------------------------------------- %
% Save the exported value of prove_cases_thm.				%
% --------------------------------------------------------------------- %
let prove_cases_thm = it;;

% ===================================================================== %
% PROOF THAT CONSTRUCTORS OF RECURSIVE TYPES ARE ONE-TO-ONE		%
% ===================================================================== %
begin_section prove_constructors_one_one;;

% --------------------------------------------------------------------- %
% Internal function: PAIR_EQ_CONV 					%
%									%
% A call to PAIR_EQ_CONV "(x1,...,xn) = (y1,...,yn)" returns:		%
%									%
%   |- ((x1,...,xn) = (y1,...,yn)) = (x1 = y1) /\ ... /\ (xn = yn)	%
% 									%
% --------------------------------------------------------------------- %

let PAIR_EQ_CONV = 
    let v = genvar ":bool" in
    letrec conv tm = 
           (let (x,xs),(y,ys) = (dest_pair # dest_pair) (dest_eq tm) in
            let xty = type_of x and xsty = type_of xs in
            let thm = INST_TYPE [xty,":*";xsty,":**"] PAIR_EQ in
            let spec = SPEC ys (SPEC y (SPEC xs (SPEC x thm))) in
            let reqn = conv (mk_eq(xs,ys)) in
            let pat = mk_eq(tm,mk_conj(mk_eq(x,y),v)) in
	    SUBST [reqn,v] pat spec) ? REFL tm in conv;;

% --------------------------------------------------------------------- %
% Internal function: list_variant					%
%									%
% makes variants of the variables in l2 such that they are all not in	%
% l1 and are all different.						%
% --------------------------------------------------------------------- %
letrec list_variant l1 l2 = 
       if (null l2) then [] else
           (let v = variant l1 (hd l2) in
	     (v.list_variant (v.l1) (tl l2)));;

% --------------------------------------------------------------------- %
% Internal function: prove_const_one_one.				%
%									%
% This function proves that a single constructor of a recursive type is	%
% one-to-one (it is called once for each appropriate constructor).  The %
% theorem input, th, is the characterizing theorem for the recursive 	%
% type in question.  The term, tm, is the defining equation for the 	%
% constructor in question, taken from the mody of the theorem th.	%
%									%
% For example, if:							%
%									%
%  th = |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t)	%
%									%
% and									%
%									%
%  tm = "!h t. fn(CONS h t) = f(fn t)h t"				%
%									%
% then prove_const_one_one th tm yields:				%
%								 	%
%  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	%
%									%
% --------------------------------------------------------------------- %

let prove_const_one_one th tm = 
    let vs,l,r = (I # dest_eq)(strip_forall tm) in
    let tup = end_itlist (curry mk_pair) (snd(strip_comb(rand l))) in
    let tupty = type_of tup in
    let eq = mk_eq(inst [] [tupty,type_of l] l, tup) in
    let eqn = prove_rec_fn_exists th eq in
    let vvs = list_variant vs vs in
    let C = rand l and C' = subst (combine (vvs,vs)) (rand l) in
    let vareqs = (list_mk_conj o (map mk_eq))
		 (combine (snd(strip_comb C),(snd(strip_comb C')))) in
    let asms = combine(CONJUNCTS (ASSUME vareqs),snd(strip_comb C)) in
    let imp1 = DISCH vareqs (SUBST_CONV asms C C) in
    let fn,fndef = (I # ASSUME) (dest_exists(concl eqn)) in
    let r1 = REWR_CONV fndef (mk_comb(fn,C)) and
        r2 = REWR_CONV fndef (mk_comb(fn,C')) and
        asm = AP_TERM fn (ASSUME (mk_eq(C,C'))) and
	v1 = genvar tupty and v2 = genvar tupty in
    let thm = (SUBST [r1,v1;r2,v2] (mk_eq(v1,v2)) asm) in
    let aimp = DISCH (mk_eq(C,C')) (CONV_RULE PAIR_EQ_CONV thm) in
    let imp2 = CHOOSE (fn,eqn) aimp in
        GENL vs (GENL vvs (IMP_ANTISYM_RULE imp2 imp1)) ;;

% --------------------------------------------------------------------- %
% prove_constructors_one_one : prove that the constructors of a given	%
% concrete recursive type are one-to-one. The input is a theorem of the %
% form returned by define_type.						%
%									%
% EXAMPLE: 								%
%									%
% Input: 								%
% 									%
%    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	%
%									%
% Output:								%
%									%
%    |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	%
% --------------------------------------------------------------------- %

let prove_constructors_one_one th = 
   (let eqns = conjuncts(snd(dest_abs(rand(snd(strip_forall(concl th)))))) in
    let funs = filter (\tm.is_comb(rand(lhs(snd(strip_forall tm))))) eqns in
        LIST_CONJ (map (prove_const_one_one th) funs)) ?
    failwith `prove_constructors_one_one: invalid input theorem`;;

% --------------------------------------------------------------------- %
% Bind the function prove_constructors_one_one to "it", so as to export %
% it outside the current section.					%
% --------------------------------------------------------------------- %
prove_constructors_one_one;; 

end_section prove_constructors_one_one;;

% --------------------------------------------------------------------- %
% Save the exported value of prove_constructors_one_one.		%
% --------------------------------------------------------------------- %
let prove_constructors_one_one = it;;

% ===================================================================== %
% DISTINCTNESS OF VALUES FOR EACH CONSTRUCTOR				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% prove_constructors_distinct : prove that the constructors of a given	%
% recursive type yield distict (non-equal) values.			%
%									%
% EXAMPLE: 								%
%									%
% Input: 								%
% 									%
%    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	%
% 									%
% Output:								%
% 									%
%    |- !h t. ~([] = CONS h t)						%
% --------------------------------------------------------------------- %

let prove_constructors_distinct = 
    let NOT_SUC = theorem `num` `NOT_SUC` and
        INV_SUC = theorem `num` `INV_SUC` in
    letrec list_variant l1 l2 = 
           if (null l2) then [] else
               (let v = variant l1 (hd l2) in
    	         (v.list_variant (v.l1) (tl l2))) in
    let SUC = "SUC" and zero = "0" and
        lemma = GEN_ALL(NOT_ELIM(NOT_EQ_SYM(SPEC_ALL NOT_SUC))) in
    letrec geneqs ls t = 
       let vars,l,r = (I # dest_eq) (strip_forall(hd ls)) in
       if (null(tl ls)) then [],mk_eq(l,t) else
          let rl,tm = geneqs(tl ls) (mk_comb(SUC,t)) in
	  ((t.rl), mk_conj (mk_eq(l,t),tm)) in
    letrec step ths = 
       if (null (tl ths)) then [] else
       let [l;r] = snd(strip_comb(fst(dest_imp(concl (hd ths))))) in
       let th = IMP_TRANS (SPEC r (SPEC l INV_SUC)) (hd ths) in
           th. (step (tl ths)) in
    letrec mk_rot ths = 
           if (null ths) then [] else ths. mk_rot (step ths) in
    let rule fn eth th = 
	let asm = (mk_eq o (rand # rand))(dest_eq(fst(dest_imp(concl th)))) in
	let imp = (IMP_TRANS (DISCH asm (AP_TERM fn (ASSUME asm))) th) in
            GEN_ALL (NOT_INTRO(CHOOSE (fn,eth) imp)) in
    let gv1 = genvar ":num" and gv2 = genvar ":num" in
    let pat = mk_imp(mk_eq(gv1,gv2),"F") in
    letrec subsfn rul eq eqs l acc = 
    	   if (null l) then acc else
	   let vs = frees (rand(rhs(concl eq))) and
	       nvs = frees (rand(rhs(concl(hd eqs)))) in
	   let eqn = INST (combine ((list_variant vs nvs),nvs)) (hd eqs) in
	   let rnum = rhs(fst(dest_imp(concl (hd l)))) in
	   let thm = SUBST [eq,gv1;eqn,gv2] pat (hd l) in 
	       (rul thm).(subsfn rul eq (tl eqs) (tl l) acc) in
    letrec subs rul (eq.eqs) eqls = 
           null eqls => [] | 
	   	subsfn rul eq eqs (hd eqls) (subs rul eqs (tl eqls)) in
    \th. (let fn,body = dest_abs(rand(snd(strip_forall(concl th)))) in
          let _,[_;ty] = dest_type(type_of fn) in
          let eqns = conjuncts(inst [] [mk_type(`num`,[]),ty] body) in
          if (null(tl eqns)) then fail else 
          let nums,eqs = (geneqs eqns zero) in
          let eth = prove_rec_fn_exists th eqs in
          let rots = mk_rot (map (C SPEC lemma) nums) in
 	  let fn,asm = dest_exists(concl eth) in
          let fneqs = map (SYM o SPEC_ALL) (CONJUNCTS (ASSUME asm)) in
               LIST_CONJ (subs (rule fn eth) fneqs rots)) ?
              failwith `prove_constructors_distinct: invalid input`;;
