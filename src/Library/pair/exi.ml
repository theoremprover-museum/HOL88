% --------------------------------------------------------------------- %
% 		Copyright (c) Jim Grundy 1992				%
%               All rights reserved                                     %
%									%
% Jim Grundy, hereafter referred to as `the Author', retains the	%
% copyright and all other legal rights to the Software contained in	%
% this file, hereafter referred to as `the Software'.			%
% 									%
% The Software is made available free of charge on an `as is' basis.	%
% No guarantee, either express or implied, of maintenance, reliability	%
% or suitability for any purpose is made by the Author.			%
% 									%
% The user is granted the right to make personal or internal use	%
% of the Software provided that both:					%
% 1. The Software is not used for commercial gain.			%
% 2. The user shall not hold the Author liable for any consequences	%
%    arising from use of the Software.					%
% 									%
% The user is granted the right to further distribute the Software	%
% provided that both:							%
% 1. The Software and this statement of rights is not modified.		%
% 2. The Software does not form part or the whole of a system 		%
%    distributed for commercial gain.					%
% 									%
% The user is granted the right to modify the Software for personal or	%
% internal use provided that all of the following conditions are	%
% observed:								%
% 1. The user does not distribute the modified software. 		%
% 2. The modified software is not used for commercial gain.		%
% 3. The Author retains all rights to the modified software.		%
%									%
% Anyone seeking a licence to use this software for commercial purposes	%
% is invited to contact the Author.					%
% --------------------------------------------------------------------- %
% CONTENTS: functions for paired existential quantifications.           %
% --------------------------------------------------------------------- %
%$Id: exi.ml,v 3.2 1994/01/28 02:56:50 jug Exp $%

% ------------------------------------------------------------------------- %
% PEXISTS_CONV "(?p. t[p])" = (|- (?p. t[p]) = (t [@p. t[p]])               %
% ------------------------------------------------------------------------- %

let PEXISTS_CONV =
    let EXISTS_THM =
        let f = "f:*->bool" in
        let th = AP_THM EXISTS_DEF f in
                GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) th) in
    (\tm.
        let g = mk_pabs (dest_pexists tm) in
        let th1 = ISPEC g EXISTS_THM in
        let th2 = PBETA_CONV (rhs (concl th1)) in
            th1 TRANS th2
    ) ? failwith `PEXISTS_CONV` ;;

% ------------------------------------------------------------------------- %
%    A |- ?p. t[p]                                                          %
% ------------------ PSELECT_RULE                                           %
%  A |- t[@p .t[p]]                                                         %
% ------------------------------------------------------------------------- %

let PSELECT_RULE = CONV_RULE PEXISTS_CONV ;;

% ------------------------------------------------------------------------- %
% PSELECT_CONV "t [@p. t[p]]" = (|- (t [@p. t[p]]) = (?p. t[p]))            %
% ------------------------------------------------------------------------- %

let PSELECT_CONV tm =
    (let right t =
	((is_pselect t) &
	paconv tm (rhs (concl (PBETA_CONV (mk_comb ((rand t), t))))))
    in
	let exi = mk_pexists (dest_pselect (find_term right tm)) in
	let th1 = SYM (PEXISTS_CONV exi) in
	let th2 = PALPHA tm (lhs(concl th1)) in
	    th2 TRANS th1
    ) ? failwith `PSELECT_CONV` ;;

% ------------------------------------------------------------------------- %
%  A |- t[@p .t[p]]                                                         %
% ------------------ PEXISTS_RULE                                           %
%    A |- ?p. t[p]                                                          %
% ------------------------------------------------------------------------- %

let PEXISTS_RULE = CONV_RULE PSELECT_CONV ;;

% ------------------------------------------------------------------------- %
%    A |- P t                                                               %
% -------------- PSELECT_INTRO                                              %
%  A |- P($@ P)                                                             %
% ------------------------------------------------------------------------- %

let PSELECT_INTRO = SELECT_INTRO ;;

% ------------------------------------------------------------------------- %
%  A1 |- f($@ f)  ,  A2, f p |- t                                           %
% -------------------------------- PSELECT_ELIM th1 ("p", th2) [p not free] %
%          A1 u A2 |- t                                                     %
% ------------------------------------------------------------------------- %

let PSELECT_ELIM th1 (v,th2) =
    (let (f,sf) = dest_comb (concl th1) in
	let t1 = MP (PSPEC sf (PGEN v (DISCH (mk_comb(f,v)) th2))) th1 in
	let t2 = ALPHA (concl t1) (concl th2) in
	    EQ_MP t2 t1
    ) ? failwith `PSELECT_ELIM` ;;

% ------------------------------------------------------------------------- %
%  A |- t[q]                                                                %
% ----------------- PEXISTS ("?p. t[p]", "q")                               %
%  A |- ?p. t[p]                                                            %
% ------------------------------------------------------------------------- %

let PEXISTS (fm,tm) th =
    (let (p,b) = dest_pexists fm in
    let th1 = PBETA_CONV (mk_comb(mk_pabs(p,b),tm)) in
    let th2 = EQ_MP (SYM th1) th in
    let th3 = PSELECT_INTRO th2 in
    let th4 = AP_THM
		(INST_TYPE [(type_of p, mk_vartype `*`)] EXISTS_DEF)
		(mk_pabs (p, b)) in
    let th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4)))) in
	EQ_MP (SYM th5) th3
    ) ? failwith `PEXISTS` ;;

% ------------------------------------------------------------------------- %
%  A1 |- ?p. t[p]  ,  A2, t[v] |- u                                         %
% ---------------------------------- PCHOOSE (v,th1) th2 [v not free]       %
%             A1 u A2 |- u                                                  %
% ------------------------------------------------------------------------- %

let PCHOOSE =
    let f = "f:*->bool" in
    let t1 = AP_THM EXISTS_DEF f in
    let t2 = GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) t1) in
    \(v,th1) th2.
	(
	    let p = rand (concl th1) in
	    let bet = PBETA_CONV (mk_comb(p,v)) in
	    if not(mem (rhs (concl bet)) (hyp th2)) then
		failwith `theorems not in the correct form`
	    else
	    let th1' = EQ_MP (ISPEC p t2) th1 in
	    let u1 = UNDISCH (fst (EQ_IMP_RULE bet)) in
	    let th2' = PROVE_HYP u1 th2 in
		PSELECT_ELIM th1' (v,th2')
	) ?\s failwith (`PCHOOSE: `^s);;

let P_PCHOOSE_THEN v ttac pth :tactic =
    let (p,b) = dest_pexists (concl pth) ? failwith `P_PCHOOSE_THEN` in
	\(asl,w).
	    let th =
		itlist
		    ADD_ASSUM
		    (hyp pth)
		    (ASSUME
			(rhs (concl (PBETA_CONV (mk_comb(mk_pabs(p,b), v))))))
	    in
	    let (gl,prf) = ttac th (asl,w) in
		(gl, (PCHOOSE (v, pth)) o prf) ;;

let PCHOOSE_THEN ttac pth :tactic =
    let (p,b) = dest_pexists (concl pth) ? failwith `CHOOSE_THEN` in
	\(asl,w).
	    let q = pvariant ((thm_frees pth) @ (freesl (w.asl))) p in
	    let th =
		itlist
		    ADD_ASSUM
		    (hyp pth)
		    (ASSUME
			(rhs
			    (concl
				(PAIRED_BETA_CONV (mk_comb(mk_pabs(p,b), q))))))
	    in
	    let (gl,prf) = ttac th (asl,w) in
		(gl, (PCHOOSE (q, pth)) o prf) ;;

let P_PCHOOSE_TAC p = P_PCHOOSE_THEN p ASSUME_TAC ;;

let PCHOOSE_TAC = PCHOOSE_THEN ASSUME_TAC ;;

% ------------------------------------------------------------------------- %
%  A ?- ?p. t[p]                                                            %
% =============== PEXISTS_TAC "u"                                           %
%    A ?- t[u]                                                              %
% ------------------------------------------------------------------------- %

let PEXISTS_TAC v :tactic (a, t) =
    (let (p,b) = dest_pexists t in
	([a, rhs (concl (PBETA_CONV (mk_comb((mk_pabs (p,b)),v))))],
	 \[th]. PEXISTS (t,v) th)
    ) ? failwith `PEXISTS_TAC` ;;

% ------------------------------------------------------------------------- %
%  |- ?!p. t[p]                                                             %
% -------------- PEXISTENCE                                                 %
%  |- ?p. t[p]                                                              %
% ------------------------------------------------------------------------- %

let PEXISTENCE th =
    (let (p,b) = dest_pabs (rand (concl th)) in
    let th1 =
	AP_THM
	    (INST_TYPE [(type_of p, mk_vartype `*`)] EXISTS_UNIQUE_DEF)
	    (mk_pabs(p,b)) in
    let th2 = EQ_MP th1 th in
    let th3 = CONV_RULE BETA_CONV th2 in
	CONJUNCT1 th3 
    ) ? failwith `PEXISTENCE` ;;
    
% ------------------------------------------------------------------------- %
% PEXISTS_UNIQUE_CONV "?!p. t[p]" =                                         %
%   (|- (?!p. t[p]) = (?p. t[p] /\ !p p'. t[p] /\ t[p'] ==> (p='p)))        %
% ------------------------------------------------------------------------- %

let PEXISTS_UNIQUE_CONV tm =
    (let (p,b) = dest_pabs (rand tm) in
    let p' = pvariant (p.(frees tm)) p in
    let th1 =
	AP_THM
	    (INST_TYPE [(type_of p, mk_vartype `*`)] EXISTS_UNIQUE_DEF)
	    (mk_pabs(p,b)) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) th1 in
    let th3 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (ABS_CONV 
		(GEN_PALPHA_CONV p'))))) th2 in
    let th4 = CONV_RULE (RAND_CONV (RAND_CONV (GEN_PALPHA_CONV p))) th3 in
    let th5 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		(RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		(RATOR_CONV (RAND_CONV PBETA_CONV)))))))))) th4 in
	CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
	    (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV PBETA_CONV))))))))) th5
    ) ? failwith `PEXISTS_UNIQUE_CONV` ;;

% ------------------------------------------------------------------------- %
% P_PSKOLEM_CONV : introduce a skolem function.                             %
%                                                                           %
%   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      %
%        =                                                                  %
%      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]                              %
%                                                                           %
% The first argument is the function f.                                     %
% ------------------------------------------------------------------------- %

begin_section skolemsec ;;

    let BABY_P_PSKOLEM_CONV f =
	if (not(is_pvar f)) then
	    failwith `P_SKOLEM_CONV: first argument not a variable`
	else
	    \tm.
	    (
		let (xs,(y,P)) = (I # dest_exists) (strip_pforall tm) in
		let fx = list_mk_comb(f,xs) ?
		    failwith `function variable has the wrong type` in
		if (free_in f tm) then
		    failwith `skolem function free in the input term`
		else
		    let pat =
			mk_exists(f,(list_mk_pforall(xs,subst [(fx,y)] P))) in
		    let fn = list_mk_pabs(xs,mk_select(y,P)) in
		    let bth = SYM(LIST_PBETA_CONV (list_mk_comb(fn,xs))) in
		    let thm1 =
			SUBST [bth,y] P (SELECT_RULE (PSPECL xs (ASSUME tm))) in
		    let imp1 = DISCH tm (EXISTS (pat,fn) (PGENL xs thm1)) in
		    let thm2 = PSPECL xs (ASSUME (snd(dest_exists pat))) in
		    let thm3 = PGENL xs (EXISTS (mk_exists(y,P),fx) thm2) in
		    let imp2 = DISCH pat (CHOOSE (f,ASSUME pat) thm3) in
			IMP_ANTISYM_RULE imp1 imp2
	    );;


    letrec P_PSKOLEM_CONV f =
	if (not (is_pvar f)) then
	    failwith `P_SKOLEM_CONV: first argument not a variable pair`
	else
	    \tm.
	    (
		let (xs,(y,P)) = (I # dest_pexists) (strip_pforall tm) ?
		    failwith `expecting "!x1...xn. ?y.tm"` in
		let FORALL_CONV =
		     (end_itlist
			(curry $o)
			(map (K (RAND_CONV o PABS_CONV)) xs)
		     )? failwith `expecting "!x1...xn. ?y.tm"`in
		if is_var f then
		    if is_var y then
			BABY_P_PSKOLEM_CONV f tm
		    else % is_pair y %
			let y' = genvar (type_of y) in
			let tha1 =
			    (FORALL_CONV (RAND_CONV (PALPHA_CONV y'))) tm
			in
			    CONV_RULE (RAND_CONV (BABY_P_PSKOLEM_CONV f)) tha1
		else % is_par f %
		    let (f1,f2) = dest_pair f in
		    let thb1 = 
			if is_var y then
			    let (y1',y2') =
				(genvar # genvar) (dest_prod (type_of y)) ?
				failwith `existential variable not of pair type`
			    in
				(FORALL_CONV
				    (RAND_CONV
					(PALPHA_CONV (mk_pair(y1',y2')))))
				tm
			else
			    REFL tm in
		    let thb2 =
			CONV_RULE
			    (RAND_CONV (FORALL_CONV CURRY_EXISTS_CONV))
			    thb1 in
		    let thb3 = CONV_RULE (RAND_CONV (P_PSKOLEM_CONV f1)) thb2 in
		    let thb4 =
			CONV_RULE
			    (RAND_CONV
				(RAND_CONV (PABS_CONV (P_PSKOLEM_CONV f2))))
			    thb3 in
			CONV_RULE (RAND_CONV UNCURRY_EXISTS_CONV) thb4
	    ) ?\st failwith `P_PSKOLEM_CONV: ` ^st;;

    P_PSKOLEM_CONV;;
end_section skolemsec;;
let P_PSKOLEM_CONV = it;;

% ------------------------------------------------------------------------- %
% PSKOLEM_CONV : introduce a skolem function.                               %
%                                                                           %
%   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      %
%        =                                                                  %
%      (?y'. !x1...xn. tm[x1,..,xn,f x1 ... xn]                             %
%                                                                           %
% Where y' is a primed variant of y not free in the input term.             %
% ------------------------------------------------------------------------- %

let PSKOLEM_CONV =
    letrec mkfn tm tyl =
	if is_var tm then
	    let (n,t) = dest_var tm in
		mk_var(n, itlist (\ty1 ty2. mk_type(`fun`,[ty1;ty2])) tyl t)
	else
	    let (p1,p2) = dest_pair tm in
		mk_pair(mkfn p1 tyl, mkfn p2 tyl)
    in
	\tm.
	(
	    let (xs,(y,P)) = (I # dest_pexists) (strip_pforall tm) in
	    let f = mkfn y (map type_of xs) in
	    let f' = pvariant (frees tm) f in
		P_PSKOLEM_CONV f' tm 
	) ? failwith `PSKOLEM_CONV: expecting "!x1...xn. ?y.tm"`;;
