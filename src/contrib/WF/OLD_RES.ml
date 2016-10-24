% ===================================================================== %
% FILE        : compat11.ml						%
% DESCRIPTION : Compatability file for HOL version 11 resolution tools. %
%		Restores: IMP_RES_TAC, IMP_RES_THEN, RES_TAC, RES_THEN  %
%		to the meanings they had in version 1.11.		%
% WARNING     : the version 12 resolution tools are now the standard.	%
% DATE	      : 15 January 1991						%
% COMPILER    : T Melham						%
% NOTE: I've change this than Tom's original by prefixing things with   %
%       OLD                                                             %
% ===================================================================== %

% ===================================================================== %
% Put a theorem 							%
%									%
%	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			%
%									%
% into canonical form for resolution by splitting conjunctions apart	%
% (like IMP_CANON but without the stripping out of quantifiers and only %
% outermost negations being converted to implications).			%
%									%
%        ~t             --->      t ==> F        (at outermost level)	%
%	t1 /\ t2	--->	  t1,   t2				%
%	(t1/\t2)==>t	--->      t1==> (t2==>t)			%
%	(t1\/t2)==>t	--->	  t1==>t, t2==>t			%
%									%
% Modification provided by David Shepherd of Inmos to make resolution 	%
% work with equalities as well as implications. HOL88.1.08, 23 Jun 1989 %
%									%
% The old code is given below:						%
%									%
%   letrec RES_CANON_FUN th =						%
%    let w = concl th in						%
%    if is_conj w 							%
%    then RES_CANON_FUN(CONJUNCT1 th)@RES_CANON_FUN(CONJUNCT2 th)	%
%    else if is_imp w & not(is_neg w) then				%
%	let ante,conc = dest_imp w in					%
%	if is_conj ante then						%
%	    let a,b = dest_conj ante in					%
%	    RES_CANON_FUN 						%
%	    (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))	%
%	else if is_disj ante then					%
%	    let a,b = dest_disj ante in					%
%	    RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @	%
%	    RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))	%
%	else								%
%	map (DISCH ante) (RES_CANON_FUN (UNDISCH th))			%
%    else [th];;							%
% ===================================================================== %

letrec OLD_RES_CANON_FUN th =
    let w = concl th in
    if is_conj w 
    then OLD_RES_CANON_FUN(CONJUNCT1 th)@OLD_RES_CANON_FUN(CONJUNCT2 th)
    else if is_imp w & not(is_neg w) then
        let ante,conc = dest_imp w in
        if is_conj ante then
            let a,b = dest_conj ante in
            OLD_RES_CANON_FUN 
            (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))
        else if is_disj ante then
            let a,b = dest_disj ante in
            OLD_RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @
            OLD_RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))
        else
        map (DISCH ante) (OLD_RES_CANON_FUN (UNDISCH th))
    else if is_eq w then
       let l,r = dest_eq w in
       if (type_of l = ":bool") then
          let (th1,th2) = EQ_IMP_RULE th in
          th . ((OLD_RES_CANON_FUN th1) @ (OLD_RES_CANON_FUN th2))
     % need to keep th as an equality is need to resolve against sometimes ! %
     % [DES] 19jun89 %
       else [th]
       else [th];;

let OLD_RES_CANON th = 
 let vars,w = strip_forall(concl th)
 in
 let th1 = if is_neg w then NOT_ELIM(SPEC_ALL th) else th
 in
 map(GENL vars)(OLD_RES_CANON_FUN(SPEC_ALL th1)) ? failwith `OLD_RES_CANON`;;

% GSPEC --> SPEC_ALL %

let OLD_HOL_PART_MATCH partfn th =
    let pth = SPEC_ALL (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth;;

let OLD_HOL_MATCH_MP impth =
     let match = OLD_HOL_PART_MATCH (fst o dest_imp) impth 
                 ? failwith `OLD_HOL_MATCH_MP` 
     in
     \th. MP (match (concl th)) th;;

% CHOOSE_THEN removed %

let OLD_HOL_STRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN];;

let OLD_HOL_STRIP_ASSUME_TAC =
    (REPEAT_TCL OLD_HOL_STRIP_THM_THEN) CHECK_ASSUME_TAC;;

% ===================================================================== %
% Repeatedly resolve an implication					%
% ===================================================================== %

letrec OLD_HOL_RESOLVE_THEN antel ttac impth : tactic =
    let answers = mapfilter (OLD_HOL_MATCH_MP impth) antel in
    EVERY (mapfilter ttac answers)
    THEN
    (EVERY (mapfilter (OLD_HOL_RESOLVE_THEN antel ttac) answers));;

let OLD_IMP_RES_THEN ttac impth =
 ASSUM_LIST
    (\asl. EVERY (mapfilter (OLD_HOL_RESOLVE_THEN asl ttac) (OLD_RES_CANON impth)));;

let OLD_RES_THEN ttac = 
    ASSUM_LIST (EVERY o (mapfilter (OLD_IMP_RES_THEN ttac)));;

let OLD_IMP_RES_TAC = OLD_IMP_RES_THEN OLD_HOL_STRIP_ASSUME_TAC
and OLD_RES_TAC     = OLD_RES_THEN     OLD_HOL_STRIP_ASSUME_TAC;;



