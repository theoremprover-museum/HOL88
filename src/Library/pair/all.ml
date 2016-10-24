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
% CONTENTS: functions for dealing with paired universal quantification. %
% --------------------------------------------------------------------- %
%$Id: all.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% ------------------------------------------------------------------------- %
% Paired Specialisation:                                                    %
%    A |- !p.t                                                              %
%  ------------- PSPEC c [where c is free for p in t]                       %
%   A |- t[c/p]                                                             %
% ------------------------------------------------------------------------- %
	    
let PSPEC =
    let spec_thm =
	prove
	(
	    "!(x:*) f. $!f ==> (f x)"
	,
	    GEN_TAC THEN
	    GEN_TAC THEN
	    (PURE_ONCE_REWRITE_TAC [FORALL_DEF]) THEN
	    BETA_TAC THEN
	    DISCH_TAC THEN
	    (PURE_ASM_REWRITE_TAC []) THEN
	    BETA_TAC
	) in
    let gxty = ":*" in
    let gfty = ":* -> bool" in
    let gx = genvar gxty in
    let gf = genvar gfty in
    let sth = ISPECL [gx;gf] spec_thm in
    \x th.
	(let f = rand (concl th) in
	let xty = type_of x
	and fty = type_of f in
	let gxinst = mk_var(fst (dest_var gx), xty) 
	and gfinst = mk_var(fst (dest_var gf), fty) in
	    (CONV_RULE PBETA_CONV)
	    (MP (INST_TY_TERM ([(x,gxinst);(f,gfinst)],[(xty,gxty)]) sth) th)
	) ? failwith `PSPEC`;;

let PSPECL xl th = rev_itlist PSPEC xl th;;

let IPSPEC x th =
    let (p,tm) = dest_pforall(concl th) ?
		failwith `IPSPEC: input theorem not universally quantified` in
    let (_,inst) = match p x ?
		failwith `IPSPEC: can't type-instantiate input theorem` in
	(PSPEC x (INST_TYPE inst th) ?
		failwith `IPSPEC: type variable free in assumptions`);;

let IPSPECL =
    let tup = end_itlist (curry mk_pair) in
    letrec strip l =
	if null l then
	    K []
	else
	    ($.) o (I # strip (tl l)) o dest_pforall
    in
	\xl.
	    if (null xl) then
		I
	    else
		let tupxl = tup xl in
		let striper = strip xl in
		    \th.let pl = striper (concl th) ?
			failwith `IPSPECL:list of terms too long for theorem` in
			let (_,inst) = match (tup pl) tupxl ?
			failwith `IPSPECL: can't type-instantiate input theorem`
			in
			    (PSPECL xl (INST_TYPE inst th) ?
			    failwith
				`IPSPECL: type variable free in assumptions`);;

let PSPEC_PAIR th =
    let (p,_) = dest_pforall (concl th) in
    let p' = pvariant (freesl (hyp th)) p in
	(p', PSPEC p' th) ;;

let PSPEC_ALL =
    let f p (ps,l) = let p' = pvariant ps p in ((frees p')@ps,p'.l) in
    \th. let (hxs,con) = (freesl # I) (dest_thm th) in
	 let fxs = frees con
	 and pairs = fst(strip_pforall con) in
	    PSPECL (snd(itlist f pairs (hxs @ fxs,[]))) th;;

letrec GPSPEC th =
    let (_,t) = dest_thm th in
	if is_pforall t then
	    GPSPEC (PSPEC (genlike (fst (dest_pforall t))) th)
	else
	    th;;

letrec PSPEC_TAC (t,x) =
    (if (not (is_pair t)) & (is_var x) then
	SPEC_TAC (t,x)
     else if (is_pair t) & (is_pair x) then
	let (t1,t2) = dest_pair t in
	let (x1,x2) = dest_pair x in
	    (PSPEC_TAC (t2,x2)) THEN
	    (PSPEC_TAC (t1,x1)) THEN
	    (CONV_TAC UNCURRY_FORALL_CONV)
    else if (not (is_pair t)) & (is_pair x) then
	let x' = genvar (type_of x) in
	    (SPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
    else % (is_pair t) & (is_var x) %
	let x' = (mk_pair o (genvar # genvar) o (type_of # type_of))
		    (dest_pair t) in
	    (PSPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
    ) ? failwith `PSPEC_TAC`;;
		    
% ------------------------------------------------------------------------- %
% Paired Gerneralisation:                                                   %
%    A |- t                                                                 %
%  ----------- PGEN p [where p is not free in A]                            %
%   A |- !p.t                                                               %
% ------------------------------------------------------------------------- %

letrec PGEN p th =
    (if is_var p then
	GEN p th
    else % is_pair p %
	let (v1, v2) = dest_pair p in
	   CONV_RULE UNCURRY_FORALL_CONV (PGEN v1 (PGEN v2 th))
    ) ? failwith `PGEN` ;;

let PGENL xl th = itlist PGEN xl th;;

letrec P_PGEN_TAC p :tactic (a,t) =
    (let (x,b) = (dest_pforall t) ?
	    failwith `P_PGEN_TAC: Goal not universally quantified` in
	if (is_var x) & (is_var p) then
	    X_GEN_TAC p (a,t)
	else if (is_pair x) & (is_pair p) then
	    let (p1,p2) = dest_pair p in
		((CONV_TAC CURRY_FORALL_CONV) THEN
		(P_PGEN_TAC p1) THEN
		(P_PGEN_TAC p2)) (a,t)
	else if (is_var p) & (is_pair x) then
	    let x' = genvar (type_of p) in
	    ((CONV_TAC (GEN_PALPHA_CONV x')) THEN
	    (X_GEN_TAC p)) (a,t)
	else %(is_pair p) & (is_var x)%
	    let x' = (mk_pair o (genvar # genvar) o (type_of # type_of))    
			(dest_pair p) in
		((CONV_TAC (GEN_PALPHA_CONV x')) THEN
		(P_PGEN_TAC p)) (a,t)
    ) ? failwith `P_PGEN_TAC` ;;

let PGEN_TAC : tactic (a,t) =
    let (x,b) = (dest_pforall t) ?
	    failwith `PGEN_TAC: Goal not universally quantified` in
	P_PGEN_TAC (pvariant (freesl(t.a)) x) (a,t);;

let FILTER_PGEN_TAC tm : tactic (a,t) =
    if (is_pforall t) & (not (tm = (fst (dest_pforall t)))) then
	PGEN_TAC (a,t)
    else
	failwith `FILTER_PGEN_TAC`;;
