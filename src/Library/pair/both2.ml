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
% CONTENTS: Functions which are common to both paried universal and	%
%           existential quantifications and which rely on more		%
%           primitive functions from all.ml and exi.ml.			%
% --------------------------------------------------------------------- %
%$Id: both2.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% ------------------------------------------------------------------------- %
% Paired stiping tactics, same as basic ones, but they use PGEN_TAC         %
% and PCHOOSE_THEN rather than GEN_TAC and CHOOSE_THEN                      %
% ------------------------------------------------------------------------- %

let PSTRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; PCHOOSE_THEN];;

let PSTRIP_ASSUME_TAC =
    (REPEAT_TCL PSTRIP_THM_THEN) CHECK_ASSUME_TAC;;

let PSTRUCT_CASES_TAC =
    REPEAT_TCL PSTRIP_THM_THEN
	 (\th. SUBST1_TAC th  ORELSE  ASSUME_TAC th);;

let PSTRIP_GOAL_THEN ttac = FIRST [PGEN_TAC; CONJ_TAC; DISCH_THEN ttac];;

let FILTER_PSTRIP_THEN ttac tm =
    FIRST [
	FILTER_PGEN_TAC tm;
	FILTER_DISCH_THEN ttac tm;
	CONJ_TAC ];;

let PSTRIP_TAC = PSTRIP_GOAL_THEN PSTRIP_ASSUME_TAC;;

let FILTER_PSTRIP_TAC = FILTER_PSTRIP_THEN PSTRIP_ASSUME_TAC;;

% ------------------------------------------------------------------------- %
%  A |- !p. (f p) = (g p)                                                   %
% ------------------------ PEXT                                             %
%       A |- f = g                                                          %
% ------------------------------------------------------------------------- %

let PEXT th =
    (let (p,_) = dest_pforall (concl th) in
    let p' = pvariant (thm_frees th) p in
    let th1 = PSPEC p' th in
    let th2 = PABS p' th1 in
    let th3 = (CONV_RULE (RATOR_CONV (RAND_CONV PETA_CONV))) th2 in
	(CONV_RULE (RAND_CONV PETA_CONV)) th3
    ) ? failwith `PEXT`;;

% ------------------------------------------------------------------------- %
% P_FUN_EQ_CONV "p" "f = g" = |- (f = g) = (!p. (f p) = (g p))              %
% ------------------------------------------------------------------------- %

let P_FUN_EQ_CONV =
    let gpty = ":*" in
    let grange = ":**" in
    let gfty = ":*->**" in
    let gf = genvar gfty in
    let gg = genvar gfty in
    let gp = genvar gpty in
    let imp1 = DISCH_ALL (GEN gp (AP_THM (ASSUME (mk_eq(gf,gg))) gp)) in
    let imp2 =
	DISCH_ALL
	    (EXT (ASSUME (mk_forall(gp, mk_eq(mk_comb(gf,gp),mk_comb(gg,gp))))))
    in
    let ext_thm = (IMP_ANTISYM_RULE imp1 imp2) in
	\p tm.
	    let (f,g) = dest_eq tm in
	    let fty = type_of f 
	    and pty = type_of p in
	    let gfinst = mk_var(fst (dest_var gf), fty)
	    and gginst = mk_var(fst (dest_var gg), fty) in
	    let range = hd (tl(snd(dest_type fty))) in
	    let th =
		INST_TY_TERM
		    ([(f,gfinst);(g,gginst)],
		     [(pty,gpty);(range,grange)])
		    ext_thm in
		(CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p)))) th ;;

% ------------------------------------------------------------------------- %
%      A |- !p. t = u                                                       %
% ------------------------ MK_PABS                                          %
%  A |- (\p. t) = (\p. u)                                                   %
% ------------------------------------------------------------------------- %

let MK_PABS th =
    (let (p,_) = dest_pforall (concl th) in
    let th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		(UNPBETA_CONV p)))))) th in
    let th2 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV
		(UNPBETA_CONV p))))) th1 in
    let th3 = PEXT th2 in
    let th4 = (CONV_RULE (RATOR_CONV (RAND_CONV (PALPHA_CONV p)))) th3 in
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th4
    ) ? failwith `MK_PABS`;;

% ------------------------------------------------------------------------- %
%  A |- !p. t p = u                                                         %
% ------------------ HALF_MK_PABS                                           %
%  A |- t = (\p. u)                                                         %
% ------------------------------------------------------------------------- %

let HALF_MK_PABS th = 
    (let (p,_) = dest_pforall (concl th) in
    let th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV 
		(UNPBETA_CONV p))))) th in
    let th2 = PEXT th1 in 
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th2
    ) ? failwith `HALF_MK_PABS` ;;

% ------------------------------------------------------------------------- %
%      A |- !p. t = u                                                       %
% ------------------------ MK_PFORALL                                       %
%  A |- (!p. t) = (!p. u)                                                   %
% ------------------------------------------------------------------------- %
let MK_PFORALL th =
    (let (p,_) = dest_pforall (concl th) in
    AP_TERM
    (mk_const
	(`!`, mk_type(`fun`, [mk_type(`fun`, [type_of p; bool_ty]); bool_ty])))
    (MK_PABS th)) ? failwith `MK_PFORALL` ;;

% ------------------------------------------------------------------------- %
%      A |- !p. t = u                                                       %
% ------------------------ MK_PEXISTS                                       %
%  A |- (?p. t) = (?p. u)                                                   %
% ------------------------------------------------------------------------- %
let MK_PEXISTS th =
    (let (p,_) = dest_pforall (concl th) in
    AP_TERM
    (mk_const
	(`?`, mk_type(`fun`, [mk_type(`fun`, [type_of p; bool_ty]); bool_ty])))
    (MK_PABS th)) ? failwith `MK_PEXISTS` ;;

% ------------------------------------------------------------------------- %
%      A |- !p. t = u                                                       %
% ------------------------ MK_PSELECT                                       %
%  A |- (@p. t) = (@p. u)                                                   %
% ------------------------------------------------------------------------- %
let MK_PEXISTS th =
    (let (p,_) = dest_pforall (concl th) in
     let pty = type_of p in
    AP_TERM
    (mk_const
	(`@`, mk_type(`fun`, [mk_type(`fun`, [pty; bool_ty]); pty])))
    (MK_PABS th)) ? failwith `MK_PSELECT` ;;

% ------------------------------------------------------------------------- %
%       A |- t = u                                                          %
% ------------------------ PFORALL_EQ "p"                                   %
%  A |- (!p. t) = (!p. u)                                                   %
% ------------------------------------------------------------------------- %

let PFORALL_EQ p th =
    (let pty = type_of p in
	AP_TERM
	    (mk_const
	    (`!`, mk_type(`fun`, [mk_type(`fun`, [pty; bool_ty ]); bool_ty])))
	(PABS p th)) ? failwith `PFORALL_EQ` ;;

% ------------------------------------------------------------------------- %
%       A |- t = u                                                          %
% ------------------------ PEXISTS_EQ "p"                                   %
%  A |- (?p. t) = (?p. u)                                                   %
% ------------------------------------------------------------------------- %

let PEXISTS_EQ p th =
    (let pty = type_of p in
	AP_TERM
	    (mk_const
	    (`?`, mk_type(`fun`, [mk_type(`fun`, [pty; bool_ty ]); bool_ty])))
	(PABS p th)) ? failwith `PEXISTS_EQ` ;;

% ------------------------------------------------------------------------- %
%       A |- t = u                                                          %
% ------------------------ PSELECT_EQ "p"                                   %
%  A |- (@p. t) = (@p. u)                                                   %
% ------------------------------------------------------------------------- %

let PSELECT_EQ p th =
    (let pty = type_of p in
	AP_TERM
	    (mk_const
	    (`@`, mk_type(`fun`, [mk_type(`fun`, [pty; bool_ty ]); pty])))
	(PABS p th)) ? failwith `PSELECT_EQ` ;;

% ------------------------------------------------------------------------- %
%                A |- t = u                                                 %
% ---------------------------------------- LIST_MK_PFORALL [p1;...pn]       %
%  A |- (!p1 ... pn. t) = (!p1 ... pn. u)                                   %
% ------------------------------------------------------------------------- %

let LIST_MK_PFORALL = itlist PFORALL_EQ ;;

% ------------------------------------------------------------------------- %
%                A |- t = u                                                 %
% ---------------------------------------- LIST_MK_PEXISTS [p1;...pn]       %
%  A |- (?p1 ... pn. t) = (?p1 ... pn. u)                                   %
% ------------------------------------------------------------------------- %

let LIST_MK_PEXISTS = itlist PEXISTS_EQ ;;
		
% ------------------------------------------------------------------------- %
%         A |- P ==> Q                                                      %
% -------------------------- EXISTS_IMP "p"                                 %
%  A |- (?p. P) ==> (?p. Q)                                                 %
% ------------------------------------------------------------------------- %

let PEXISTS_IMP p th =
    (let (a,c) = dest_imp (concl th) in
    let th1 = PEXISTS (mk_pexists(p,c),p) (UNDISCH th) in
    let asm = mk_pexists(p,a) in
    let th2 = DISCH asm (PCHOOSE (p, ASSUME asm) th1) in
	(CONV_RULE (RAND_CONV (GEN_PALPHA_CONV p))) th2 
    ) ? failwith `PEXISTS_IMP`;;

% ------------------------------------------------------------------------- %
% SWAP_PFORALL_CONV "!p q. t" = (|- (!p q. t) = (!q p. t))                  %
% ------------------------------------------------------------------------- %

let SWAP_PFORALL_CONV pqt =
    (let (p,qt) = dest_pforall pqt in
    let (q,t) = dest_pforall qt in
    let p' = genlike p in
    let q' = genlike q in
    let th1 = GEN_PALPHA_CONV p' pqt in
    let th2 = CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (GEN_PALPHA_CONV q')))) th1 in
    let th3 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV q)) th2 in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (GEN_PALPHA_CONV p)))) th3
    ) ? failwith `SWAP_PFORALL_CONV`;;

% ------------------------------------------------------------------------- %
% SWAP_PEXISTS_CONV "?p q. t" = (|- (?p q. t) = (?q p. t))                  %
% ------------------------------------------------------------------------- %

let SWAP_PEXISTS_CONV pqt =
    (let (p,qt) = dest_pexists pqt in
    let (q,t) = dest_pexists qt in
    let p' = genlike p in
    let q' = genlike q in
    let th1 = GEN_PALPHA_CONV p' pqt in
    let th2 = CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (GEN_PALPHA_CONV q')))) th1 in
    let th3 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV q)) th2 in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (GEN_PALPHA_CONV p)))) th3
    ) ? failwith `SWAP_PEXISTS_CONV`;;


% --------------------------------------------------------------------- %
% PART_PMATCH : just like PART_MATCH but doesn't mind leading paird q.s	%
% --------------------------------------------------------------------- %

let PART_PMATCH partfn th =
    let pth = GPSPEC (GSPEC (GEN_ALL th))  in
    let pat = partfn (concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth;;

% --------------------------------------------------------------------- %
%  A ?- !v1...vi. t'                                                    %
% ================== MATCH_MP_TAC (A' |- !x1...xn. s ==> !y1...tm. t)	%
%  A ?- ?z1...zp. s'                                                    %
% where z1, ..., zp are (type instances of) those variables among	%
% x1, ..., xn that do not occur free in t.				%
% --------------------------------------------------------------------- %

let PMATCH_MP_TAC : thm_tactic =
    let efn p (tm,th) = let ntm = mk_pexists(p,tm) in
        (ntm, PCHOOSE (p, ASSUME ntm) th)
    in
    \thm.
	let (tps,(ant,(cps,con))) =
	    ((I # ((I # strip_forall) o dest_imp)) o strip_pforall o concl) thm
	    ? failwith `MATCH_MP_TAC: not an implication` in
        let th1 = PSPECL cps (UNDISCH (PSPECL tps thm)) in
        let eps = filter (\p. not (occs_in p con)) tps in 
        let th2 = uncurry DISCH (itlist efn eps (ant,th1)) in
        \(A,g).
	    let (gps,gl) = strip_pforall g in
            let ins = match con gl ? failwith `PMATCH_MP_TAC: no match` in
            let ith = INST_TY_TERM ins th2 in
            let newg = fst(dest_imp(concl ith)) in
            let gth = PGENL gps (UNDISCH ith) ?
                           failwith `PMATCH_MP_TAC: generalized pair(s)` in
		([(A,newg)], \[th]. PROVE_HYP th gth);;

% --------------------------------------------------------------------- %
%  A1 |- !x1..xn. t1 ==> t2   A2 |- t1'            			%
% --------------------------------------  PMATCH_MP			%
%        A1 u A2 |- !xa..xk. t2'					%
% --------------------------------------------------------------------- %

let PMATCH_MP =
    letrec variants as vs =
	if null vs then
	    []
	else
	    let (h.t) = vs in
	    let h' = variant (as@(filter (\e. not (e = h)) t)) h in
	      (h',h).(variants (h'.as) t) in
    let frev_assoc e2 l = (fst (rev_assoc e2 l)) ? e2 
    in
    \ith. 
    let t = (fst o dest_imp o snd o strip_pforall o concl) ith
	    ? failwith `PMATCH_MP: not an implication` in
    \th.
    (let (B,t') = dest_thm th in
    let ty_inst = snd (match t t') in
    let ith_ = INST_TYPE ty_inst ith in
    let (A_, forall_ps_t_imp_u_) = dest_thm ith_ in
    let (ps_,t_imp_u_) = strip_pforall forall_ps_t_imp_u_ in
    let (t_,u_) = dest_imp (t_imp_u_) in
    let pvs = freesl ps_ in
    let A_vs = freesl A_ in
    let B_vs = freesl B in
    let tm_inst = fst (match t_ t') in
    let (match_vs, unmatch_vs) = partition (C free_in t_) (frees u_) in
    let rename = subtract unmatch_vs (subtract A_vs pvs) in
    let new_vs = freesl (map (C frev_assoc tm_inst) match_vs) in
    let renaming = variants (new_vs@A_vs@B_vs) rename in
    let (specs,insts) = partition (C mem (freesl pvs) o snd)
	    (renaming@tm_inst) in
    let spec_list = map (subst specs) ps_ in
    let mp_th = MP (PSPECL spec_list (INST insts ith_)) th in
    let gen_ps = (filter (\p. null (subtract (rip_pair p) rename)) ps_) in
    let qs = map (subst renaming) gen_ps
    in
	PGENL qs mp_th
    ) ? failwith `PMATCH_MP: can't instantiate theorem`;;
