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
% CONTENTS: conversions for moveing qantifiers about.			%
% --------------------------------------------------------------------- %
%$Id: conv.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

begin_section convsec;;

% ------------------------------------------------------------------------- %
% NOT_FORALL_THM = |- !f. ~(!x. f x) = (?x. ~f x)                   	    %
% ------------------------------------------------------------------------- %

    let NOT_FORALL_THM =
	let f = "f:*->bool" in
	let x = "x:*" in
	let t = mk_comb(f,x) in
	let all = mk_forall(x,t) and exists = mk_exists(x,mk_neg t) in
	let nott = ASSUME (mk_neg t) in
%WW%	let th1 = DISCH all (MP (NOT_ELIM nott) (SPEC x (ASSUME all))) in
	let imp1 = DISCH exists (CHOOSE (x, ASSUME exists) (NOT_INTRO th1)) in
	let th2 = CCONTR t 
%WW%   	    (MP (NOT_ELIM(ASSUME(mk_neg exists))) (EXISTS(exists,x)nott)) in
	let th3 = CCONTR exists 
%WW%   	    (MP (NOT_ELIM(ASSUME (mk_neg all))) (GEN x th2)) in
	let imp2 = DISCH (mk_neg all) th3 in
	    GEN f (IMP_ANTISYM_RULE imp2 imp1);;

% ------------------------------------------------------------------------- %
% NOT_EXISTS_THM = |- !f. ~(?x. f x) = (!x. ~f x)                   	    %
% ------------------------------------------------------------------------- %

    let NOT_EXISTS_THM =
	let f = "f:*->bool" in
	let x = "x:*" in
	let t = mk_comb(f,x) in
	let tm = mk_neg(mk_exists(x,t)) in
	let all = mk_forall(x,mk_neg t) in
	let asm1 = ASSUME t in
%WW%	let thm1 = MP (NOT_ELIM(ASSUME tm)) (EXISTS (rand tm, x) asm1) in
	let imp1 = DISCH tm (GEN x (NOT_INTRO (DISCH t thm1))) in
	let asm2 = ASSUME  all and asm3 = ASSUME (rand tm) in
	let thm2 = DISCH (rand tm) (CHOOSE (x,asm3) 
%WW%    	    (MP (NOT_ELIM(SPEC x asm2)) asm1)) in
	let imp2 = DISCH all (NOT_INTRO thm2) in
	    GEN f (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% NOT_PFORALL_CONV "~!p.t" = |- (~!p.t) = (?p.~t)                           %
% ------------------------------------------------------------------------- %

    let NOT_PFORALL_CONV tm =
	(let (p,_) = dest_pforall (dest_neg tm) in
	let f = rand (rand tm) in
	let th = ISPEC f NOT_FORALL_THM in
	let th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))) th in
	let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p))) th1 in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
	) ? failwith `NOT_PFORALL_CONV: argyment must have the form "~!p.tm"`;;

% ------------------------------------------------------------------------- %
% NOT_PEXISTS_CONV "~?p.t" = |- (~?p.t) = (!p.~t)                           %
% ------------------------------------------------------------------------- %

    let NOT_PEXISTS_CONV tm =
	(let (p,_) = dest_pexists (dest_neg tm) in
	let f = rand (rand tm) in
	let th = ISPEC f NOT_EXISTS_THM in
	let th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))) th in
	let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p))) th1 in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
	) ? failwith `NOT_PEXISTS_CONV: argyment must have the form "~!p.tm"`;;

% ------------------------------------------------------------------------- %
% PEXISTS_NOT_CONV "?p.~t" = |- (?p.~t) = (~!p.t)                           %
% ------------------------------------------------------------------------- %

    let PEXISTS_NOT_CONV tm =
	(let xtm = mk_pforall ((I # dest_neg) (dest_pexists tm)) in
	    SYM (NOT_PFORALL_CONV (mk_neg xtm))
	) ? failwith `PEXISTS_NOT_CONV: argument must have the form "?x.~tm"`;;

% ------------------------------------------------------------------------- %
% PFORALL_NOT_CONV "!p.~t" = |- (!p.~t) = (~?p.t)                           %
% ------------------------------------------------------------------------- %

    let PFORALL_NOT_CONV tm =
	(let xtm = mk_pexists ((I # dest_neg) (dest_pforall tm)) in
	    SYM (NOT_PEXISTS_CONV (mk_neg xtm))
	) ? failwith `PFORALL_NOT_CONV: argument must have the form "!x.~tm"`;;


% ------------------------------------------------------------------------- %
% FORALL_AND_THM |- !f g. (!x. f x /\ g x) = ((!x. f x) /\ (!x. g x))       %
% ------------------------------------------------------------------------- %

    let FORALL_AND_THM =
	let f = "f:*->bool" in
	let g = "g:*->bool" in
	let x = "x:*" in
	let th1 = ASSUME "!x:*. (f x) /\ (g x)" in
	let imp1 =
	    (uncurry CONJ) (((GEN x) # (GEN x)) (CONJ_PAIR (SPEC x th1))) in
	let th2 = ASSUME "(!x:*. f x) /\ (!x:*. g x)" in
	let imp2 =
	    GEN x ((uncurry CONJ) (((SPEC x) # (SPEC x)) (CONJ_PAIR th2)))
	in
	    GENL [f;g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2));;

% ------------------------------------------------------------------------- %
% PFORALL_AND_CONV "!x. P /\ Q" = |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)        %
% ------------------------------------------------------------------------- %

    let PFORALL_AND_CONV tm =
	(let (x,(P,Q)) = (I # dest_conj) (dest_pforall tm) in
	let f = mk_pabs(x,P) in
	let g = mk_pabs(x,Q) in
	let th = ISPECL [f;g] FORALL_AND_THM in
	let th1 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV
		    (PALPHA_CONV x))))
		th in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
		    (RATOR_CONV (RAND_CONV PBETA_CONV))))))
		    th1 in
	let th3 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
		    (RAND_CONV PBETA_CONV)))))
		    th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th3 in
	    (CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV)))) th4
	) ? failwith
	    `PFORALL_AND_CONV: argument must have the form "!p. P /\\ Q"`;;

% ------------------------------------------------------------------------- %
% EXISTS_OR_THM |- !f g. (?x. f x \/ g x) = ((?x. f x) \/ (?x. g x))        %
% ------------------------------------------------------------------------- %

    let EXISTS_OR_THM =
	let f = "f:*->bool" in
	let g = "g:*->bool" in
	let x = "x:*" in
	let P = mk_comb(f,x) in
	let Q = mk_comb(g,x) in
	let tm = mk_pexists (x,mk_disj(P,Q)) in
	let ep = mk_exists(x,P) and eq = mk_exists(x,Q) in
	let Pth = EXISTS(ep,x)(ASSUME P) and Qth = EXISTS(eq,x)(ASSUME Q) in
	let thm1 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth in
	let imp1 = DISCH tm (CHOOSE (x,ASSUME tm) thm1) in
	let t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) in
	let th1 = EXISTS(tm,x) t1 and th2 = EXISTS(tm,x) t2 in
	let e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2 in
	let thm2 = DISJ_CASES (ASSUME(mk_disj(ep,eq))) e1 e2 in
	let imp2 = DISCH (mk_disj(ep,eq)) thm2 in
	    GENL [f;g] (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% PEXISTS_OR_CONV "?x. P \/ Q" = |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)         %
% ------------------------------------------------------------------------- %

    let PEXISTS_OR_CONV tm =
	(let (x,(P,Q)) = (I # dest_disj) (dest_pexists tm) in
	let f = mk_pabs(x,P) in
	let g = mk_pabs(x,Q) in
	let th = ISPECL [f;g] EXISTS_OR_THM in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
	    (PALPHA_CONV x))))) th in
	let th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
	    (RATOR_CONV (RAND_CONV PBETA_CONV))))))) th1 in
	let th3 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
	    (RAND_CONV PBETA_CONV)))))) th2 in
	let th4 = (CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV 
	    ETA_CONV))))) th3 in
	    (CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV)))) th4
	) ? failwith
	    `PEXISTS_OR_CONV: argument must have the form "?p. P \\/ Q"`;;

% ------------------------------------------------------------------------- %
% AND_PFORALL_CONV "(!x. P) /\ (!x. Q)" = |- (!x.P)/\(!x.Q) = (!x. P /\ Q)  %
% ------------------------------------------------------------------------- %

    let AND_PFORALL_CONV tm =
	(let (x,P),(y,Q) = (dest_pforall # dest_pforall) (dest_conj tm) in
	if (not (x=y)) then fail else
	let f = mk_pabs (x,P) in
	let g = mk_pabs (x,Q) in
	let th = SYM (ISPECL [f;g] FORALL_AND_THM) in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV 
	    (RAND_CONV ETA_CONV)))))) th in
	let th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
	    (RAND_CONV ETA_CONV))))) th1 in
	let th3 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th2 in
	let th4 = (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
	    (RATOR_CONV (RAND_CONV PBETA_CONV)))))) th3
	in
	    (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV
		PBETA_CONV))))) th4
	) ? failwith
	    `AND_PFORALL_CONV: arguments must have form "(!p.P)/\\(!p.Q)"`;;

% ------------------------------------------------------------------------- %
% LEFT_AND_FORALL_THM = |- !f Q. (!x. f x) /\ Q = (!x. f x /\ Q)            %
% ------------------------------------------------------------------------- %

    let LEFT_AND_FORALL_THM =
	let x = "x:*" in
	let f = "f:*->bool" in
	let Q = "Q:bool" in
	let th1 = ASSUME "(!x:*. f x) /\ Q" in
	let imp1 = GEN x ((uncurry CONJ) ((SPEC x # I) (CONJ_PAIR th1))) in
	let th2 = ASSUME "!x:*. f x /\ Q" in
	let imp2 = (uncurry CONJ) ((GEN x # I) (CONJ_PAIR (SPEC x th2))) in
	    GENL [Q;f] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2));;

% ------------------------------------------------------------------------- %
% LEFT_AND_PFORALL_CONV "(!x.P) /\  Q" =                                    %
%   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)                                    %
% ------------------------------------------------------------------------- %

    let LEFT_AND_PFORALL_CONV tm =
	(let (x,P),Q = (dest_pforall # I) (dest_conj tm) in
	let f = mk_pabs(x,P) in
	let th = ISPECL [Q;f] LEFT_AND_FORALL_THM in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV ETA_CONV)))))) th in
	let th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
	in
	    (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		PBETA_CONV)))))) th2
	) ? failwith `LEFT_AND_PFORALL_CONV: expecting "(!p.P) /\\ Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_AND_FORALL_THM = |- !P g. P /\ (!x. g x) = (!x. P /\ g x)           %
% ------------------------------------------------------------------------- %

    let RIGHT_AND_FORALL_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let th1 = ASSUME "P /\ (!x:*. g x)" in
	let imp1 = GEN x ((uncurry CONJ) ((I # SPEC x) (CONJ_PAIR th1))) in
	let th2 = ASSUME "!x:*. P /\ g x" in
	let imp2 = (uncurry CONJ) ((I # GEN x) (CONJ_PAIR (SPEC x th2))) in
	    GENL [P;g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2));;

% ------------------------------------------------------------------------- %
% RIGHT_AND_PFORALL_CONV "P /\ (!x.Q)" =                                    %
%   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x])                                   %
% ------------------------------------------------------------------------- %

    let RIGHT_AND_PFORALL_CONV tm =
	(let P,(x,Q) = (I # dest_pforall) (dest_conj tm) in
	let g = mk_pabs(x,Q) in
	let th = (ISPECL [P; g] RIGHT_AND_FORALL_THM) in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
	    ETA_CONV))))) th in
	let th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1 in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
	) ? failwith `RIGHT_AND_PFORALL_CONV: expecting "P /\\ (!p.Q)"`;;

% ------------------------------------------------------------------------- %
% OR_PEXISTS_CONV "(?x. P) \/ (?x. Q)" = |- (?x.P) \/ (?x.Q) = (?x. P \/ Q) %
% ------------------------------------------------------------------------- %

    let OR_PEXISTS_CONV tm =
	(let (x,P),(y,Q) = (dest_pexists # dest_pexists) (dest_disj tm) in
	if (not (x=y)) then fail else
	let f = mk_pabs (x,P) in
	let g = mk_pabs (x,Q) in
	let th = SYM (ISPECL [f;g] EXISTS_OR_THM) in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV 
	    (RAND_CONV ETA_CONV)))))) th in
	let th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
	    (RAND_CONV ETA_CONV))))) th1 in
	let th3 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th2 in
	let th4 = (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
	    (RATOR_CONV (RAND_CONV PBETA_CONV)))))) th3
	in
	    (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV
		PBETA_CONV))))) th4
	) ? failwith
	    `OR_PEXISTS_CONV: arguments must have form "(!p.P) \\/ (!p.Q)"`;;

% ------------------------------------------------------------------------- %
% LEFT_OR_EXISTS_THM = |- (?x. f x) \/ Q = (?x. f x \/ Q)                   %
% ------------------------------------------------------------------------- %

    let LEFT_OR_EXISTS_THM =
	let x = "x:*" in
	let Q = "Q:bool" in
	let f = "f:*->bool" in
	let P = mk_comb (f,x) in
	let ep = mk_exists(x,P) in
	let tm = mk_disj (ep,Q) in
	let otm = mk_exists (x,(mk_disj(P,Q))) in
	let t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) in
	let th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2 in
	let thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x,ASSUME ep)th1) th2 in
	let imp1 = DISCH tm thm1 in
	let Pth = EXISTS(ep,x)(ASSUME P) and Qth = ASSUME Q in
	let thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth in
	let imp2 = DISCH otm (CHOOSE (x,ASSUME otm) thm2) in
	    GENL [Q;f] (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% LEFT_OR_PEXISTS_CONV "(?x.P) \/  Q" =                                     %
%   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)                                    %
% ------------------------------------------------------------------------- %

    let LEFT_OR_PEXISTS_CONV tm =
	(let (x,P),Q = (dest_pexists # I) (dest_disj tm) in
	let f = mk_pabs(x,P) in
	let th = ISPECL [Q;f] LEFT_OR_EXISTS_THM in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV ETA_CONV)))))) th in
	let th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
	in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th2
	) ? failwith `LEFT_OR_PEXISTS_CONV: expecting "(?p.P) \\/ Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_OR_EXISTS_THM = |- P \/ (?x. g x) = (?x. P \/ g x)                  %
% ------------------------------------------------------------------------- %

    let RIGHT_OR_EXISTS_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let Q = mk_comb (g,x) in
	let eq = mk_exists(x,Q) in
	let tm = mk_disj (P,eq) in
	let otm = mk_exists (x,(mk_disj(P,Q))) in
	let t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) in
	let th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2 in
	let thm1 = DISJ_CASES (ASSUME tm) th1 (CHOOSE(x,ASSUME eq)th2) in
	let imp1 = DISCH tm thm1 in
	let Qth = EXISTS(eq,x)(ASSUME Q) and Pth = ASSUME P in
	let thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth in
	let imp2 = DISCH otm (CHOOSE (x,ASSUME otm)  thm2) in
	    GENL [P;g] (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% RIGHT_OR_PEXISTS_CONV "P \/ (?x.Q)" =                                     %
%   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x])                                   %
% ------------------------------------------------------------------------- %

    let RIGHT_OR_PEXISTS_CONV tm =
	(let P,(x,Q) = (I # dest_pexists) (dest_disj tm) in
	let g = mk_pabs(x,Q) in
	let th = (ISPECL [P; g] RIGHT_OR_EXISTS_THM) in
	let th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
	    ETA_CONV))))) th in
	let th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1 in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
	) ? failwith `RIGHT_OR_PEXISTS_CONV: expecting "P \\/ (?p.Q)"`;;
	
% ------------------------------------------------------------------------- %
% BOTH_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q) = (?x. P) /\ (?x. Q)          %
% ------------------------------------------------------------------------- %

    let BOTH_EXISTS_AND_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let Q = "Q:bool" in
	let t = mk_conj(P,Q) in
	let exi = mk_exists(x,t) in
	let (t1,t2) = CONJ_PAIR (ASSUME t) in
	let t11 = EXISTS ((mk_exists(x,P)),x) t1 in
	let t21 = EXISTS ((mk_exists(x,Q)),x) t2 in
	let imp1 =
	    DISCH_ALL
		(CHOOSE (x, ASSUME (mk_exists(x,mk_conj(P,Q)))) (CONJ t11 t21))
	in
	let th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) in
	let th22 = CHOOSE(x,ASSUME(mk_exists(x,P))) th21 in
	let th23 = CHOOSE(x,ASSUME(mk_exists(x,Q))) th22 in
	let (u1,u2) =
	    CONJ_PAIR (ASSUME (mk_conj(mk_exists(x,P),mk_exists(x,Q)))) in
	let th24 = PROVE_HYP u1 (PROVE_HYP u2 th23) in
	let imp2 = DISCH_ALL th24 in
	    GENL [P;Q] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% LEFT_EXISTS_AND_THM = |- !Q f. (?x. f x /\ Q) = (?x. f x) /\ Q            %
% ------------------------------------------------------------------------- %

    let LEFT_EXISTS_AND_THM =
	let x = "x:*" in
	let f = "f:*->bool" in
	let P = mk_comb (f,x) in
	let Q = "Q:bool" in
	let t = mk_conj(P,Q) in
	let exi = mk_exists(x,t) in
	let (t1,t2) = CONJ_PAIR (ASSUME t) in
	let t11 = EXISTS ((mk_exists(x,P)),x) t1 in
	let imp1 =
	    DISCH_ALL
		(CHOOSE
		    (x, ASSUME (mk_exists(x,mk_conj(P,Q))))
		    (CONJ t11 t2)) in
	let th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) in
	let th22 = CHOOSE(x,ASSUME(mk_exists(x,P))) th21 in
	let (u1,u2) = CONJ_PAIR (ASSUME (mk_conj(mk_exists(x,P),Q))) in
	let th23 = PROVE_HYP u1 (PROVE_HYP u2 th22) in
	let imp2 = DISCH_ALL th23 in
	    GENL [Q;f] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% RIGHT_EXISTS_AND_THM = |- !P g. (?x. P /\ g x) = P /\ (?x. g x)           %
% ------------------------------------------------------------------------- %

    let RIGHT_EXISTS_AND_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let Q = mk_comb(g,x) in
	let t = mk_conj(P,Q) in
	let exi = mk_exists(x,t) in
	let (t1,t2) = CONJ_PAIR (ASSUME t) in
	let t21 = EXISTS ((mk_exists(x,Q)),x) t2 in
	let imp1 =
	    DISCH_ALL
		(CHOOSE
		    (x, ASSUME (mk_exists(x,mk_conj(P,Q))))
		    (CONJ t1 t21)) in
	let th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) in
	let th22 = CHOOSE(x,ASSUME(mk_exists(x,Q))) th21 in
	let (u1,u2) = CONJ_PAIR (ASSUME (mk_conj(P,mk_exists(x,Q)))) in
	let th23 = PROVE_HYP u1 (PROVE_HYP u2 th22) in
	let imp2 = DISCH_ALL th23 in
	    GENL [P;g] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% PEXISTS_AND_CONV : move existential quantifier into conjunction.          %
%                                                                           %
% A call to PEXISTS_AND_CONV "?x. P /\ Q"  returns:                         %
%                                                                           %
%    |- (?x. P /\ Q) = (?x.P) /\ Q        [x not free in Q]                 %
%    |- (?x. P /\ Q) = P /\ (?x.Q)        [x not free in P]                 %
%    |- (?x. P /\ Q) = (?x.P) /\ (?x.Q)   [x not free in P /\ Q]            %
% ------------------------------------------------------------------------- %

    let PEXISTS_AND_CONV tm =
	(let (x,(P,Q)) = (I # dest_conj) (dest_pexists tm) ?
	    failwith `expecting "?x. P /\\ Q"` in
	let oP = occs_in x P and oQ =  occs_in x Q in
	    if (oP & oQ) then
		failwith `bound pair occurs in both conjuncts`
	    else if ((not oP) & (not oQ)) then
		let th1 =
		    INST_TYPE
			[(type_of x, mk_vartype `*`)]
			BOTH_EXISTS_AND_THM in
		let th2 = SPECL [P;Q] th1 in
		let th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 in
		let th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 in
		let th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
		in
		    th5
	    else if oP then % not free in Q %
		let f = mk_pabs(x,P) in
		let th1 = ISPECL [Q;f] LEFT_EXISTS_AND_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV))))))
			th2 in
		let th4 = 
		    CONV_RULE
			(RAND_CONV
			    (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			th3
		in
		    th4
	    else % not free in P%
		let g = mk_pabs(x,Q) in
		let th1 = ISPECL [P;g] RIGHT_EXISTS_AND_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RAND_CONV PBETA_CONV)))))
			th2 in
		let th4 = 
		    CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))) th3
		in
		    th4
	) ?\st failwith `PEXISTS_AND_CONV: `^st;;

% ------------------------------------------------------------------------- %
% AND_PEXISTS_CONV "(?x.P) /\ (?x.Q)" = |- (?x.P) /\ (?x.Q) = (?x. P /\ Q)  %
% ------------------------------------------------------------------------- %

    let AND_PEXISTS_CONV tm =
	(let ((x,P),(y,Q)) = (dest_pexists # dest_pexists) (dest_conj tm)
	    ? failwith `expecting "(?x.P) /\\ (?x.Q)"`
	in
	    if not (x=y) then
		failwith `expecting "(?x.P) /\\ (?x.Q)"`
	    else if (occs_in x P) or (occs_in x Q) then
		failwith `"` ^ (fst(dest_var x)) ^ `" free in conjunct(s)`
	    else
		SYM (PEXISTS_AND_CONV (mk_pexists (x,mk_conj(P,Q))))
	) ?\st failwith `AND_EXISTS_CONV: ` ^ st;;

% ------------------------------------------------------------------------- %
% LEFT_AND_PEXISTS_CONV "(?x.P) /\  Q" =                                    %
%   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q)                                    %
% ------------------------------------------------------------------------- %
     
    let LEFT_AND_PEXISTS_CONV tm =
	(let ((x,P),Q) = (dest_pexists # I) (dest_conj tm) in
	let f = mk_pabs(x,P) in
	let th1 = SYM (ISPECL [Q;f] LEFT_EXISTS_AND_THM) in
	let th2 =
	    CONV_RULE   
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 in
	let th3 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th3
	in
	    th4
	) ? failwith `LEFT_AND_PEXISTS_CONV: expecting "(?x.P) /\\ Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_AND_PEXISTS_CONV "P /\ (?x.Q)" =                                    %
%   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x])                                   %
% ------------------------------------------------------------------------- %

    let RIGHT_AND_PEXISTS_CONV tm =
	(let (P,(x,Q)) = (I # dest_pexists) (dest_conj tm) in
	let g = mk_pabs(x,Q) in
	let th1 = SYM (ISPECL [P;g] RIGHT_EXISTS_AND_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
	in
	    th4
	) ? failwith `RIGHT_AND_EXISTS_CONV: expecting "P /\\ (?x.Q)"`;;

% ------------------------------------------------------------------------- %
% BOTH_FORALL_OR_THM = |- !P Q. (!x. P \/ Q) = (!x. P) \/ (!x. Q)           %
% ------------------------------------------------------------------------- %

    let BOTH_FORALL_OR_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let Q = "Q:bool" in
	let imp11 = DISCH_ALL (SPEC x (ASSUME (mk_forall(x,P)))) in
	let imp12 = DISCH_ALL (GEN x (ASSUME P)) in
	let fath = IMP_ANTISYM_RULE imp11 imp12 in
	let th1 = REFL (mk_forall(x, mk_disj (P,Q))) in
	let th2 =
	    CONV_RULE (RAND_CONV (K (INST [(mk_disj(P,Q),P)] fath))) th1 in
	let th3 =
	    CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (K (SYM fath))))) th2 in
	let th4 =
	    CONV_RULE (RAND_CONV (RAND_CONV (K (SYM (INST [(Q,P)] fath))))) th3 
	in
	    GENL [P;Q] th4 ;;

% ------------------------------------------------------------------------- %
% LEFT_FORALL_OR_THM = |- !Q f. (!x. f x \/ Q) = (!x. f x) \/ Q             %
% ------------------------------------------------------------------------- %

    let LEFT_FORALL_OR_THM =
	let x = "x:*" in
	let f = "f:*->bool" in
	let P = mk_comb (f,x) in
	let Q = "Q:bool" in
	let tm = (mk_forall(x,mk_disj(P,Q))) in
	let thm1 = SPEC x (ASSUME tm) in
%WW%	let thm2 = CONTR P (MP (NOT_ELIM(ASSUME (mk_neg Q))) (ASSUME Q)) in
	let thm3 = DISJ1 (GEN x (DISJ_CASES thm1 (ASSUME P) thm2)) Q in
	let thm4 = DISJ2 (mk_forall(x,P)) (ASSUME Q) in
	let imp1 = DISCH tm (DISJ_CASES (SPEC Q EXCLUDED_MIDDLE) thm4 thm3) in
	let thm5 = SPEC x (ASSUME (mk_forall(x,P))) in
	let thm6 = ASSUME Q in
	let imp2 =
	    (DISCH_ALL (GEN x (DISJ_CASES_UNION
				 (ASSUME (mk_disj(mk_forall(x,P),Q)))
				 thm5
				 thm6)))
	in
	    GENL [Q;f] (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% RIGHT_FORALL_OR_THM = |- !P g. (!x. P \/ g x) = P \/ (!x. g x)            %
% ------------------------------------------------------------------------- %

    let RIGHT_FORALL_OR_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let Q = mk_comb(g,x) in
	let tm = (mk_forall(x,mk_disj(P,Q))) in
	let thm1 = SPEC x (ASSUME tm) in
%WW%	let thm2 = CONTR Q (MP (NOT_ELIM (ASSUME (mk_neg P))) (ASSUME P)) in
	let thm3 = DISJ2 P (GEN x (DISJ_CASES thm1 thm2 (ASSUME Q))) in
	let thm4 = DISJ1 (ASSUME P) (mk_forall(x,Q)) in
	let imp1 = DISCH tm (DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm4 thm3) in
	let thm5 = ASSUME P in
	let thm6 = SPEC x (ASSUME (mk_forall(x,Q))) in
	let imp2 =
	    (DISCH_ALL (GEN x (DISJ_CASES_UNION
				 (ASSUME (mk_disj(P,mk_forall(x,Q))))
				 thm5
				 thm6)))
	in
	    GENL [P;g] (IMP_ANTISYM_RULE imp1 imp2);;

% ------------------------------------------------------------------------- %
% PFORALL_OR_CONV : move universal quantifier into disjunction.             %
%                                                                           %
% A call to PFORALL_OR_CONV "!x. P \/ Q"  returns:                          %
%                                                                           %
%   |- (!x. P \/ Q) = (!x.P) \/ Q        [if x not free in Q]               %
%   |- (!x. P \/ Q) = P \/ (!x.Q)        [if x not free in P]               %
%   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)   [if x free in neither P nor Q]     %
% ------------------------------------------------------------------------- %

    let PFORALL_OR_CONV tm =
	(let (x,(P,Q)) = (I # dest_disj) (dest_pforall tm) ?
	    failwith `expecting "!x. P \\/ Q"` in
	let oP = occs_in x P and oQ =  occs_in x Q in
	    if (oP & oQ) then
		failwith `bound pair occurs in both conjuncts`
	    else if ((not oP) & (not oQ)) then
		let th1 =
		    INST_TYPE
			[(type_of x, mk_vartype `*`)]
			BOTH_FORALL_OR_THM in
		let th2 = SPECL [P;Q] th1 in
		let th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 in
		let th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 in
		let th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
		in
		    th5
	    else if oP then % not free in Q %
		let f = mk_pabs(x,P) in
		let th1 = ISPECL [Q;f] LEFT_FORALL_OR_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV)))))) 
			th2 in
		let th4 = 
		    CONV_RULE
			(RAND_CONV
			    (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			th3
		in
		    th4
	    else % not free in P%
		let g = mk_pabs(x,Q) in
		let th1 = ISPECL [P;g] RIGHT_FORALL_OR_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
			(PABS_CONV (RAND_CONV PBETA_CONV)))))) 
			th2 in
		let th4 = 
		    (CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			th3
		in
		    th4
	) ?\st failwith `PFORALL_OR_CONV: `^st;;

% ------------------------------------------------------------------------- %
% OR_PFORALL_CONV "(!x.P) \/ (!x.Q)" = |- (!x.P) \/ (!x.Q) = (!x. P \/ Q)   %
% ------------------------------------------------------------------------- %

    let OR_PFORALL_CONV tm =
	(let ((x,P),(y,Q)) = (dest_pforall # dest_pforall) (dest_disj tm)
	    ? failwith `expecting "(!x.P) \\/ (!x.Q)"`
	in
	    if not (x=y) then
		failwith `expecting "(!x.P) \\/ (!x.Q)"`
	    else if (occs_in x P) or (occs_in x Q) then
		failwith `"` ^ (fst(dest_var x)) ^ `" free in disjuncts(s)`
	    else
		SYM (PFORALL_OR_CONV (mk_pforall (x,mk_disj(P,Q))))
	) ?\st failwith `OR_FORALL_CONV: ` ^ st;;

% ------------------------------------------------------------------------- %
% LEFT_OR_PFORALL_CONV "(!x.P) \/  Q" =                                     %
%   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q)                                    %
% ------------------------------------------------------------------------- %
     
    let LEFT_OR_PFORALL_CONV tm =
	(let ((x,P),Q) = (dest_pforall # I) (dest_disj tm) in
	let f = mk_pabs(x,P) in
	let th1 = SYM (ISPECL [Q;f] LEFT_FORALL_OR_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th3
	in
	    th4
	) ? failwith `LEFT_OR_PFORALL_CONV: expecting "(!x.P) \\/ Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_OR_PFORALL_CONV "P \/ (!x.Q)" =                                     %
%   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x])                                   %
% ------------------------------------------------------------------------- %

    let RIGHT_OR_PFORALL_CONV tm =
	(let (P,(x,Q)) = (I # dest_pforall) (dest_disj tm) in
	let g = mk_pabs(x,Q) in
	let th1 = SYM (ISPECL [P;g] RIGHT_FORALL_OR_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
	in
	    th4
	) ? failwith `RIGHT_OR_FORALL_CONV: expecting "P \\/ (!x.Q)"`;;

% ------------------------------------------------------------------------- %
% BOTH_FORALL_IMP_THM = |- (!x. P ==> Q) = ((?x.P) ==> (!x.Q))              %
% ------------------------------------------------------------------------- %

    let BOTH_FORALL_IMP_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let Q = "Q:bool" in
	let tm = mk_forall(x, mk_imp (P, Q)) in
	let asm = mk_exists(x,P) in
	let th1 = GEN x (CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm)))) in
	let imp1 = DISCH tm (DISCH asm th1) in
	let cncl = rand(concl imp1) in
	let th2 = SPEC x (MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P))) in
	let imp2 = DISCH cncl (GEN x (DISCH P th2)) in
	    GENL [P;Q] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% LEFT_FORALL_IMP_THM = |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)               %
% ------------------------------------------------------------------------- %

    let LEFT_FORALL_IMP_THM =
	let x = "x:*" in
	let f = "f:*->bool" in
	let P = mk_comb(f,x) in
	let Q = "Q:bool" in
	let tm = mk_forall(x, mk_imp (P, Q)) in
	let asm = mk_exists(x,P) in
	let th1 = CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm))) in
	let imp1 = DISCH tm (DISCH asm th1) in
	let cncl = rand(concl imp1) in
	let th2 = MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P)) in
	let imp2 = DISCH cncl (GEN x (DISCH P th2)) in
	    GENL [Q;f] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% RIGHT_FORALL_IMP_THM = |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))              %
% ------------------------------------------------------------------------- %

    let RIGHT_FORALL_IMP_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let Q = mk_comb (g,x) in
	let tm = mk_forall(x, mk_imp (P, Q)) in
	let imp1 = DISCH P(GEN x(UNDISCH(SPEC x(ASSUME tm)))) in
	let cncl = concl imp1 in
	let imp2 = GEN x (DISCH P(SPEC x(UNDISCH (ASSUME cncl)))) in
	    GENL [P;g] (IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2)) ;;

% ------------------------------------------------------------------------- %
% BOTH_EXISTS_IMP_THM = |- (?x. P ==> Q) = ((!x.P) ==> (?x.Q))              %
% ------------------------------------------------------------------------- %

    let BOTH_EXISTS_IMP_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let Q = "Q:bool" in
	let tm = mk_exists(x, mk_imp (P, Q)) in
	let eQ = mk_exists(x,Q) in
	let aP = mk_forall(x,P) in
	let thm1 = EXISTS(eQ,x)(UNDISCH(ASSUME(mk_imp(P,Q)))) in
	let thm2 = DISCH aP (PROVE_HYP (SPEC x (ASSUME aP)) thm1) in
	let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) thm2) in
	let thm2 = CHOOSE(x,UNDISCH (ASSUME (rand(concl imp1)))) (ASSUME Q) in
	let thm3 = DISCH P (PROVE_HYP (GEN x (ASSUME P)) thm2) in
	let imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,x) thm3) in
	    GENL [P;Q] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% LEFT_EXISTS_IMP_THM = |- (?x. P[x] ==> Q) = ((!x.P[x]) ==> Q)             %
% ------------------------------------------------------------------------- %

    let LEFT_EXISTS_IMP_THM =
	let x = "x:*" in
	let f = "f:*->bool" in
	let P = mk_comb(f,x) in
	let Q = "Q:bool" in
	let tm = mk_exists(x, mk_imp (P, Q)) in
	let allp = mk_forall(x,P) in
	let th1 = SPEC x (ASSUME allp) in
	let thm1 = MP (ASSUME(mk_imp(P,Q))) th1 in
	let imp1 = DISCH tm (CHOOSE(x,ASSUME tm)(DISCH allp thm1)) in
	let otm = rand(concl imp1) in
	let thm2 = EXISTS(tm,x)(DISCH P (UNDISCH(ASSUME otm))) in
	let nex =  mk_exists(x,mk_neg P) in
	let asm1 = EXISTS (nex, x) (ASSUME (mk_neg P)) in
%WW%	let th2 = CCONTR P (MP (NOT_ELIM(ASSUME (mk_neg nex))) asm1) in
%WW%	let th3 = CCONTR nex (MP (NOT_ELIM(ASSUME(mk_neg allp)))(GEN x th2)) in
	let thm4 = DISCH P (CONTR Q (UNDISCH (ASSUME (mk_neg P)))) in
	let thm5 = CHOOSE(x,th3)(EXISTS(tm,x)thm4) in
	let thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5 in
	let imp2 = DISCH otm thm6 in
	    GENL [Q; f] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% RIGHT_EXISTS_IMP_THM = |- (?x. P ==> Q[x]) = (P ==> (?x.Q[x]))            %
% ------------------------------------------------------------------------- %

    let RIGHT_EXISTS_IMP_THM =
	let x = "x:*" in
	let P = "P:bool" in
	let g = "g:*->bool" in
	let Q = mk_comb (g,x) in
	let tm = mk_exists(x, mk_imp (P, Q)) in
	let thm1 = EXISTS (mk_exists(x,Q),x) (UNDISCH(ASSUME(mk_imp(P,Q)))) in
	let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (DISCH P thm1)) in
	let thm2 = UNDISCH (ASSUME (rand(concl imp1))) in
	let thm3 = CHOOSE (x,thm2) (EXISTS (tm,x) (DISCH P (ASSUME Q))) in
	let thm4 = EXISTS(tm,x)(DISCH P(CONTR Q(UNDISCH(ASSUME(mk_neg P))))) in
	let thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4 in
	let imp2 = (DISCH(rand(concl imp1)) thm5) in
	    GENL [P;g] (IMP_ANTISYM_RULE imp1 imp2) ;;

% ------------------------------------------------------------------------- %
% PFORALL_IMP_CONV, implements the following axiom schemes.                 %
%                                                                           %
%       |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))     [x not free in P]         %
%                                                                           %
%       |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)     [x not free in Q]         %
%                                                                           %
%       |- (!x. P==>Q) = ((?x.P) ==> (!x.Q))      [x not free in P==>Q]     %
% ------------------------------------------------------------------------- %

    let PFORALL_IMP_CONV tm =
	(let (x,(P,Q)) = (I # dest_imp) (dest_pforall tm) ?
	    failwith `expecting "?x. P ==> Q"` in
	let oP = occs_in x P and oQ =  occs_in x Q in
	    if (oP & oQ) then
		failwith `bound pair occurs in both sides of "==>"`
	    else if ((not oP) & (not oQ)) then
		let th1 =
		    INST_TYPE
			[(type_of x, mk_vartype `*`)]
			BOTH_FORALL_IMP_THM in
		let th2 = SPECL [P;Q] th1 in
		let th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 in
		let th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 in
		let th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
		in
		    th5
	    else if oP then % not free in Q %
		let f = mk_pabs(x,P) in
		let th1 = ISPECL [Q;f] LEFT_FORALL_IMP_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV)))))) 
			th2 in
		let th4 = 
		    CONV_RULE
			(RAND_CONV
			    (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			th3
		in
		    th4
	    else % not free in P%
		let g = mk_pabs(x,Q) in
		let th1 = ISPECL [P;g] RIGHT_FORALL_IMP_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
			    (RAND_CONV PBETA_CONV)))))
			th2 in
		let th4 = 
		    CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))) th3
		in
		    th4
	) ?\st failwith `PFORALL_IMP_CONV: `^st;;

% ------------------------------------------------------------------------- %
% LEFT_IMP_PEXISTS_CONV "(?x.P) ==>  Q" =                                   %
%   |- ((?x.P) ==> Q) = (!x'. P[x'/x] ==> Q)                                %
% ------------------------------------------------------------------------- %

    let LEFT_IMP_PEXISTS_CONV tm =
	(let (x,P),Q = (dest_pexists # I) (dest_imp tm) in
	let f = mk_pabs(x,P) in
	let th = SYM (ISPECL [Q;f] LEFT_FORALL_IMP_THM) in
	let th1 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
		    (RAND_CONV ETA_CONV)))))
		th in
	let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th1
	in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV
		    (RATOR_CONV (RAND_CONV PBETA_CONV)))))
		th2
	) ? failwith `LEFT_IMP_PEXISTS_CONV: expecting "(?p.P) ==> Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_IMP_PFORALL_CONV "P ==> (!x.Q)" =                                   %
%   |- (P ==> (!x.Q)) = (!x'. P ==> (Q[x'/x])                               %
% ------------------------------------------------------------------------- %

    let RIGHT_IMP_PFORALL_CONV tm =
	(let (P,(x,Q)) = (I # dest_pforall) (dest_imp tm) in
	let g = mk_pabs(x,Q) in
	let th1 = SYM (ISPECL [P;g] RIGHT_FORALL_IMP_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
	in
	    th4
	) ? failwith `RIGHT_IMP_FORALL_CONV: expecting "P ==> (!x.Q)"`;;

% ------------------------------------------------------------------------- %
% PEXISTS_IMP_CONV, implements the following axiom schemes.                 %
%                                                                           %
%       |- (?x. P==>Q[x]) = (P ==> (?x.Q[x]))     [x not free in P]         %
%                                                                           %
%       |- (?x. P[x]==>Q) = ((!x.P[x]) ==> Q)     [x not free in Q]         %
%                                                                           %
%       |- (?x. P==>Q) = ((!x.P) ==> (?x.Q))      [x not free in P==>Q]     %
% ------------------------------------------------------------------------- %

    let PEXISTS_IMP_CONV tm =
	(let (x,(P,Q)) = (I # dest_imp) (dest_pexists tm) ?
	    failwith `expecting "?x. P ==> Q"` in
	let oP = occs_in x P and oQ =  occs_in x Q in
	    if (oP & oQ) then
		failwith `bound pair occurs in both sides of "==>"`
	    else if ((not oP) & (not oQ)) then
		let th1 =
		    INST_TYPE
			[(type_of x, mk_vartype `*`)]
			BOTH_EXISTS_IMP_THM in
		let th2 = SPECL [P;Q] th1 in
		let th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 in
		let th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 in
		let th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
		in
		    th5
	    else if oP then % not free in Q %
		let f = mk_pabs(x,P) in
		let th1 = ISPECL [Q;f] LEFT_EXISTS_IMP_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV))))))
			th2 in
		let th4 = 
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    ETA_CONV))))
			th3
		in
		    th4
	    else % not free in P%
		let g = mk_pabs(x,Q) in
		let th1 = ISPECL [P;g] RIGHT_EXISTS_IMP_THM in
		let th2 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th1 in
		let th3 = 
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RAND_CONV PBETA_CONV)))))
			th2 in
		let th4 = 
		    CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))) th3
		in
		    th4
	) ?\st failwith `PEXISTS_IMP_CONV: `^st;;

% ------------------------------------------------------------------------- %
% LEFT_IMP_PFORALL_CONV "(!x. t1[x]) ==> t2" =                              %
%   |- (!x. t1[x]) ==> t2 = (?x'. t1[x'] ==> t2)                            %
% ------------------------------------------------------------------------- %

    let LEFT_IMP_PFORALL_CONV tm =
	(let ((x,P),Q) = (dest_pforall # I) (dest_imp tm) in
	let f = mk_pabs(x,P) in
	let th1 = SYM (ISPECL [Q;f] LEFT_EXISTS_IMP_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV
		    (RATOR_CONV (RAND_CONV PBETA_CONV)))))
		th3
	in
	    th4
	) ? failwith `LEFT_IMP_PFORALL_CONV: expecting "(!x.P) ==> Q"`;;

% ------------------------------------------------------------------------- %
% RIGHT_IMP_EXISTS_CONV "t1 ==> (?x. t2)" =                                 %
%   |- (t1 ==> ?x. t2) = (?x'. t1 ==> t2[x'/x])                             %
% ------------------------------------------------------------------------- %

    let RIGHT_IMP_PEXISTS_CONV tm =
	(let (P,(x,Q)) = (I # dest_pexists) (dest_imp tm) in
	let g = mk_pabs(x,Q) in
	let th1 = SYM (ISPECL [P;g] RIGHT_EXISTS_IMP_THM) in
	let th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 in
	let th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 in
	let th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
	in
	    th4
	) ? failwith `RIGHT_IMP_PEXISTS_CONV: expecting "P ==> (!x.Q)"`;;

    (
	NOT_PFORALL_CONV,
	NOT_PEXISTS_CONV,
	PEXISTS_NOT_CONV,
	PFORALL_NOT_CONV,
	PFORALL_AND_CONV,
	PEXISTS_OR_CONV,
	AND_PFORALL_CONV,
	LEFT_AND_PFORALL_CONV,
	RIGHT_AND_PFORALL_CONV,
	OR_PEXISTS_CONV,
	LEFT_OR_PEXISTS_CONV,
	RIGHT_OR_PEXISTS_CONV,
	PEXISTS_AND_CONV,
	AND_PEXISTS_CONV,
	LEFT_AND_PEXISTS_CONV,
	RIGHT_AND_PEXISTS_CONV,
	PFORALL_OR_CONV,
	OR_PFORALL_CONV,
	LEFT_OR_PFORALL_CONV,
	RIGHT_OR_PFORALL_CONV,
	PFORALL_IMP_CONV,
	LEFT_IMP_PEXISTS_CONV,
	RIGHT_IMP_PFORALL_CONV,
	PEXISTS_IMP_CONV,
	LEFT_IMP_PFORALL_CONV,
	RIGHT_IMP_PEXISTS_CONV
    );;
end_section convsec;;
let (
	NOT_PFORALL_CONV,
	NOT_PEXISTS_CONV,
	PEXISTS_NOT_CONV,
	PFORALL_NOT_CONV,
	PFORALL_AND_CONV,
	PEXISTS_OR_CONV,
	AND_PFORALL_CONV,
	LEFT_AND_PFORALL_CONV,
	RIGHT_AND_PFORALL_CONV,
	OR_PEXISTS_CONV,
	LEFT_OR_PEXISTS_CONV,
	RIGHT_OR_PEXISTS_CONV,
	PEXISTS_AND_CONV,
	AND_PEXISTS_CONV,
	LEFT_AND_PEXISTS_CONV,
	RIGHT_AND_PEXISTS_CONV,
	PFORALL_OR_CONV,
	OR_PFORALL_CONV,
	LEFT_OR_PFORALL_CONV,
	RIGHT_OR_PFORALL_CONV,
	PFORALL_IMP_CONV,
	LEFT_IMP_PEXISTS_CONV,
	RIGHT_IMP_PFORALL_CONV,
	PEXISTS_IMP_CONV,
	LEFT_IMP_PFORALL_CONV,
	RIGHT_IMP_PEXISTS_CONV
    ) = it;;
