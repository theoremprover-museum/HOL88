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
% CONTENTS: functions which are common to paried universal and		%
%		existentail quantifications.				%
% --------------------------------------------------------------------- %
%$Id: both1.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% ------------------------------------------------------------------------- %
% PFORALL_THM = |- !f. (!x y. f x y) = (!(x,y). f x y)                      %
% ------------------------------------------------------------------------- %

let PFORALL_THM =
    prove
    (
	"!f. (!(x:*) (y:**). f x y) = (!(x:*,y:**). f x y)"
    ,
	GEN_TAC THEN
	EQ_TAC THENL
	[
	    DISCH_TAC THEN
	    (REWRITE_TAC [FORALL_DEF]) THEN
	    BETA_TAC THEN
	    (ASM_REWRITE_TAC []) THEN
	    (CONV_TAC (RAND_CONV (PALPHA_CONV "(x:*,y:**)"))) THEN
	    REFL_TAC
	;
	    (CONV_TAC (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV "z:*#**")))) THEN
	    DISCH_TAC THEN
	    (CONV_TAC (RAND_CONV (ABS_CONV (RAND_CONV (ABS_CONV
		(RATOR_CONV (RAND_CONV (\tm. (SYM (SPEC_ALL FST)))))))))) THEN
	    (CONV_TAC (RAND_CONV (ABS_CONV (RAND_CONV (ABS_CONV
		(RAND_CONV (\tm. (SYM (SPEC_ALL SND)))))))))    THEN
	     (ASM_REWRITE_TAC [])
	]
    );;

% ------------------------------------------------------------------------- %
% PEXISTS_THM = |- !f. (?x y. f x y) = (?(x,y). f x y)                      %
% ------------------------------------------------------------------------- %

let PEXISTS_THM =
    prove
    (
	"!f. (?(x:*) (y:**). f x y) = (?(x:*,y:**). f x y)"
    ,
	GEN_TAC THEN
	EQ_TAC THENL
	[
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    DISCH_TAC THEN
	    (CONV_TAC (GEN_PALPHA_CONV "a:*#**")) THEN
	    (EXISTS_TAC "(x:*,y:**)") THEN
	    (ASM_REWRITE_TAC [FST; SND]) 
	;
	    (CONV_TAC (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV "a:*#**")))) THEN
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    DISCH_TAC THEN
	    (EXISTS_TAC "FST (a:*#**)") THEN
	    (EXISTS_TAC "SND (a:*#**)") THEN
	    (ASM_REWRITE_TAC [])
	]
    );;

% ------------------------------------------------------------------------- %
% CURRY_FORALL_CONV "!(x,y).t" = (|- (!(x,y).t) = (!x y.t))                 %
% ------------------------------------------------------------------------- %

let CURRY_FORALL_CONV tm = 
    (let (xy,bod) = dest_pforall tm in
    let (x,y) = dest_pair xy in
    let result = list_mk_pforall ([x;y],bod) in
    let f = rand (rand tm) in
    let th1 = RAND_CONV (PABS_CONV (UNPBETA_CONV xy)) tm in
    let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV CURRY_CONV))) th1 in
    let th3 = (SYM (ISPEC f PFORALL_THM)) in
    let th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV xy))) th3 in
    let th5 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV x)) (th2 TRANS th4) in
    let th6 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
			    (GEN_PALPHA_CONV y)))) th5 in
    let th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
			    (RATOR_CONV PBETA_CONV)))))) th6 in
    let th8 =
	CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
		    PBETA_CONV))))) th7
    in
        th8 TRANS (REFL result)
    )? failwith `CURRY_FORALL_CONV` ;;

% ------------------------------------------------------------------------- %
% CURRY_EXISTS_CONV "?(x,y).t" = (|- (?(x,y).t) = (?x y.t))                 %
% ------------------------------------------------------------------------- %

let CURRY_EXISTS_CONV tm = 
    (let (xy,bod) = dest_pexists tm in
    let (x,y) = dest_pair xy in
    let result = list_mk_pexists ([x;y],bod) in
    let f = rand (rand tm) in
    let th1 = RAND_CONV (PABS_CONV (UNPBETA_CONV xy)) tm in
    let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV CURRY_CONV))) th1 in
    let th3 = (SYM (ISPEC f PEXISTS_THM)) in
    let th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV xy))) th3 in
    let th5 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV x)) (th2 TRANS th4) in
    let th6 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
			    (GEN_PALPHA_CONV y)))) th5 in
    let th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
			    (RATOR_CONV PBETA_CONV)))))) th6 in
    let th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
		    PBETA_CONV))))) th7
    in 
	th8 TRANS (REFL result)
    )? failwith `CURRY_EXISTS_CONV` ;;

% ------------------------------------------------------------------------- %
% UNCURRY_FORALL_CONV "!x y.t" = (|- (!x y.t) = (!(x,y).t))                 %
% ------------------------------------------------------------------------- %

let UNCURRY_FORALL_CONV tm =
    (let (x,(y,bod)) = (I # dest_pforall) (dest_pforall tm) in
    let xy = mk_pair(x,y) in
    let result = mk_pforall (xy,bod) in
    let th1 = (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
		    (UNPBETA_CONV xy))))) tm in
    let f = rand (rator (pbody (rand (pbody (rand (rand (concl th1))))))) in
    let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
			    CURRY_CONV))))) th1 in
    let th3 = ISPEC f PFORALL_THM in
    let th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV x))) th3 in
    let th5 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		(GEN_PALPHA_CONV y))))) th4 in
    let th6 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV xy)) (th2 TRANS th5) in
    let th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV
			    PBETA_CONV)))) th6 in
    let th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV PBETA_CONV))) th7
    in
	th8 TRANS (REFL result)
    ) ? failwith `UNCURRY_FORALL_CONV`;;

% ------------------------------------------------------------------------- %
% UNCURRY_EXISTS_CONV "?x y.t" = (|- (?x y.t) = (?(x,y).t))                 %
% ------------------------------------------------------------------------- %

let UNCURRY_EXISTS_CONV tm =
    (let (x,(y,bod)) = (I # dest_pexists) (dest_pexists tm) in
    let xy = mk_pair(x,y) in
    let result = mk_pexists (xy,bod) in
    let th1 = (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
		    (UNPBETA_CONV xy))))) tm in
    let f = rand (rator (pbody (rand (pbody (rand (rand (concl th1))))))) in
    let th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
			    CURRY_CONV))))) th1 in
    let th3 = ISPEC f PEXISTS_THM in
    let th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV x))) th3 in
    let th5 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		(GEN_PALPHA_CONV y))))) th4 in
    let th6 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV xy)) (th2 TRANS th5) in
    let th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV
			    PBETA_CONV)))) th6 in
    let th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV PBETA_CONV))) th7
    in
	th8 TRANS (REFL result)
    ) ? failwith `UNCURRY_EXISTS_CONV`;;
