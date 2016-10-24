% --------------------------------------------------------------------- %
%       Copyright (c) Jim Grundy 1992                                   %
%       All rights reserved                                             %
%                                                                       %
% Jim Grundy, hereafter referred to as `the Author', retains the        %
% copyright and all other legal rights to the Software contained in     %
% this file, hereafter referred to as `the Software'.                   %
%                                                                       %
% The Software is made available free of charge on an `as is' basis.    %
% No guarantee, either express or implied, of maintenance, reliability, %
% merchantability or suitability for any purpose is made by the Author. %
%                                                                       %
% The user is granted the right to make personal or internal use        %
% of the Software provided that both:                                   %
% 1. The Software is not used for commercial gain.                      %
% 2. The user shall not hold the Author liable for any consequences     %
%    arising from use of the Software.                                  %
%                                                                       %
% The user is granted the right to further distribute the Software      %
% provided that both:                                                   %
% 1. The Software and this statement of rights is not modified.         %
% 2. The Software does not form part or the whole of a system           %
%    distributed for commercial gain.                                   %
%                                                                       %
% The user is granted the right to modify the Software for personal or  %
% internal use provided that all of the following conditions are        %
% observed:                                                             %
% 1. The user does not distribute the modified software.                %
% 2. The modified software is not used for commercial gain.             %
% 3. The Author retains all rights to the modified software.            %
%                                                                       %
% Anyone seeking a licence to use this software for commercial purposes %
% is invited to contact the Author.                                     %
% --------------------------------------------------------------------- %
%============================================================================%
% CONTENTS: generic and basic window inference rules                         %
%============================================================================%
%$Id: basic_close.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

begin_section basic_close;;

%      (|- f = g)                                                           %
% --------------------  RATOR_CLOSE "g x"                                   %
%  (|- (f x) = (g x))                                                       %
let RATOR_CLOSE tm th = (AP_THM th (rand tm)) ? failwith `RATOR_CLOSE`;;

%      (|- y = x)                                                           %
% --------------------- RAND_CLOSE "f x"                                    %
%  (|- (f y) = (f x))                                                       %
let RAND_CLOSE tm th = (AP_TERM (rator tm) th) ? failwith `RAND_CLOSE`;;

%       (|- t = u)                                                          % 
% ---------------------- BODY_CLOSE "\x.u"                                  %
%  (|- (\x.t) = (\x.u))                                                     %
let BODY_CLOSE tm th = (ABS (bndvar tm) th) ? failwith `BODY_CONV`;;

let COND1_THM =
    prove
    (
        "!R A B C D. (!x:*. R x x) ==>
            (A ==> R D B) ==> (R (A => D | C) (A => B | C))"
    ,
        (REPEAT GEN_TAC) THEN
        DISCH_TAC THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (ASM_REWRITE_TAC [])
    ) ;;

%            (A |- D R B)                                                   %
% --------------------------------- COND1_CLOSE "A => B | C"                %
%  (|- (A => D | C) R (A => B | C)                                          %
let COND1_CLOSE tm th =
    let (a,b,c) = dest_cond tm in
    let d = rand (rator (concl th)) in
    let r = rator (rator (concl th)) in
    let x = genvar (type_of b) in
    let rref = GEN x (reflexive (mk_comb ((mk_comb (r, x)), x))) in
        MP (MP (ISPECL [r; a; b; c; d] COND1_THM) rref) (DISCH a th) ;;

let COND2_THM =
    prove
    (
        "!R A B C D. (!x:*. R x x) ==>
            ((~A) ==> R D C) ==> (R (A => B | D) (A => B | C))"
    ,
        (REPEAT GEN_TAC) THEN
        DISCH_TAC THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (ASM_REWRITE_TAC [])
    ) ;;

%          (~A |- D R C)                                                    %
% --------------------------------- COND2_CLOSE "A => B | C"                %
%  (|- (A => B | D) R (A => B | C)                                          %
let COND2_CLOSE tm th =
    let (a,b,c) = dest_cond tm in
    let d = rand (rator (concl th)) in
    let r = rator (rator (concl th)) in
    let x = genvar (type_of c) in
    let rref = GEN x (reflexive (mk_comb ((mk_comb (r, x)), x))) in
        MP (MP (ISPECL [r; a; b; c; d] COND2_THM) rref) (DISCH (mk_neg a) th) ;;

let BODY2_THM =
    prove
    (
        "!(c:*) (f:*->**) (g:*->**) (r:**->**->bool).
            (!v:*. (v=c) ==> (r (f v) (g v))) ==> (r (f c) (g c))"
    ,
        (REPEAT STRIP_TAC) THEN
        (REWRITE_TAC 
            [REWRITE_RULE
                []
                (SPEC
                    "c:*"
                    (ASSUME "!v:*. (v = c) ==> (r:**->**->bool)(f v)(g v)"))])
    );;

%        (v = c |- u R t)                                                   %
% ----------------------------- BODY2_CLOSE "((\v.t) c)"                    %
%  (|- ((\v.u) c) R ((\v.t) c)                                              %
let BODY2_CLOSE tm th =
    let ((v,t),c) = (dest_abs # I) (dest_comb tm) in
    let u = rand (rator (concl th)) in
    let r = rator (rator (concl th)) in
    if mem v (flat (map frees (hyp th))) then
        let t1 = GEN v (DISCH (mk_eq(v,c)) th) in
        let t2 = ISPECL [c; mk_abs(v,u); mk_abs(v,t); r] BODY2_THM in
        let t3 =
            CONV_RULE
                (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                    (RATOR_CONV (RAND_CONV BETA_CONV)))))))
                t2 in
        let t4 =
            CONV_RULE
                (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
                    (RAND_CONV BETA_CONV))))))
                t3 in
            MP t4 t1
    else
        let t1 = BETA_CONV (mk_comb(mk_abs(v,u),v)) in
        let t2 = SYM (BETA_CONV (mk_comb(mk_abs(v,t),v))) in
            INST [(c,v)] (transitive (CONJ (transitive (CONJ t1 th)) t2)) ;;

let LET_THM =
    prove
    (
        "!(c:*) (f:*->**) (g:*->**) (r:**->**->bool).
            (!v:*. (v=c) ==> (r (f v) (g v))) ==>
                (r (LET f c) (LET g c))"
    ,
        (REPEAT STRIP_TAC) THEN
        (PURE_ONCE_REWRITE_TAC [LET_DEF]) THEN
        BETA_TAC THEN
        (REWRITE_TAC
            [REWRITE_RULE
                []
                (SPEC
                    "c:*"
                    (ASSUME "!v:*. (v = c) ==> (r:**->**->bool)(f v)(g v)"))])
    );;

%             (v = c |- u R t)                                              %
% ----------------------------------------- LET_CLOSE "let v = c in t"      %
%  (|- (let v = c in u) R (let v = c in t)                                  %
let LET_CLOSE tm th =
    let ((v,t),c) = (dest_abs # I) (dest_let tm) in
    let u = rand (rator (concl th)) in
    let r = rator (rator (concl th)) in
    let t1 = GEN v (DISCH (mk_eq(v,c)) th) in
    let t2 = ISPECL [c; mk_abs(v,u); mk_abs(v,t); r] LET_THM in
    let t3 =    
	CONV_RULE
	    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
		(RATOR_CONV (RAND_CONV BETA_CONV)))))))
	    t2 in
    let t4 =    
	CONV_RULE
	    (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV (RAND_CONV
		(RAND_CONV BETA_CONV))))))
	    t3 in
	MP t4 t1;;

% Put all those rules in the data base.                                     %

store_rule
    (
        [RATOR], 
        is_comb, 
        (\targ.\rel.
            let ty = type_of (rator targ) in
                mk_const
                (
                    `=`
                ,
                    mk_type (`fun`, [ty; mk_type(`fun`, [ty; bool_ty])])
                )),  
        (\targ.\rel. mk_const(`=`, type_of rel)),
        KI, 
        K [],
        RATOR_CLOSE
    );;
store_rule
    (
        [RAND],
        is_comb,
        (
            \targ.\rel.
                let ty = type_of (rand targ) in
                    mk_const
                    (
                        `=`
                    ,
                        mk_type (`fun`, [ty; mk_type(`fun`, [ty; bool_ty])])
                    )
        ),
        (\targ.\rel. mk_const(`=`, type_of rel)),
        KI,
        K [],
        RAND_CLOSE
    );;
store_rule
    (
        [BODY],
        is_abs, 
        (
            \targ.\rel.
                let ty = ran targ in
                    mk_const
                    (
                        `=`
                    ,
                        mk_type (`fun`, [ty; mk_type(`fun`, [ty; bool_ty])])
                    )
        ),
        (\targ.\rel. mk_const(`=`, type_of rel)),
        (\tm.\tl. (filter (\th. not (mem (bndvar tm) (thm_frees th))) tl)),
        (\tm. [bndvar tm]),
        BODY_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_cond,
        K I,
        K I,
        (\tm.\tl. (SMASH (ASSUME (rand (rator (rator tm))))) @ tl),
        K [],
        COND1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_cond,
        K I,
        K I,
        (\tm.\tl.
            (SMASH (ASSUME (mk_neg (rand (rator (rator tm)))))) @ tl),
        K [],
        COND2_CLOSE
    );;
store_rule
    (
        [RATOR; BODY],
        (\tm. (is_comb tm) & (is_abs (rator tm))),
        K I,
        K I,
        (\tm.\tl.
            let v = bndvar (rator tm) in
                filter
                    (\th. not (mem v (thm_frees th)))
                    ((ASSUME (mk_eq (v, rand tm))).tl)),
        (\tm. [bndvar (rator tm)]),
        BODY2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND; BODY],
        (\tm. is_let tm),
        K I,
        K I,
        (\tm.\tl.
            let ((v,_),c) = (dest_abs # I) (dest_let tm) in
                (ASSUME (mk_eq (v,c))).
		(filter (\th. not (mem v (thm_frees th))) tl)),
        (\foc. [bndvar (rand (rator foc))]),
        LET_CLOSE
    );;
