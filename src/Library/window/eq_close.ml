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
% CONTENTS: window infernce rules preserving equality                        %
%============================================================================%
%$Id: eq_close.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

begin_section eq_close;;

let CONJ1_THM =
    prove
    (
        "!A B C. (B ==> (C = A)) ==> ((C /\ B) = (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    );;

%        (B |- C = A)                                                       %
% --------------------------    CONJ1_CLOSE "A /\ B"                        %
%  (|- (C /\ B) = (A /\ B))                                                 %
let CONJ1_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] CONJ1_THM) (DISCH b th) ;;

let CONJ2_THM =
    prove
    (
        "!A B C. (A ==> (C = B)) ==> ((A /\ C) = (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    );;

%        (A |- C = B)                                                       %
% --------------------------    CONJ2_CLOSE "A /\ B"                        %
%  (|- (A /\ C) = (A /\ B))                                                 %
let CONJ2_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] CONJ2_THM) (DISCH a th) ;;

let IMP1_THM =
    prove
    (
        "!A B C. (~B ==> (C = A)) ==> ((C ==> B) = (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;
            
%         (~B |- C = A)                                                     %
% ----------------------------  IMP1_CLOSE "A ==> B"                        %
%  (|- (C ==> B) = (A ==> B))                                               %
let IMP1_CLOSE tm th = 
    let (a,b) = dest_imp tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP1_THM) (DISCH (mk_neg b) th) ;;

let IMP2_THM =
    prove
    (
        "!A B C. (A ==> (C = B)) ==> ((A ==> C) = (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;

%         (A |- C = B)                                                      %
% ----------------------------  IMP2_CLOSE "A ==> B"                        %
%  (|- (A ==> C) = (A ==> B))                                               %
let IMP2_CLOSE tm th =
    let (a,b) = dest_imp tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP2_THM) (DISCH a th) ;;

let PMI1_THM =
    prove
    (
        "!A B C. (B ==> (C = A)) ==> ((C <== B) = (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (PURE_REWRITE_TAC [PMI_DEF]) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;

%         (B |- C = A)                                                      %
% ----------------------------  PMI1_CLOSE "A <== B"                        %
%  (|- (C <== B) = (A <== B))                                               %
let PMI1_CLOSE tm th = 
    let (a,b) = dest_pmi tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] PMI1_THM) (DISCH b th) ;;

let PMI2_THM =
    prove
    (
        "!A B C. (~A ==> (C = B)) ==> ((A <== C) = (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (PURE_REWRITE_TAC [PMI_DEF]) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;

%         (~A |- C = B)                                                     %
% ----------------------------  PMI2_CLOSE "A <== B"                        %
%  (|- (A <== C) = (A <== B))                                               %
let PMI2_CLOSE tm th = 
    let (a,b) = dest_pmi tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] PMI2_THM) (DISCH (mk_neg a) th) ;;

let DISJ1_THM =
    prove
    (
        "!A B C. (~B ==> (C = A)) ==> ((C \/ B) = (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;

%        (~B |- C = A)                                                      %
% --------------------------    DISJ1_CLOSE "A \/ B"                        %
%  (|- (C \/ B) = (A \/ B))                                                 %
let DISJ1_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] DISJ1_THM) (DISCH (mk_neg b) th) ;;

let DISJ2_THM =
    prove
    (
        "!A B C. (~A ==> (C = B)) ==> ((A \/ C) = (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        BOOL_CASES_TAC "A:bool" THEN
        BOOL_CASES_TAC "B:bool" THEN
        REWRITE_TAC []
    ) ;;

%        (~A |- C = B)                                                      %
% ---------------------------   DISJ2_CLOSE "A \/ B"                        %
%  (|- (A \/ C) = (A \/ B))                                                 %
let DISJ2_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] DISJ2_THM) (DISCH (mk_neg a) th) ;;

% Put all those rules in the data base.                                     %

store_rule
    (
        [RATOR; RAND],
        is_conj,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        CONJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_conj,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl), 
        K [],
        CONJ2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_trueimp,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        IMP1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_trueimp,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl),
        K [],
        IMP2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_pmi,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        PMI1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_pmi,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        PMI2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_disj,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        DISJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_disj,
        K (K equiv_tm),
        K (K equiv_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        DISJ2_CLOSE
    );;

end_section eq_close.ml
