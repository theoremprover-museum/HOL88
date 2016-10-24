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
% CONTENTS: window inference preserving implication (and backward implies)   %
%============================================================================%
%$Id: imp_close.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

begin_section imp_close;;

let IMP_CONJ1_THM =
    prove
    (
        "!A B C. (B ==> (C ==> A)) ==> ((C /\ B) ==> (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (B |- C ==> A)                                                     %
% ----------------------------  IMP_CONJ1_CLOSE "A /\ B"                    %
%  (|- (C /\ B) ==> (A /\ B))                                               %
let IMP_CONJ1_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] IMP_CONJ1_THM) (DISCH b th) ;;

let IMP_CONJ2_THM =
    prove
    (
        "!A B C. (A ==> (C ==> B)) ==> ((A /\ C) ==> (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (A |- C ==> B)                                                     %
% ----------------------------  IMP_CONJ2_CLOSE "A /\ B"                    %
%  (|- (A /\ C) ==> (A /\ B))                                               %
let IMP_CONJ2_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] IMP_CONJ2_THM) (DISCH a th) ;;

let IMP_IMP1_THM =
    prove
    (
        "!A B C. (~B ==> (C <== A)) ==> ((C ==> B) ==> (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (~B |- C <== A)                                                   %
% ------------------------------    IMP_IMP1_CLOSE "A ==> B"                %
%  (|- (C ==> B) ==> (A ==> B))                                             %
let IMP_IMP1_CLOSE tm th = 
    let (a,b) = dest_imp tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_IMP1_THM) (DISCH (mk_neg b) th) ;;

let IMP_IMP2_THM =
    prove
    (
        "!A B C. (A ==> (C ==> B)) ==> ((A ==> C) ==> (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (A |- C ==> B)                                                    %
% ------------------------------    IMP_IMP2_CLOSE "A ==> B"                %
%  (|- (A ==> C) ==> (A ==> B))                                             %
let IMP_IMP2_CLOSE tm th =
    let (a,b) = dest_imp tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_IMP2_THM) (DISCH a th) ;;
    
let IMP_PMI1_THM =
    prove
    (
        "!A B C. (B ==> (C ==> A)) ==> ((C <== B) ==> (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (B |- C ==> A)                                                    %
% ------------------------------    IMP_PMI1_CLOSE "A <== B"                %
%  (|- (C <== B) ==> (A <== B))                                             %
let IMP_PMI1_CLOSE tm th =
    let (a,b) = dest_pmi tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_PMI1_THM) (DISCH b th) ;;

let IMP_PMI2_THM =
    prove
    (
        "!A B C. (~A ==> (C <== B)) ==> ((A <== C) ==> (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;
    
%         (~A |- C <== B)                                                   %
% ------------------------------    IMP_PMI2_CLOSE "A <== B"                %
%  (|- (A <== C) ==> (A <== B))                                             %
let IMP_PMI2_CLOSE tm th = 
    let (a,b) = dest_pmi tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_PMI2_THM) (DISCH (mk_neg a) th) ;;

let IMP_DISJ1_THM =
    prove
    (
        "!A B C. (~B ==> (C ==> A)) ==> ((C \/ B) ==> (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (~B |- C ==> A)                                                    %
% ----------------------------  IMP_DISJ1_CLOSE "A \/ B"                    %
%  (|- (C \/ B) ==> (A \/ B))                                               %
let IMP_DISJ1_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_DISJ1_THM) (DISCH (mk_neg b) th) ;;

let IMP_DISJ2_THM =
    prove
    (
        "!A B C. (~A ==> (C ==> B)) ==> ((A \/ C) ==> (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (~A |- C ==> B)                                                    %
% ----------------------------  IMP_DISJ2_CLOSE "A \/ B"                    %
%  (|- (A \/ C) ==> (A \/ B))                                               %
let IMP_DISJ2_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = (rand (rator (concl th))) in
        MP (SPECL [a; b; c] IMP_DISJ2_THM) (DISCH (mk_neg a) th) ;;

let IMP_NEG_THM =
    prove
    (
        "!A B. (B <== A) ==> ((~B) ==> (~A))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%      (|- B <== A)                                                         %
% --------------------   IMP_NEG_CLOSE "~A"                                 %
%  (|- (~B) ==> (~A))                                                       %
let IMP_NEG_CLOSE (tm:term) th =
    let (b,a) = dest_pmi (concl th) in
        MP (SPECL [a; b] IMP_NEG_THM) th ;;

%      (|- B ==> A)                                                         %
% -----------------------   IMP_ALL_CLOSE "!v.A"                            %
%  (|- (!v.B) ==> (!v.A)                                                    %
let IMP_ALL_CLOSE tm th =
    let (v,a) = dest_forall tm in
    let b = rand (rator (concl th)) in
        DISCH
            (mk_forall (v,b))
            (GEN v (MP th (SPEC v (ASSUME (mk_forall (v,b))))));;

%      (|- B ==> A)                                                         %
% -----------------------   IMP_EXISTS_CLOSE "?v.A"                         %
%  (|- (?v.B) ==> (?v.A)                                                    %
let IMP_EXISTS_CLOSE tm th = EXISTS_IMP (bndvar (rand tm)) th;;

let PMI_CONJ1_THM =
    prove
    (
        "!A B C. (B ==> (C <== A)) ==> ((C /\ B) <== (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (B |- C <== A)                                                     %
% ----------------------------  PMI_CONJ1_CLOSE "A /\ B"                    %
%  (|- (C /\ B) <== (A /\ B))                                               %
let PMI_CONJ1_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_CONJ1_THM) (DISCH b th) ;;

let PMI_CONJ2_THM =
    prove
    (
        "!A B C. (A ==> (C <== B)) ==> ((A /\ C) <== (A /\ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (A |- C <== B)                                                     %
% ----------------------------  PMI_CONJ2_CLOSE "A /\ B"                    %
%  (|- (A /\ C) <== (A /\ B))                                               %
let PMI_CONJ2_CLOSE tm th =
    let (a,b) = dest_conj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_CONJ2_THM) (DISCH a th) ;;

let PMI_IMP1_THM =
    prove
    (
        "!A B C. (~B ==> (C ==> A)) ==> ((C ==> B) <== (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (~B |- C ==> A)                                                   %
% ------------------------------    PMI_IMP1_CLOSE "A ==> B"                %
%  (|- (C ==> B) <== (A ==> B))                                             %
let PMI_IMP1_CLOSE tm th =
    let (a,b) = dest_imp tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_IMP1_THM) (DISCH (mk_neg b) th) ;;

let PMI_IMP2_THM =
    prove
    (
        "!A B C. (A ==> (C <== B)) ==> ((A ==> C) <== (A ==> B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (A |- C <== B)                                                    %
% ------------------------------    PMI_IMP2_CLOSE "A ==> B"                %
%  (|- (A ==> C) <== (A ==> B))                                             %
let PMI_IMP2_CLOSE tm th =
    let (a,b) = dest_imp tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_IMP2_THM) (DISCH a th) ;;

let PMI_PMI1_THM =
    prove
    (
        "!A B C. (B ==> (C <== A)) ==> ((C <== B) <== (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (B |- C <== A)                                                    %
% ------------------------------    PMI_PMI1_CLOSE "A <== B"                %
%  (|- (C <== B) <== (A <== B))                                             %
let PMI_PMI1_CLOSE tm th =
    let (a,b) = dest_pmi tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_PMI1_THM) (DISCH b th) ;;

let PMI_PMI2_THM =
    prove
    (
        "!A B C. (~A ==> (C ==> B)) ==> ((A <== C) <== (A <== B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%         (~A |- C ==> B)                                                   %
% ------------------------------    PMI_PMI2_CLOSE "A <== B"                %
%  (|- (A <== C) <== (A <== B))                                             %
let PMI_PMI2_CLOSE tm th =
    let (a,b) = dest_pmi tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_PMI2_THM) (DISCH (mk_neg a) th) ;;

let PMI_DISJ1_THM =
    prove
    (
        "!A B C. (~B ==> (C <== A)) ==> ((C \/ B) <== (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (~B |- C <== A)                                                    %
% ----------------------------  PMI_DISJ1_CLOSE "A \/ B"                    %
%  (|- (C \/ B) <== (A \/ B))                                               %
let PMI_DISJ1_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_DISJ1_THM) (DISCH (mk_neg b) th) ;;

let PMI_DISJ2_THM =
    prove
    (
        "!A B C. (~A ==> (C <== B)) ==> ((A \/ C) <== (A \/ B))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (BOOL_CASES_TAC "B:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%        (~A |- C <== B)                                                    %
% ----------------------------  PMI_DISJ2_CLOSE "A \/ B"                    %
%  (|- (A \/ C) <== (A \/ B))                                               %
let PMI_DISJ2_CLOSE tm th =
    let (a,b) = dest_disj tm in
    let c = rand (rator (concl th)) in
        MP (SPECL [a; b; c] PMI_DISJ2_THM) (DISCH (mk_neg a) th) ;;

let PMI_NEG_THM =
    prove
    (
        "!A B. (B ==> A) ==> ((~B) <== (~A))"
    ,
        (REPEAT GEN_TAC) THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        (BOOL_CASES_TAC "A:bool") THEN
        (REWRITE_TAC [])
    ) ;;

%    (|- B ==> A)                                                           %
% -------------------   PMI_NEG_CLOSE "~A"                                  %
%  (|- (~B) <== (~A)                                                        %
let PMI_NEG_CLOSE (tm:term) th =
    let (b,a) = dest_imp (concl th) in
        MP (SPECL [a; b] PMI_NEG_THM) th ;;

%      (|- B <== A)                                                         %
% -----------------------   PMI_ALL_CLOSE "!v.A"                            %
%  (|- (!v.B) <== (!v.A)                                                    %
let PMI_ALL_CLOSE tm th =
    let b = rand (rator (concl th)) in
    let v = bndvar (rand tm) in
        IMP_PMI (IMP_ALL_CLOSE (mk_forall (v,b)) (PMI_IMP th));;

%      (|- B <== A)                                                         %
% -----------------------   PMI_EXIST_CLOSE "?v.A"                          %
%  (|- (?v.B) <== (?v.A)                                                    %
let PMI_EXISTS_CLOSE tm th =
    let b = rand (rator (concl th)) in
    let v = bndvar (rand tm) in
        IMP_PMI (IMP_EXISTS_CLOSE (mk_exists (v,b)) (PMI_IMP th));;

% Put all these rules in the database.                                      %

store_rule
    (
        [RATOR; RAND],
        is_conj,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        IMP_CONJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_conj,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl), 
        K [],
        IMP_CONJ2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_trueimp,
        K (K pmi_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        IMP_IMP1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_trueimp,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl),
        K [],
        IMP_IMP2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_pmi,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        IMP_PMI1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_pmi,
        K (K pmi_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        IMP_PMI2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_disj,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        IMP_DISJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_disj,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        IMP_DISJ2_CLOSE
    );;
store_rule
    (
        [RAND],
        is_neg,
        K (K pmi_tm),
        K (K imp_tm),
        K I,
        K [],
        IMP_NEG_CLOSE
    );;
store_rule
    (
        [RAND; BODY],
        is_forall,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl.
            filter (\th. not (mem (bndvar (rand tm)) (thm_frees th))) tl),
        (\foc. [bndvar (rand foc)]),
        IMP_ALL_CLOSE
        );;
store_rule
    (
        [RAND; BODY],
        is_exists,
        K (K imp_tm),
        K (K imp_tm),
        (\tm.\tl.
            filter (\th. not (mem (bndvar (rand tm)) (thm_frees th))) tl),
        (\foc. [bndvar (rand foc)]),
        IMP_EXISTS_CLOSE
        );;
store_rule
    (
        [RATOR; RAND],
        is_conj,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        PMI_CONJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_conj,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl), 
        K [],
        PMI_CONJ2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_trueimp,
        K (K imp_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        PMI_IMP1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_trueimp,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (rand (rator tm)))) @ tl),
        K [],
        PMI_IMP2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_pmi,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (rand tm))) @ tl),
        K [],
        PMI_PMI1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_pmi,
        K (K imp_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        PMI_PMI2_CLOSE
    );;
store_rule
    (
        [RATOR; RAND],
        is_disj,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand tm)))) @ tl),
        K [],
        PMI_DISJ1_CLOSE
    );;
store_rule
    (
        [RAND],
        is_disj,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl. (SMASH (ASSUME (mk_neg (rand (rator tm))))) @ tl),
        K [],
        PMI_DISJ2_CLOSE
    );;
store_rule
    (
        [RAND],
        is_neg,
        K (K imp_tm),
        K (K pmi_tm),
        K I,
        K [],
        PMI_NEG_CLOSE
    );;
store_rule
    (
        [RAND; BODY],
        is_forall,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl.
            filter (\th. not (mem (bndvar (rand tm)) (thm_frees th))) tl),
        K [],
        PMI_ALL_CLOSE
        );;
store_rule
    (
        [RAND; BODY],
        is_exists,
        K (K pmi_tm),
        K (K pmi_tm),
        (\tm.\tl.
            filter (\th. not (mem (bndvar (rand tm)) (thm_frees th))) tl),
        K [],
        PMI_EXISTS_CLOSE
        );;

end_section imp_close;;
