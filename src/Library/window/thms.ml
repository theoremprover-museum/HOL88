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
% CONTENTS: miscelaneous theorems                                            %
%============================================================================%
%$Id: thms.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

let PMI_DEF = definition (`win`) `PMI_DEF`;;

% |- !x. x ==> x                                                            %
let IMP_REFL_THM = 
    prove
    (
        "!x. x ==> x"
    ,
        GEN_TAC THEN
        DISCH_TAC THEN
        (ASM_REWRITE_TAC [])
    ) ;;

% |- !x y z. (x ==> y) /\ (y ==> z) ==> x ==> z                             %
let IMP_TRANS_THM =
    prove
    (
        "!x y z. ((x ==> y) /\ (y ==> z)) ==> (x ==> z)"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "x:bool") THEN
        (BOOL_CASES_TAC "y:bool") THEN
        (REWRITE_TAC [])
    );;

% |- !x. x <== x                                                            %
let PMI_REFL_THM =
    prove
    (
        "!x. x <== x"
    ,
        GEN_TAC THEN
        (REWRITE_TAC [PMI_DEF]) THEN
        DISCH_TAC THEN
        (ASM_REWRITE_TAC [])
    );;
    
% |- !x y z. x <== y /\ y <== z ==> x <== z                                 %
let PMI_TRANS_THM =
    prove
    (
        "!x y z. ((x <==y) /\ (y <== z)) ==> (x <== z)"
    ,
        (REPEAT GEN_TAC) THEN
        (BOOL_CASES_TAC "x:bool") THEN
        (BOOL_CASES_TAC "y:bool") THEN
        (REWRITE_TAC [PMI_DEF])
    );;
