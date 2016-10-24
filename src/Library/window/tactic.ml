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
% CONTENTS: tactics for interfacing subgoal and window proof.                %
%============================================================================%
%$Id: tactic.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

% Open a subwindow on the goal, transform it, close it,                 %
%   transform the goal.                                                 %
let open_TAC p thms f gl =
    let (hyps, foc) = gl in
    let win = create_win (mk_comb (imp_tm, foc)) (term_setify hyps) thms in
    let (subwin, close) = open_win_basis (FOCUS_PATH p) win in
    let th = win_thm (close (f subwin) win) in
        MATCH_MP_TAC th gl;;

% When we create a stack for a tactic, we do not place a window whose focus %
% is the current subgoal on the stack.   The stack starts at the indicated  %
% subterm.   However, we need to store this bottom window and the close     %
% function to get back from the window we store to the bottom window in     %
% order for the whole thing to work.   Hence this table of windows and      %
% close functions called close_table.                                       %
begin_section tacsec;;
    letref close_table = [] :
        (string # (window # (window -> window -> window))) list;;

    let BEGIN_STACK_TAC name p thms gl =
        let (hyps, foc) = gl in
        let shyps = term_setify hyps in
        let win = create_win (mk_comb (imp_tm, foc)) shyps thms in
        let (subwin, close) = open_win_basis (FOCUS_PATH p) win in
        let subfoc = focus subwin in
        let subrel = relation subwin in
            BEGIN_STACK name (mk_comb (subrel, subfoc)) shyps thms;
            close_table := (name,(win,close)).close_table;
            ALL_TAC gl;;

    let END_STACK_TAC name =
        if mem name (map fst close_table) then
            let (_,(win,close)) = assoc name close_table in
            letref the_stack = GET_STACK name in
            let th =
                while (not ((depth_stack the_stack) = 1)) do
                (
                    the_stack := close_window the_stack
                );
                win_thm (close (top_window the_stack) win)
            in
                END_STACK name;
                close_table := filter (\(n,_). (not (n = name))) close_table;
                MATCH_MP_TAC th
        else
            failwith `END_STACK_TAC: not a tactic based stack`;;
        
    (BEGIN_STACK_TAC, END_STACK_TAC);;
end_section tacsec;;
let (BEGIN_STACK_TAC, END_STACK_TAC) = it;;
