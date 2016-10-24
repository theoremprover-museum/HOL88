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
% CONTENTS: interactive front end to the window infernce library.            %
%============================================================================%
%$Id: inter.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

% In this file we extend the functional interface described in win.ml.  %
% This file desribes an interactive interface.                          %
% The interface is stack based.                                         %

% A General History Mechanism is defined.                               %
abstype * history  = (int # (* list) # (* list))
    %   Create a new history with intial size size and state state.     %
    with epoch size state =
            abs_history(size, [state],[])
    %   Return the current state of the history.                        %
    and present hist =
            let (_,pres._,_) = rep_history hist in
                pres
    %   Makes (event (present hist)) the current state.                 %
    and dodo event hist =
            let (size, pres.past,_) = rep_history hist in
                abs_history (size, first size ((event pres).pres.past) ,[])
    %   Undoes the last event.                                          %
    and undo hist =
            let (size, pres.past,future) = rep_history hist in
                if (null past) then
                    failwith `undo: nothing to undo`
                else
                    abs_history(size, past, pres.future)
    %   Undoes an undo, but only if no interveening event has occured.  %
    and redo hist =
            let (size,past,future) = rep_history hist in
                if (null future) then
                    failwith `redo: nothing to redo`
                else
                    abs_history
                        (size, first size ((hd future).past), tl future)
    and set_max_hist size hist =
            let (_,past,future) = rep_history hist in
                if size < 1 then
                    failwith `set_max_hist: size must be at least 1.`
                else
                    abs_history(size,past,future)
    and get_max_hist hist =
            let (size,_,_) = rep_history hist in
                size
    ;;

abstype window_stack =
    (window # (((window -> window -> window) # win_path) + void)) list
    %   Create a new window stack containing window w.                  %
    with create_stack w =
            abs_window_stack [(w,  (inr ()))]
    %   Apply some transformation to the top window of the stack.       %
    and change_window f st =
            let ((w,cp).tl) = (rep_window_stack st) in
                abs_window_stack ((f w,cp).tl)
    %   Open a new window, requires a path and a basis function.        %
    and open_window p' basis st =
            let ((w,cp).tl) = (rep_window_stack st) in
            let (w',c') = (basis p' w) in
                abs_window_stack ((w',inl (c',p')).(w,cp).tl)
    %   Removes the top window from the stack.                          %
    and pop_window st =
            (let (w1.w2.w3) = (rep_window_stack st) in
                abs_window_stack (w2.w3)
            ) ? failwith `pop_window: only 1 window left`
    %   Removes the top window and transforms the one below.            %
    and close_window st =
            let ((w1,cp1).(w2,cp2).tl) = (rep_window_stack st) in
            let (c1,_) = outl cp1 in
                abs_window_stack ((c1 w1 w2,cp2).tl)
    %   The current depth of the stack.                                 %
    and depth_stack st =
            length (rep_window_stack st)
    %   The window on top of the stack.                                 %
    and top_window st =
            fst (hd (rep_window_stack st))
    %   The path that the current window was opened on.                 %
    %   Fails for the first window in the stack - it had no path.       %
    and top_path st =
            (snd (outl (snd (hd (rep_window_stack st)))))
            ? failwith `top_path: bottom window` ;;

% Next come a bunch of functions required printing a stack.             %
% Actually only prints the window on top of the stack.                  %

% The conjectures which are used in the top window and are not valid    %
%   in the window below.                                                %
let bad_conjectures st =
    let topwin = top_window st in
    let bnds = bound topwin in
    let usedcnjs = used_conjectures topwin in
        if (depth_stack st) > 1 then
        (
            let winbelow =
                transfer_sups_thms topwin (top_window (pop_window st)) in
            let hypsbelow = all_hypotheses winbelow in
            let lemsbelow = lemmas winbelow in
            let cnjsbelow = conjectures winbelow in
                (filter
                    (\c. not
                        (term_mem c (hypsbelow @ lemsbelow @ cnjsbelow)))
                    usedcnjs)
                @
                (filter
                    (\c. not (null (intersect bnds (frees c))))
                    usedcnjs)
        )
        else
            usedcnjs;;

% Give a friendly picture of the stack.                                 %
% Only the top window is displayed.                                     %
% Each of the hypotheses appears with a "!" infront of it.              %
% Each of the lemmas appears with a "|" infront of it.                  %
% Each of the conjectures appears with a "?" infront of it.             %
% Each of the used conjectures appears with a "$" infront of it.        %
% Each of the bad conjectures appears with a "@" infront of it.         %
% The relation and focus are then printed last.                         %
let print_stack st =
    let rel_pic (tm:term) =
        if (is_const tm) then
            fst (dest_const tm)
        else `??` in
    let topwin = top_window st in
    let hyps = disp_hypotheses topwin in
    let cnjs = conjectures topwin in
    let usedcnjs = used_conjectures topwin in
    let lems = lemmas topwin in
    let badcnjs = bad_conjectures st in
    let rel = rel_pic (relation topwin) in
    let rellen = length (explode rel) in
    letref all = term_setify ((rev hyps) @ (rev lems) @ (rev cnjs)) in
        while not (null all) do
        (
            let h.t = all in
                print_string (implode (replicate ` ` rellen));
                (if (term_mem h badcnjs) then
                    print_string ` @ `
                else if (term_mem h usedcnjs) then
                    print_string ` $ `
                else if (term_mem h hyps) then
                    print_string ` ! `
                else if (term_mem h lems) then
                    print_string ` | `
                else % An unused conjecture. %
                    print_string ` ? `);
                print_ibegin (rellen + 4);
                    print_unquoted_term h;
                print_end ();
                print_newline ();
                all := t
        );
        print_string rel;
        print_string ` * `;
        print_ibegin (rellen + 4);
            print_unquoted_term (focus topwin);
        print_end ();
        print_newline ();;

% We now set up functions to handle a tabel of                              %
%   window_stack history pointers.                                          %
% Each element in the table is a pair of the name of a                      %
%   window_stack (history) and a pointer to it.                             %
% There is also a pair cur_nam_st_hist with the name of the current         %
%   stack and a pointer to it.                                              %
% cur_nam_st_hist can also be void in the event of their being no           %
%   current stack.                                                          %

% We also set up some signals which are made when the current stack         %
%   changes.   These are used to alert centaur so it can update its         %
%   displayes.   They can also be used to set the window stripe on an       %
%   xterm to the name of the current stack.   They are also used to print   %
%   a fresh view of the stack when necessary.                               %

sigtype `stk_sig` `string`;;
sigtype `win_sig` `void`;;

let beg_stack_sig = newsig_stk_sig ();;
let end_stack_sig = newsig_stk_sig ();;
let set_stack_sig = newsig_stk_sig ();;

let psh_win_sig = newsig_win_sig ();;
let pop_win_sig = newsig_win_sig ();;
let cng_win_sig = newsig_win_sig ();;

begin_section tablesec;;

    ptrtype `wshp` `window_stack history`;;

    letref stack_table = [] : (string # window_stack history pointer) list;;
    letref cur_nam_st_hist =
        (inr ()) : ((string # window_stack history pointer) + void);;

    let CURRENT_STACK (():void) =
        (present (value (snd (outl cur_nam_st_hist))))
        ? failwith `CURRENT_STACK: no current stack`;;

    let CURRENT_NAME (():void) =
        (fst (outl cur_nam_st_hist))
        ? failwith `CURRENT_NAME: no current name`;;

    let CURRENT_SHP (():void) =
        (snd (outl cur_nam_st_hist)) ? failwith `no current stack`;;

    % There are versions of all the history functions which side-effect the %
    %   current window_stack history.                                       %

    letref history_size = 20;;

    let EPOCH s =
        let the_stack = (CURRENT_SHP ()) in
            store the_stack (epoch history_size s);;

    let DO f = 
        let the_stack = (CURRENT_SHP ()) in
            store the_stack (dodo f (value the_stack));;

    let UNDO (():void) =
        let the_stack = (CURRENT_SHP ()) in
        let old_depth = depth_stack (present (value the_stack)) in
        let new_depth = depth_stack (present (undo (value the_stack))) in
            store the_stack (undo (value the_stack));
            if old_depth = new_depth then
                signal cng_win_sig ()
            else if old_depth < new_depth then
                signal psh_win_sig ()
            else % old_depth > new_depth %
                signal pop_win_sig ();;

    let REDO (():void) =
        let the_stack = (CURRENT_SHP ()) in
        let old_depth = depth_stack (present (value the_stack)) in
        let new_depth = depth_stack (present (redo (value the_stack))) in
            store the_stack (redo (value the_stack));
            if old_depth = new_depth then
                signal cng_win_sig ()
            else if old_depth < new_depth then
                signal psh_win_sig ()
            else % old_depth > new_depth %
                signal pop_win_sig ();;

    % Set the size of the history on all stacks.                            %
    let SET_MAX_HIST size =
        history_size := size;
        map (\(_,shp). store shp (set_max_hist size (value shp))) stack_table;;

    % Get the size of the history.                                          %
    let GET_MAX_HIST (():void) = history_size;;

    % Start a new stack.                                                    %
    % The new stack becomes the current stack.                              %
    let BEGIN_STACK name relfoc hyps thms =
        if mem name (map fst stack_table) then
            failwith `BEGIN_STACK: stack exists`
        else
            (
                cur_nam_st_hist := (inl (name, new_wshp ()));
                EPOCH
                    (create_stack (create_win relfoc (rev hyps) (rev thms)));
                stack_table := (outl cur_nam_st_hist).stack_table;
                signal beg_stack_sig name
            );;

    % Dispose of a named stack.                                             %
    % If the named stack is the current stack, then the current stack       %
    %   is left undefined.                                                  %
    let END_STACK name = 
        if mem name (map fst stack_table) then
            (
                (
                    if ((name = (CURRENT_NAME ())) ? false) then
                        do (cur_nam_st_hist := (inr ()))
                );
                stack_table := filter ((\(n,_). not (n = name))) stack_table;
                signal end_stack_sig name
            )
        else
            failwith `END_STACK: no such stack`;;

    % Set the current stack the the stack named.                            %
    let SET_STACK name =
        (
            do
            (
                cur_nam_st_hist := inl (assoc name stack_table);
                signal set_stack_sig name
            )
        ) ? failwith `SET_STACK: no such stack`;;

    % Return the named stack.                                               %
    let GET_STACK name =
        (present (value (snd (assoc name stack_table))))
        ? failwith `GET_STACK: no such stack`;;

    % The names of all the stacks.                                          %
    let ALL_STACKS (():void) = (map fst stack_table);;

    (
        CURRENT_STACK,
        CURRENT_NAME,
        DO,
        UNDO,
        REDO,
        SET_MAX_HIST,
        GET_MAX_HIST,
        BEGIN_STACK,
        END_STACK,
        SET_STACK,
        GET_STACK,
        ALL_STACKS
    );;

end_section tablesec;;

let (
        CURRENT_STACK,
        CURRENT_NAME,
        DO,
        UNDO,
        REDO,
        SET_MAX_HIST,
        GET_MAX_HIST,
        BEGIN_STACK,
        END_STACK,
        SET_STACK,
        GET_STACK,
        ALL_STACKS
    ) = it ;;

% Apply a opening basis to the stack to create a new window.            %
let APPLY_OPEN p basis =
    DO (open_window p basis);
    signal psh_win_sig ();;

% Apply a window transforming function to the top of the stack.         %
let APPLY_TRANSFORM f = 
    DO (change_window f);
    signal cng_win_sig ();;

% Since life is no longer functional, you have to close windows after   %
% you have finished with them.                                          %
let CLOSE_WIN (():void) =
    (DO close_window) ? failwith `CLOSE_WIN`;
    signal pop_win_sig ();;

% Pops the top window of the current stack.                             %
let UNDO_WIN (():void) =
    DO pop_window;
    signal pop_win_sig ();;
    
% Stack based versions of the window opening commands.                  %
let GEN_OPEN_WIN p = APPLY_OPEN p gen_open_basis
and OPEN_WIN p = APPLY_OPEN (FOCUS_PATH p) open_win_basis
and OPEN_CONTEXT tm p = APPLY_OPEN (CONTEXT_PATH (tm,p)) open_context_basis
and ESTABLISH tm = APPLY_OPEN (CONTEXT_PATH (tm,[])) establish_basis;;

% Analogues of all the functional commands.                             %

let TOP_WIN (():void) = top_window (CURRENT_STACK ())
and BAD_CONJECTURES (():void) = bad_conjectures (CURRENT_STACK ());;

let TRANSFORM_WIN tr = APPLY_TRANSFORM (transform_win tr)
and MATCH_TRANSFORM_WIN tr = APPLY_TRANSFORM (match_transform_win tr)
and CONVERT_WIN c = APPLY_TRANSFORM (convert_win c)
and RULE_WIN inf = APPLY_TRANSFORM (rule_win inf)
and THM_RULE_WIN inf = APPLY_TRANSFORM (thm_rule_win inf)
and FOC_RULE_WIN inf = APPLY_TRANSFORM (foc_rule_win inf)
and TACTIC_WIN tac = APPLY_TRANSFORM (tactic_win tac)
and ADD_THEOREM th = APPLY_TRANSFORM (add_theorem th)
and ADD_SUPPOSE sup = APPLY_TRANSFORM (add_suppose sup)
and CONJECTURE tm = APPLY_TRANSFORM (conjecture tm);;

let FOCUS (():void) = focus (TOP_WIN ())
and LEMMA_THMS (():void) = lemma_thms (TOP_WIN ())
and WIN_THM (():void) = win_thm (TOP_WIN ());;

% Rewriting functions.							%
let GEN_REWRITE_WIN rewrite_fun built_in_rewrites =
    APPLY_TRANSFORM o (gen_rewrite_win rewrite_fun built_in_rewrites)
and PURE_REWRITE_WIN = APPLY_TRANSFORM o pure_rewrite_win
and REWRITE_WIN = APPLY_TRANSFORM o rewrite_win
and PURE_ONCE_REWRITE_WIN = APPLY_TRANSFORM o pure_once_rewrite_win
and ONCE_REWRITE_WIN = APPLY_TRANSFORM o once_rewrite_win
and PURE_ASM_REWRITE_WIN = APPLY_TRANSFORM o pure_asm_rewrite_win
and ASM_REWRITE_WIN = APPLY_TRANSFORM o asm_rewrite_win
and PURE_ONCE_ASM_REWRITE_WIN =
    APPLY_TRANSFORM o pure_once_asm_rewrite_win
and ONCE_ASM_REWRITE_WIN = APPLY_TRANSFORM o once_asm_rewrite_win
and FILTER_PURE_ASM_REWRITE_WIN f =
    APPLY_TRANSFORM o (filter_pure_asm_rewrite_win f)
and FILTER_ASM_REWRITE_WIN f =
    APPLY_TRANSFORM o (filter_asm_rewrite_win f)
and FILTER_PURE_ONCE_ASM_REWRITE_WIN f =
    APPLY_TRANSFORM o (filter_pure_once_asm_rewrite_win f)
and FILTER_ONCE_ASM_REWRITE_WIN f =
    APPLY_TRANSFORM o (filter_once_asm_rewrite_win f);;

% Save the theorem on the top of the window stack.                      %
let SAVE_WIN_THM (():void) =
    (save_thm (CURRENT_NAME (), WIN_THM ())) ? failwith `SAVE_WIN_THM`;;

% Print out the window stack.                                           %
let PRINT_STACK (():void) = print_stack (CURRENT_STACK ());;

% Set up the signals so that they print out a fresh view of the stack   %
% anytime something happens.                                            %
handle beg_stack_sig (\_. PRINT_STACK ());;
handle set_stack_sig (\_. PRINT_STACK ());;
handle psh_win_sig PRINT_STACK;;
handle cng_win_sig PRINT_STACK;;
handle pop_win_sig PRINT_STACK;;
