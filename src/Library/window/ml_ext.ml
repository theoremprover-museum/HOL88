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
% CONTENTS: miscelaneous ml ultility functions                               %
%============================================================================%
%$Id: ml_ext.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

% Set up "le" and "ge" to be the infix less-than-or-equal-to and            %
% greater-than-or-equal-to functions on integers respectively.              %
    ml_curried_infix `le`;;
    let x le y = (x < y) or (x = y);;

    ml_curried_infix `ge`;;
    let x ge y = (x > y) or (x = y);;

% (prefix l1 l2) = (?m. (l1 @ m) = l2)                                      %
    letrec prefix (l1 : * list) (l2 : * list) = 
        if null l1  then
            true
        else if null l2 then
            false
        else if (hd l1) = (hd l2) then
            prefix (tl l1) (tl l2)
        else
            false;;

% (suffix l1 l2) = (?m. (m @ l1) = l2)                                      %
let suffix (l1 : * list) (l2 : * list) = prefix (rev l1) (rev l2);;

% (after l1 l2) = (@l. (l1 @ l) = l2)                                       %
letrec after (l1 : * list) (l2 : * list) =
    if null l1 then
        l2
    else if (hd l1) = (hd l2) then
        after (tl l1) (tl l2)
    else
        failwith `after`;;

% (before l1 l2) = (@l (l @ l1) = l2)                                       %
let before (l1 : * list) (l2 : * list) = rev (after (rev l1) (rev l2));;

% (index p l) = (@i. p(el i l))                                             %
letrec index pred = fun (h.t) . if (pred h) then 1 else 1 + index pred t
                     |  []    . failwith `index`;;

% (merge sortfn (sort sortfn l1) (sort sortfn l2)) = (sort sortfn (l1 @ l2)) %
letrec merge sortfn l1 l2 =
    if null l1 then
        l2
    else if null l2 then
        l1
    else
        let (h1.t1) = l1
        and (h2.t2) = l2 in
            if sortfn (h1, h2) then
               h1.(merge sortfn t1 l2)
            else
               h2.(merge sortfn l1 t2);;

% best sortfn l = @e. mem e l /\ !e'. mem e l /\ ~(e' = e) ==> sortfun e e'    %
let best =
    let better sortfun x y =
        if sortfun (x,y) then 
            x
        else
            y
    in
        \sortfun. end_itlist (better sortfun) ;;

% first n l = the first n elements of the list l.                           %
% If there are less than n elements in l then l is returned.                %
let first = 
    letrec frst n l =
        if (n = 0) or (null l) then
            []
        else
            (hd l).(frst (n - 1) (tl l))
    in
        \n. if n < 0 then
                failwith `first: length must be nonnegative`
            else
                frst n;;

% last n l = the last n elements of the list l.                             %
% If there are less than n elements in l then l is returned.                %
let last n l =
    (rev (first n (rev l))) ? failwith `last: length must be nonnegative`;;

% Set up generic handeling of pointers.                                     %
% If you want pointers to things of type t, first make this call.           %
%   ptrtype `name` `t`;;                                                    %
% name is some string that will probably want to stand for `t pointer`.     %
% name must be a valid ML identifier.                                       %
% The call to ptrtype must be made at top level, and yes the name of the    %
% type is given as a string.                                                %
%                                                                           %
% The function new_name can then be used to create new pointers to          %
% objects of type t.                                                        %
% The result of   new_name ()    is of type   t pointer  .                  %
% The following functions work for pointers.                                %
% value p   returns the value pointed at by p.                              %
% value p   will fail if nothing has been stored at p.                      %
% store p v stores the value v at p.                                        %
% dispose p throws away what ever is stored at p.                           %
% is_nill p is true if nothing is stored at p.                              %

type * pointer = POINTER of ((void -> *) # (* -> void) # (void -> void));;

let value (POINTER (val,_,_)) = (val ()) ? failwith `value: dereference of NIL`
and store (POINTER (_,sto,_)) = sto
and dispose (POINTER (_,_,dsp)) = dsp ()
and is_nil (POINTER (val,_,_)) = not (can val ());;

% ptrtype `name` `type` declares a function                                 %
% new_name: void -> type pointer                                            %
% This should then be used to create pointers of the required type.         %
let ptrtype name ty =
    if compiling then
        ML_eval
        (
            `
                top_print 
                (\\(p:(`^ty^`) pointer). print_string \`(-)\`);;

                let new_`^name^` (():void) =
                    letref val = (inr ()) : ((`^ty^`) + void) in
                        POINTER
                        (
                            (\\(():void). (outl val))
                        ,
                            (\\v. do (val := (inl v)))
                        ,
                            (\\(():void). do (val := (inr ())))
                        );;
            `
        );;

% Set up generic handeling of pointers.                                     %
% If you want signals to hanle exceptions of type t, make this call:        %
%   sigtype `name` `t`;;                                                    %
% name is some string that will probably want to stand for `t signal`.      %
% name must be a valid ML identifier.                                       %
% The call to sigtype must be made at top level, and yes the name of the    %
% type is given as a string.                                                %
%                                                                           %
% The function newsig_name can then be used to handle exeptions of type t.  %
% The following functions work for signals.                                 %
% signal sig p  signals sig with parameter p.                               %
% clear sig     clears all the handlers from signal sig.                    %
% handle sig f  adds a signal handler to the signal sig.                    %
type * signal =
    SIGNAL of ((* -> void) # (void -> void) # ((* -> void) -> void));;

let signal (SIGNAL (sig,_,_)) = sig
and clear (SIGNAL (_,clr,_)) = clr ()
and handle (SIGNAL (_,_,hand)) = hand;;

let sigtype name ty =
    if compiling then
        ML_eval
        (
            `
                top_print
                (\\(s:(`^ty^`) signal). print_string \`(-)\`);;

                let newsig_`^name^` (():void) =
                    letref handlers = [] : (`^ty^` -> void) list in
                        SIGNAL
                        (
                            (\\p. do (map (\\f. f p) handlers))
                        ,
                            (\\(():void). do (handlers := []))
                        ,
                            (\\f. do (handlers := f.handlers))
                        );;
            `
        );;
