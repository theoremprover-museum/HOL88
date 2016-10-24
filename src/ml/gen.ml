%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        gen.ml                                                %
%                                                                             %
%     DESCRIPTION:      General purpose functions for ML                      %
%                                                                             %
%     USES FILES:       hol-lcf lisp files, ml-curry.ml, lis.ml               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%


% --------------------------------------------------------------------- %
% Use the character "sep" to split the token into non-empty words       %
%                                                                       %
% words2 `/` `abc//d/ef/`  -->  [`abc`; `d`; `ef`]                      %
% --------------------------------------------------------------------- %

let words2 sep string =
    snd (itlist (\ch (chs,tokl).
             if ch = sep then
                if null chs then [],tokl
                else [], (implode chs . tokl)
             else (ch.chs), tokl)
    (sep . explode string)
    ([],[]));;


% --------------------------------------------------------------------- %
% words `are you there`  -->  [`are`; `you`; `there`]                   %
% --------------------------------------------------------------------- %
let words = words2 ` `;;

% --------------------------------------------------------------------- %
% maptok f `are you there` = [f `are`; f `you`; f `there`]              %
% --------------------------------------------------------------------- %
let maptok f tok = map f (words tok);;

% --------------------------------------------------------------------- %
% Loading abbreviations.                                                %
%                                                                       %
% loadx added by MJCG for HOL88.1.05 on April 6 1989                    %
% --------------------------------------------------------------------- %

let loadt tok = load (tok,true) and loadf tok = load (tok,false);;
let compilet tok = compile (tok,true) and compilef tok = compile (tok,false);;

% Deleted TFM 90.12.01                                                  %
% let loadx tok = load(tok, get_flag_value `print_lib`);;               %

% --------------------------------------------------------------------- %
% Token concatenation                                                   %
% --------------------------------------------------------------------- %

let concat tok1 tok2 = implode(explode tok1 @ explode tok2) ;;
let concatl tokl = implode (itlist append (map explode tokl) []);;

ml_curried_infix `^`;;
let $^ = concat;;

let message tok = print_string tok; print_newline();;

% --------------------------------------------------------------------- %
% combinators, as in Curry & Feys                                       %
% CB added: TFM 91.09.13                                                %
% --------------------------------------------------------------------- %

ml_paired_infix `o`;;
ml_paired_infix `#`;;
ml_paired_infix `oo`;;
ml_curried_infix `CB`;;

let $o(f,g)x = f(g x) ;;
let $CB f g x = g(f x) ;;
let $# (f,g) (x,y) = (f x, g y);;

% --------------------------------------------------------------------- %
% Composition for a function that takes a paired argument               %
% --------------------------------------------------------------------- %
let $oo (f,(g,h)) x = f(g x, h x);;

let I x = x;;
let K x y = x;;
let KI = K I;;  % Dual of K; K and KI are analogs of fst and snd%
let C f x y = f y x         %  the permutator  %
and W f x   = f x x         %  the duplicator  %
and B f g x = f (g x)       %  the compositor, curried form of "o" %
and S f g x = f x (g x);;

% --------------------------------------------------------------------- %
% S, K, I permit the definition of lambda-abstraction                   %
% \x.x = I      actually unnecessary, since I = S K K)                  %
% \x.A = K A    where A is a constant or a variable other than x        %
% \x.(A B) = S (\x.A) (\x.B)                                            %
% --------------------------------------------------------------------- %

ml_paired_infix `Co`;;
let $Co (f,g) x y = f (g y) x;;    % permutation-composition                %
                                   % Ainsi nomme car  $Co (f,g) = C (f o g) %
let pair x y = (x,y);;
let curry f x y = f(x,y);;

% --------------------------------------------------------------------- %
% sequencing operators for functions            [Deleted: TFM 90.09.19] %
%                                                                       %
% ml_curried_infix `thenf` ;;                                           %
% ml_curried_infix `orelsef` ;;                                         %
%                                                                       %
% let thenf f g x = g(f x);;                                            %
% let orelsef f g x = f x ? g x;;                                       %
% let all_fun x = x;;                                                   %
% let no_fun x = failwith `no_fun`;;                                    %
% let first_fun fl x =                                                  %
%     itlist $orelsef fl no_fun x ? failwith `first_fun`;;              %
% let every_fun fl x =                                                  %
%     itlist $thenf fl all_fun x ? failwith `first_fun`;;               %
% letrec repeatf f x = (f thenf (repeatf f) elsef I) x;;                %
% letrec repeatf f x = (f thenf (repeatf f)) x ? x;;                    %
%                                                                       %
% --------------------------------------------------------------------- %


let can f x = (f x ; true) ? false ;;

% --------------------------------------------------------------------- %
% Check that the value x satisfies the predicate p; if so, pass x on.   %
% --------------------------------------------------------------------- %
let assert p x =  if p x then x else fail ;;

let syserror tok =
    print_string `ML system error `;
    print_string tok;
    print_newline();
    failwith `syserror`;;


% --------------------------------------------------------------------- %
% Provides a simple backtrace, since it prefixes a token to the previous%
% failure token.  Warning:  this                                        %
%  (1)  slows down failure propagation.                                 %
%  (2)  works only with the innermost lambda of a curried function.     %
% --------------------------------------------------------------------- %
let set_fail_prefix tok ff arg =
    ff arg ?\tail failwith (concatl [tok; ` -- `; tail]);;

% --------------------------------------------------------------------- %
% Set a function's failure token                                        %
% --------------------------------------------------------------------- %
let set_fail tok ff arg = ff arg ? failwith tok;;

% --------------------------------------------------------------------- %
% f^n (x) = f(f....(f x))                                               %
% Changed to treat -ve arguments as zero, i.e. return x [JRH 94.01.29]  %
% --------------------------------------------------------------------- %

letrec funpow n f x =
    if n < 1 then x
    else funpow (n-1) f (f x);;

% --------------------------------------------------------------------- %
% "<<" Added by MJCG for HOL88.1.01                                     %
% --------------------------------------------------------------------- %
ml_paired_infix `<<`;;


% ===================================================================== %
% The following were added by MJCG for HOL88.1.02.  Revised by TFM for  %
% version 1.12 on 1 December 1990.                                      %
% ===================================================================== %

% --------------------------------------------------------------------- %
% HOLdir no longer used                                  [TFM 90.12.01] %
%                                                                       %
% letref HOLdir = `<holdir>`;;                                          %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Functions for loading files from a library                            %
%                                                                       %
% DELETED: access the library through the search path.  [TFM 90.12.01]  %
%                                                                       %
% let load_from_lib t lib file =                                        %
%  load((HOLdir ^ `/Library/` ^ lib ^ `/` ^ file),t);;                  %
%                                                                       %
% let loadt_from_lib = load_from_lib true                               %
% and loadf_from_lib = load_from_lib false;;                            %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Function for resetting various paths relative to a new HOL root       %
% directory.                                    [REVISED: TFM 90.12.01] %
% --------------------------------------------------------------------- %

let install =
    let helps = [`/help/ENTRIES/`] in
    \st. print_string (`HOL installed (\`` ^ st ^ `\`)`);
         print_newline();
         lisp (`(setq %hol-dir (quote |` ^ st ^ `|))`);
         lisp (`(setq %lib-dir (quote |` ^ st ^ `/Library|))`);
         set_search_path [``; `~/`; st ^ `/theories/`];
         set_library_search_path [st ^ `/Library/`];
         set_help_search_path (map (concat st) helps);
         ();;

% --------------------------------------------------------------------- %
% Functions for adding to the search path       [DELETED TFM 90.12.01]  %
%                                                                       %
% let add_to_search_path p = set_search_path(p.search_path());;         %
% let append_to_search_path p = set_search_path(search_path()@[p]);;    %
% --------------------------------------------------------------------- %

