%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_arith.ml                                           %
%                                                                             %
%     DESCRIPTION:      Creates the theory "arithmetic.th" containing the     %
%                       definitions of the usual arithmetic operators + * etc %
%                                                                             %
%     AUTHOR:           T. F. Melham (88.04.02)                               %
%                                                                             %
%     PARENTS:          prim_rec.th fun.th                                    %
%     WRITES FILES:     arithmetic.th                                         %
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
%     REVISION HISTORY: adding fun.th as parent by WW (2 Jan 94)              %
%=============================================================================%

new_theory `arithmetic`;;

map new_parent [`prim_rec`; `fun`];;

% --------------------------------------------------------------------- %
% Load the code for primitive recursive definitions on arbitrary types. %
%                                                                       %
% Note that prim_rec_ml.o must be recompiled if basic-hol has been      %
% rebuilt. The uncompiled version is therefore loaded here.             %
%                                                                       %
% TFM 88.04.02                                                          %
% --------------------------------------------------------------------- %

loadt (concat ml_dir_pathname `prim_rec.ml`);;

% fetch the prim rec definition axiom from prim_rec.th                  %
let num_Axiom = theorem `prim_rec` `num_Axiom`;;

let ADD = new_recursive_definition true num_Axiom `ADD`
         "($+ 0 n = n) /\
          ($+ (SUC m) n = SUC($+ m n))";;

let SUB = new_recursive_definition true num_Axiom `SUB`
          "($- 0 m = 0) /\
           ($- (SUC m) n = ((m < n) => 0 | SUC($- m n)))";;

let MULT = new_recursive_definition true num_Axiom `MULT`
          "($* 0 n = 0) /\
           ($* (SUC m) n = ($* m n) + n)";;

let EXP = new_recursive_definition true num_Axiom `EXP`
   "(EXP m 0       = 1) /\
    (EXP m (SUC n) = m * (EXP m n))";;

% --------------------------------------------------------------------- %
% Deleted TFM 88.04.02                                                  %
% let SLASH = new_infix_definition(`/`,  "$/ m n = @x. n*x = m");;      %
% --------------------------------------------------------------------- %

let GREATER =
    new_infix_definition(`GREATER`,  "$> m n = (n < m)");;

let LESS_OR_EQ =
    new_infix_definition(`LESS_OR_EQ`, "$<= m n = (m < n) \/ (m = n)");;

let GREATER_OR_EQ =
    new_infix_definition(`GREATER_OR_EQ`, "$>= m n = (m > n) \/ (m = n)");;

%----------------------------------------------------------------------------%
% Definitions of factorial, even and odd                [JRH 92.07.14]       %
%----------------------------------------------------------------------------%

let FACT = new_recursive_definition false num_Axiom `FACT`
  "(FACT 0 = 1) /\
   (FACT (SUC n) = (SUC n) * FACT(n))";;

let EVEN = new_recursive_definition false num_Axiom `EVEN`
  "(EVEN 0 = T) /\
   (EVEN (SUC n) = ~(EVEN n))";;

let ODD = new_recursive_definition false num_Axiom `ODD`
  "(ODD 0 = F) /\
   (ODD (SUC n) = ~(ODD n))";;

% ---------------------------------------------------------------------    %
% These definitions of MOD and DIV are replaced by constant specifications %
% in the file mk_arith_thms.ml                                             %
%                                                                          %
% let MOD =                                                                %
%    new_infix_definition                                                  %
%    (`MOD`, "MOD k n = @r. ?q. (k = (q * n) + r) /\ r < n");;             %
%                                                                          %
% let DIV =                                                                %
%    new_infix_definition                                                  %
%    (`DIV`, "DIV k n = @q. (k = (q * n) + (k MOD n))");;                  %
%                                                                          %
%                                                           [TFM 90.05.26] %
% ---------------------------------------------------------------------    %

close_theory();;

quit();;
