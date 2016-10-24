% precedence.ml                                                               %
%-----------------------------------------------------------------------------%

%  Precedence tables for HOL  %

%  Values have been chosen to allow user-defined objects to have a  %
%  precedence between the precedences of any built-in objects.      %

let is_res_quan =
   (\con. mem con [`RES_FORALL`; `RES_EXISTS`; `RES_SELECT`; `RES_ABSTRACT`]);;

%  Precedence table for HOL types  %

let type_prec symb =

   % : (string -> int) %

   case symb
   of `fun`  . 300
    | `prod` . 100
    | `sum`  . 200
    | _      . 0;;


%  Highest type precedence (minimum value)  %

let min_type_prec = 0;;


%  Lowest type precedence (maximum value)  %

let max_type_prec = 400;;


%  Precedence table for HOL terms  %

let term_prec symb =

   % : (string -> int) %

   case symb
   of `\\`   . 1700                    %  Abstractions  %
    | `o`    . 1600
    | `Sum`  . 1600
    | `IS_ASSUMPTION_OF` . 1600
    | `=`    . 1500
    | `<=>`  . 1400
    | `==>`  . 1300
    | `\\/`  . 1200
    | `/\\`  . 1100
    | `<`    . 1000
    | `>`    . 1000
    | `<=`   . 1000
    | `>=`   . 1000
    | `+`    . 900
    | `-`    . 900
    | `*`    . 800
    | `DIV`  . 800
    | `MOD`  . 800
    | `EXP`  . 700
    | `LET`  . 600
    | `COND` . 500
    | `,`    . 400                     %  Tuples  %
    | `~`    . 300
    | `:`    . 100                     %  Type information  %
    | x . (if (is_binder x) then 1700
    	   else if (is_res_quan x) then 1700
           else if (is_infix x) then 200
           else 0);;


%  Highest term precedence (minimum value)  %

let min_term_prec = 0;;


%  Lowest term precedence (maximum value)  %

let max_term_prec = 1800;;


%-----------------------------------------------------------------------------%
