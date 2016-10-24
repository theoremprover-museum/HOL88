% FILE		: inst_int_mod.ml					%
% DESCRIPTION   : defines functions for instatiating single theorems    %
%                 and the whole theory of the integers mod n with a	%
%                 particular value for n.				%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.9.11						%
%									%
%-----------------------------------------------------------------------%

loadf `start_groups`;;

% return_INT_MOD_thm : string -> term -> thm				%
%									%
% return_INT_MOD_thm returns the intstantiated version of a theorem	%
% from elt_gp.th.							%
%									%
% The string is the name of the int_mod.th theorem to be instantiated;	%
% the term is the integer value with which n is to be instantiated.	%

let return_INT_MOD_thm name value =
  STRONG_INST [(value,"n:integer")] (theorem `int_mod` name);;


% include_INT_MOD_thm : string -> string -> term -> thm			%
%									%
% include_INT_MOD_thm intstantiates the named theorem from int_mod.th,	%
% stores the result in the current theory, and returns it.		%
%									%
% The first string is the name of the int_mod.th theorem to be		%
% instantiated; the second string is the name under which the resultant %
% theorem will be store in the current theory; the term is the integer	%
% value with which n is to be instantiated.				%

let include_INT_MOD_thm old_name name value =
 save_thm (name,(return_INT_MOD_thm old_name value));;


% return_INT_MOD_theory : string -> term -> (string # thm)list		%
%									%
% return_INT_MOD_theory returns the list of all pairs of names of       %
% theorems, prefixed by the given string, together with the		%
% instantiated version of the corresponding theorem from int_mod.th	%
%									%
% The string is the prefix to be added to all names of the theorems     %
% from int_mod.th; the term is the integer value with which n is to	%
% be instantiated.							%


let return_INT_MOD_theory name_prefix value =
 map(\ (thm_name, thm).
      (name_prefix^`_`^thm_name,
       (STRONG_INST [(value,"n:integer")] thm)))
  (rev (theorems `int_mod`));;

% include_INT_MOD_theory : string -> term -> (string # thm)list		%
%									%
% include_INT_MOD_theory  instantiates all the theorems from int_mod.th %
% with the given value, stores the resulting theorems in the current	%
% theory under their old name prefixed by the given string, and returns %
% them bound to the names under which they were stored.			%
%									%
% The string is the prefix to be added to all names of the theorems     %
% from int_mod.th; the term is the integer value with which n is to	%
% be instantiated.							%



let include_INT_MOD_theory name_prefix value =
 (map save_thm 
    (return_INT_MOD_theory name_prefix value);
 (include_theorems (current_theory ())));;
