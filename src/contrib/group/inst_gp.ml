% FILE		: inst_gp.ml						%
% DESCRIPTION   : defines functions for instatiating and simplifying    %
%                 single theorems and the whole theory of the integers  %
%                 with a particular theory.				%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
%-----------------------------------------------------------------------%

loadf `start_groups`;;


% return_GROUP_thm : string -> thm -> thm list -> thm			%
%									%
% return_GROUP_thm returns the intstantiated and simplfied version of a %
% theorem from elt_gp.th.						%
%									%
% The string is the name of the elt_gp.th theorem to be	instantiated;	%
% the theorem must state that the desired example does form a group;    %
% the list of theorems are for use in simplifying the instantiated      %
% theorem.								%

let return_GROUP_thm old_name set_as_gp_thm rewrite_list =
 if fst(dest_const(rator(concl set_as_gp_thm))) = `GROUP`
 then
  let (set,bin_op) = dest_pair(rand (concl set_as_gp_thm)) in
  let set_type = hd (snd (dest_type (type_of set))) in
  let thm = theorem `elt_gp` old_name in
   NORMALIZE rewrite_list (MP
   (INST [(set,"G:^set_type -> bool");
          (bin_op,"prod:^set_type -> ^set_type -> ^set_type")]
   (INST_TYPE [(set_type,":*")] thm)) set_as_gp_thm)
 else failwith
  `return_GROUP_thm failed; Theorem not of form |- GROUP(G,prod).`;;


% include_GROUP_thm : string -> string -> thm -> thm list -> thm	%
%									%
% include_GROUP_thm instantiates a named theorem from elt_gp.th,	% 
% simplifies it, stores the result in the current theory, and returns 	%
% it.									%
%									%
% The first string is the name of the elt_gp.th theorem to be		%
% instantiated; the second string is the name under which the resultant %
% theorem will be store in the current theory; the theorem must state   %
% that the desired example does form a group; the list of theorems are  %
% for use in simplifying the instantiated theorem, prior to storing.    %

let include_GROUP_thm old_name name set_as_gp_thm rewrite_list =
 save_thm (name,(return_GROUP_thm old_name set_as_gp_thm rewrite_list));;


% return_GROUP_theory : string -> thm -> thm list -> (string # thm)list	%
%									%
% return_GROUP_theory returns the list of all pairs of names of         %
% theorems, prefixed by the given string, together with the		%
% instantiated and simplfied version of the corresponding theorem from  %
% from elt_gp.th.							%
%									%
% The string is the prefix to be added to all names of the theorems     %
% from  elt_gp.th; the theorem must state that the desired example does %
% form a group; the list of theorems are for use in simplifying the     %
% instantiated theorems.						%


let return_GROUP_theory name_prefix set_as_gp_thm rewrite_list =
 if fst(dest_const(rator(concl set_as_gp_thm))) = `GROUP`
 then
  let (set,bin_op) = dest_pair(rand (concl set_as_gp_thm)) in
  let set_type = hd (snd (dest_type (type_of set))) in
  map(\ (thm_name, thm).
       (name_prefix^`_`^thm_name,
           (NORMALIZE rewrite_list (MP
             (INST [(set,"G:^set_type -> bool");
               (bin_op,"prod:^set_type -> ^set_type -> ^set_type")]
               (INST_TYPE [(set_type,":*")] thm))
             set_as_gp_thm))))
   (rev (theorems `elt_gp`))
 else failwith `Theorem not of form |- GROUP(G,prod).`;;


% include_GROUP_theory : string -> thm -> thm list -> thm list		%
%									%
% include_GROUP_theory instantiates all the theorems from elt_gp.th,	% 
% simplifies them, removes all trivial theorems, stores the resulting   %
% theorems in the current theory under their old name prefixed by the   %
% given string, and returns them bound to the names under which they    %
% were stored.								%
%									%
% The string is the prefix to be added to the names of all the		%
% theorems from elt_gp.th after instantiation; the theorem must state   %
% that the desired example does form a group; the list of theorems are  %
% for use in simplifying the instantiated theorem, prior to storing.    %

%
let include_GROUP_theory name_prefix set_as_gp_thm rewrite_list =
 if fst(dest_const(rator(concl set_as_gp_thm))) = `GROUP`
 then 
  map
   (\ (thm_name, thm).
       (save_thm (thm_name, thm);
        autoload_theory
          (`theorem`,
           (current_theory()),
           (name_prefix^`_`^thm_name))))
   (filter (\ (name,thm).not((concl thm) = "T"))
    (return_GROUP_theory name_prefix set_as_gp_thm rewrite_list))
 else failwith `Theorem not of form |- GROUP(G,prod).`;;
%


let include_GROUP_theory name_prefix set_as_gp_thm rewrite_list =
 if fst(dest_const(rator(concl set_as_gp_thm))) = `GROUP`
 then 
 (map save_thm
   (filter (\ (name,thm).not((concl thm) = "T"))
    (return_GROUP_theory name_prefix set_as_gp_thm rewrite_list));
  include_theorems (current_theory ()))
 else failwith `Theorem not of form |- GROUP(G,prod).`;;

