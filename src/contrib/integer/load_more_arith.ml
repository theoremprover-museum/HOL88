% FILE		: mk_more_arith.ml					%
% DESCRIPTION   : loads the theory more_arith.th, together with the     %
%                 the rule and tactic for general induction from	%
%                 num_tac.ml						%
%									%
% 		  Assumes more_arith.th is an ancestor of the current   %
%                 theory.						%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
%-----------------------------------------------------------------------%

% add_lib_path `group`;; Not needed for HOL88.1.05 (MJCG 14 April, 1989)%
% add_lib_path `integer`;;                                              %

if draft_mode () 
   then new_parent `more_arith`
   else ((load_theory `more_arith`)? (():void));;

loadf (library_pathname() ^ `/group/start_groups`);;

loadt `num_tac`;;

include_theory `more_arith`;;
