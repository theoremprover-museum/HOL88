% FILE		: load_elt_gp.ml					%
% DESCRIPTION   : loads the first-order group theory into HOL, together %
%                 with the tactics and functions from start.ml,         %
%                 group_tac.ml, and inst_gp.ml.				%
%									%
% 		  Assumes elt_gp.th an ancestor of the current theory.	%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
%-----------------------------------------------------------------------%

% add_lib_path `group`;; Not needed for HOL88.1.05 (MJCG 14 April 1989) %

if draft_mode () 
then new_parent `elt_gp`
else ((load_theory `elt_gp`)? (():void));;

loadf `start_groups`;;
include_theory `elt_gp`;;
loadt `group_tac`;;
loadt `inst_gp`;;
