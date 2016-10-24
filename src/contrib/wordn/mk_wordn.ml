% ===================================================================== %
% FILE		: mk_wordn.ml						%
% DESCRIPTION   : Create the theory wordn as the descedent theory of	%
%   	    	  all the wordn_xxx theories.				%
% WRITES FILE   : wordn.th  	    					%
%									%
% AUTHOR	: (c) Wai Wong						%
% DATE		: 2 April 1992					        %
% ===================================================================== %

new_theory`wordn`;;

map new_parent [`wordn_base`; `wordn_bitops`; `wordn_num`];;

close_theory();;
