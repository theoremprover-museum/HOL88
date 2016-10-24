% ===================================================================== %
% FILE		: mk_word.ml						%
% DESCRIPTION   : Create the theory word as the descedent theory of	%
%   	    	  all the word_xxx theories.				%
% WRITES FILE   : word.th  	    					%
%									%
% AUTHOR	: (c) Wai Wong						%
% DATE		: 24 September 1992					%
% ===================================================================== %

loadt(`ver_`^(string_of_int(version())));;

new_theory`word`;;

map new_parent [`bword_bitop`; `bword_num`; `bword_arith`];;

close_theory();;
