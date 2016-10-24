% ===================================================================== %
% FILE		: word.ml						%
% DESCRIPTION   : loads the library "word" into hol.			%
%									%
% AUTHOR	: Wai Wong						%
% DATE		: 14 May 1993						%
% ===================================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

let this_lib_name = `word`
and parent_libs = [`res_quan`]
and theories = [`word`; `word_base`;`word_bitop`;`bword_bitop`;
    `word_num`;`bword_num`;`bword_arith`]
and codes = [`word_convs`]
and load_parent = ``
and part_path = ``
and help_paths = [`entries`; `thms`]
in
library_loader (this_lib_name, parent_libs, theories, codes,
 load_parent, part_path, help_paths);;
