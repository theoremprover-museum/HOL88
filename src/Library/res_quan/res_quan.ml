% ===================================================================== %
% FILE: res_quan.ml 	DATE: 1 Aug 92 	BY: Wai WONG			%
% Loads the res_quan library.	    					%
% ===================================================================== %
% WW 17 May 93 Modified to call the library loader.			%
% ===================================================================== %

let this_lib_name = `res_quan`
and parent_libs = []
and theories = [`res_quan`]
and codes = [`cond_rewr`; `res_rules`]
and load_parent = ``
and part_path = ``
and help_paths = [`entries`]
in
library_loader (this_lib_name, parent_libs, theories, codes,
 load_parent, part_path, help_paths);;
