% ===================================================================== %
% FILE: enable.ml 	DATE: 16 July 93    BY: Wai WONG		%
% Loads the record_proof library.    					%
% ===================================================================== %

let this_lib_name = `record_proof:enable`
and parent_libs = []
and theories = []
and codes = [`proof_rec`]
and load_parent = ``
and part_path = ``
and help_paths = [`entries`]
in
library_loader (this_lib_name, parent_libs, theories, codes,
 load_parent, part_path, help_paths);;
