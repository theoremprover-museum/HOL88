% ===================================================================== %
% FILE		: record_proof.ml					%
% DESCRIPTION   : loads the library "record-proof" into hol.		%
%									%
% AUTHOR	: Wai Wong						%
% DATE		: 15 July 1993						%
% ===================================================================== %

let this_lib_name = `record_proof`
and parent_libs = []
and theories = []
and codes = [`proof_rec`]
and load_parent = ``
and part_path = ``
and help_paths = [`entries`]
in
library_loader (this_lib_name, parent_libs, theories, codes,
 load_parent, part_path, help_paths);;
