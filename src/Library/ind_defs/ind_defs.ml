% ===================================================================== %
% FILE		: ind_defs.ml						%
% DESCRIPTION   : loads the library "ind_defs" into hol.		%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.10.30						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %
let path = library_pathname() ^ `/ind_defs/ind-defs` in
    load(path, get_flag_value `print_lib`);;
