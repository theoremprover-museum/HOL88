% ===================================================================== %
% FILE		: unwind.ml						%
% DESCRIPTION   : loads the library "unwind" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE    	: 90.12.01						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/unwind/mjcg-unwind` in
    load(path, get_flag_value `print_lib`);;

