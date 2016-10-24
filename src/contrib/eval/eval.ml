% ===================================================================== %
% FILE		: eval.ml						%
% DESCRIPTION   : loads the library "eval" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE    	: 90.12.01						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Fasl in the compiled lisp code.					%
% --------------------------------------------------------------------- %
lisp `(load (concat %lib-dir '|/eval/eval|))`;;
lisp `(load (concat %lib-dir '|/eval/dml-eval|))`;;

% --------------------------------------------------------------------- %
% Now, load the compiled code into ml.					%
% --------------------------------------------------------------------- %
let path = library_pathname() ^ `/eval/wordn` in
    load(path, get_flag_value `print_lib`);;

