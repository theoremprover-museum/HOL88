% ===================================================================== %
% FILE		: load_wordn.ml						%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "wordn" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% MODIFIED by	: Wai Wong						%
% DATE		: 2 April 1992						%
%   	Modified to load more codes and theories			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_wordn.					%
% --------------------------------------------------------------------- %

let load_wordn (v:void) =
    if (mem `wordn` (ancestry())) then
       (print_string `Loading contents of wordn...`; print_newline();
        let path st = `./wordn/` ^ st in
        (map (\name. load(path name, get_flag_value `print_lib`))
    	    [`wordn_rules`; `wordn_conv`; `wordn_bit_op`;
    	     `wordn_num`]);
    	 ()) else
     failwith `theory wordn not an ancestor of the current theory`;;

