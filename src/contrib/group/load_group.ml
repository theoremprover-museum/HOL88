% ===================================================================== %
% FILE		: load_group.ml						%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "group" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_group.					%
% --------------------------------------------------------------------- %

let load_group (v:void) =
    if (mem `more_gp` (ancestry())) then
       (print_string `Loading contents of group...`; print_newline();
        include_theory `elt_gp`;
        include_theory `more_gp`;
        let path st = library_pathname() ^ `/group/` ^ st in
            load(path `group_tac`, get_flag_value `print_lib`);
            load(path `inst_gp`, get_flag_value `print_lib`); ()) else
       failwith `theory more_gp not an ancestor of the current theory`;;

