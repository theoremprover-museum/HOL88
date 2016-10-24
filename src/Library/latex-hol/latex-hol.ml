% latex-hol.ml by Wai Wong 15 May 1990					%
% for loading the library latex-hol 					%

% --------------------------------------------------------------------- %
% Put the pathname to the library sets onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/latex-hol/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Add the help files to online help.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/latex-hol/help/entries/` in
    print_newline();
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Loading the prettyp library	    					%
% --------------------------------------------------------------------- %

load_library `prettyp:PP_printer`;;

    map (\st. loadf(st))
        [`filters`;
    	 `hol_trees`;
         `precedence`;
         `latex_type_pp`;
         `latex_term_pp`;
         `latex_thm_pp`;
    	 `latex_sets_pp`;
    	 `formaters`];;

%-----------------------------------------------------------------------------%
