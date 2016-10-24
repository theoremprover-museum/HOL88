% FILE		: add_lib_path.ml					%
% DESCRIPTION   : defines a function for easy addition of a path for a	%
%		  subdirectory of Library				%
%									%
%		This function, or something like it, should be built	%
%		into HOL.						%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.25						%
%									%
%-----------------------------------------------------------------------%


% lib_path () is a string whose contents is that of lib-dir %

let lib_dir =
 (lisp `(setq %search-path (cons %lib-dir %search-path))`;
  let (value.original_list) = (search_path ()) in
   (set_search_path original_list;value));;

let add_lib_path dir_name =
 let old_search_path = (search_path()) in
 let full_path = (lib_dir^`/`^dir_name^`/`) in
 if mem full_path old_search_path
 then old_search_path
 else set_search_path (old_search_path @ [full_path]);;
