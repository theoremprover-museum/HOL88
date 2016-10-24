% ===================================================================== %
% FILE		: lib_loader.ml						%
% DESCRIPTION   : A function for loading library into hol		%
%									%
% AUTHOR	: Wai Wong						%
% DATE		: 14 May 1993						%
% ===================================================================== %

%< --------------------------------------------------------------------- %
 This file defines a generic library loader as an ML function named
   library_loader.
 It carries out the standard loading procedures for loading the library.

 A library consists of three parts: theories, codes and document.	
 Any of these may be absent. The standard procedures of loading a library
 are:
    1) update the system search path to include the library directory;
    2) load any libraries on which the current library depends;
    3) load the theories (if there are any);
    4) load the codes (if there are any);
    5) update the help search path to include the current library document;
    6) set up auto-loading of theorems, definitions, etc.

 When a library, say foo, is loaded into a HOL session by evaluating   
    load_library `foo`;;
 This will load a file named `foo.ml` in the directory `foo` which is
 in the library seaarch path. The generic library loader, namely 
 library_loader, should be called with appropriate arguments in this file.
 (See the libraries auxiliary or more_lists for an example of calling this.)
 In addition, other functions may be called in this file to set up
 special environment necessary for working with the library.

 If one is not in draft mode, a library may not be loaded completely.
 In such case, a function whose name is created by prefixing the name
 of the library with `load_` is defined. This function can be called
 later to complete the loading.

 The definition of this library loading function is done dynamically
 by the ML function define_load_lib_function. Due to the way it is
 called by `let_before`, it can  take only a single argument, a
 string list. The information passed in this list consists of the
 library name, the names of theories and the names of the code files.
 The library name is the first string in the list and it is mandatory.
 The theory names and code file names follow, and they are separated by
 a null string. Both of these are optional. E.g. the simplest case is
 [`lib_name`; ``].
----------------------------------------------------------------------->%

let define_load_lib_function args =
    let split_args lst = let (lib_name.rest) = args in
    	let (thy,cod) = splitp (\x.x=``) rest in (lib_name,thy,tl cod) in
    let lib_path = library_pathname () in
    let autoload_defs_and_thms thy =
       (map (\name. autoload_theory(`definition`,thy,name))
         (map fst (definitions thy));
        map (\name. autoload_theory(`theorem`,thy,name))
     	(map fst (theorems thy));
        ()) in
    let (lib_name, theories, codes) = split_args args in
  \(v:void).
    if (mem lib_name (ancestry())) then
       (print_string (`Loading contents of `^lib_name^`...`); print_newline();
        let path st = (lib_path ^ `/` ^ lib_name ^ `/` ^ st) in
        (map (\name. load(path name, get_flag_value `print_lib`)) codes);
        (map autoload_defs_and_thms theories);
        (map delete_cache theories);
    	 ()) else
     failwith (`theory `^lib_name^` not an ancestor of the current theory`);;

%<--------------------------------------------------------------------------
 The loader function library_loader takes a 6-tuple as its argument.
 The fields of this are:
  lib_name : string --- the name of the library. It should be the name
    of the directory where the library is found, and the basename of
    the load file.
  parent_libs : string list --- the names of the library on which the
    current library depends. They will be loaded in the order given.
  theories : string list --- the names of the theories in this
    library. If the library contains more than one theory, the
    descendant of all other theories should be the first in the list.
    This will be loaded and becomes the current theory or the new
    parent of the current theory. The order of other names is not
    important. The axioms, definitions and theorems in all the
    theories listed are set up to be autoloaded.
  codes : string list --- the names of the code files. They will be
    loaded in the order given.
  load_parent : string --- the name of a file to be loaded before the
    code files are loaded. If we are not currently in draft mode, the
    parent libraries may not be loaded completely. Instead, functions
    having name prefixed by `load_` will be defined. These functions
    can be called in the file specified with this argument to complete
    the loading of the parent library. 
  part_path : string --- the directory name of the library part. If
    only part of the library is loaded, the lib_name string should have
    the part separator `:` in it, e.g. `lib:part`. It such case, the
    files of the library part may reside in a sub-directory. The name of
    this sub-directory is specified by this field, and it is added to
    the search path.
  help_paths : string list --- the names of directories containing the
    help files. These are relative to the subdirectory `help` of the
    library. They are added to the help_search_path.
------------------------------------------------------------------------->%

let library_loader =
      let autoload_defs_and_thms thy =
       (map (\name. autoload_theory(`definition`,thy,name))
    	 (map fst (definitions thy));
       	map (\name. autoload_theory(`theorem`,thy,name))
    	 (map fst (theorems thy));
    	 () )
      in
 \(lib_name, parent_libs, theories, codes, load_parent, part_path, help_paths).
    let path =
    	let root,part = splitp (\c.c = `:`) (explode lib_name) in
    	if (null part) 
    	then (library_pathname() ^ `/` ^ lib_name ^ `/`)
    	else (if (part_path = ``)
    	      then (library_pathname() ^ `/` ^ (implode root) ^ `/`)
    	      else (library_pathname() ^ `/` ^ (implode root) ^ `/` ^
    	    	    part_path ^ `/`))  in
    let top_thy = if null theories then `` else (hd theories) in
    
    (% Update the search path %
     print_string `Updating search path`; print_newline();
     set_search_path (union (search_path()) [path]);

     % Loading parent libraries %
     map load_library parent_libs;

     % Load (or attempt to load) the theory provided by this library %
     if not(top_thy = ``)
       then
     	(if draft_mode() 
           then (print_string (`Declaring theory `^top_thy^` a new parent`);
    	         print_newline();
                 new_parent top_thy)
           else (load_theory top_thy ?
             (print_string (`Defining ML function load_`^lib_name);
    	      print_newline() ;
    	      let_before((`load_`^lib_name), `define_load_lib_function`,
    	    	(lib_name. (theories @ (``. codes))));
              ())));

     % Load compiled code if possible %
    if (draft_mode() or (current_theory() = top_thy) or (top_thy=``))
     then
    	(if not((draft_mode()) or (load_parent=``))
    	    then  loadf load_parent;
         map (\name. load( name, get_flag_value `print_lib`)) codes;
    	 ());
    
    % Update online help path %
    let helppaths =
    	if null help_paths then [(path ^ `/help/`)]
    	else map (\s. path ^ `/help/` ^ s ^ `/`) help_paths in
        (print_string `Updating help search path`; print_newline();
    	 set_help_search_path (union helppaths (help_search_path())));

    % Set up autoloading of theorems and definitions %
    if (draft_mode() or (current_theory() = top_thy)) then
      (map autoload_defs_and_thms theories;
       map delete_cache theories;
       ());
    ());;
