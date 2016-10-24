%============================================================================%
% Creates a function that loads the contents of the library                  %
% "wellorder" into hol.                                                      %
%============================================================================%

%----------------------------------------------------------------------------%
% Define the function load_wellorder.                                        %
%----------------------------------------------------------------------------%

let load_wellorder (():void) =
    if (mem `WELLORDER` (ancestry())) then
       (print_string `Loading contents of WELLORDER...`; print_newline();
        let defs = map fst (definitions `WELLORDER`) in
            map (\st. autoload_theory(`definition`,`WELLORDER`,st)) defs;
        let thms = [`KL`; `HP`; `ZL`; `WO`] in
            map (\st. autoload_theory(`theorem`,`WELLORDER`,st)) thms;
        delete_cache `WELLORDER`; ()) else
    failwith `theory WELLORDER not an ancestor of the current theory`;;
