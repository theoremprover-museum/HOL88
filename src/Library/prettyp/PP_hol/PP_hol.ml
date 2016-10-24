%=============================================================================%
%                                                                             %
%                             A General-Purpose                               %
%                               Pretty-Printer                                %
%                             for the HOL System                              %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Filename: PP_hol.ml (A pretty-printer for HOL types, terms, and theorems)  %
%  Version:  1.1                                                              %
%  Author:   Richard J. Boulton                                               %
%  Date:     5th August 1991                                                  %
%                                                                             %
%  Special instructions: Requires PP_printer.ml to be pre-loaded.             %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Load sub-files in the following order:                                     %
%                                                                             %
%     hol_trees.ml                                                            %
%     precedence.ml                                                           %
%     hol_type_pp.ml                                                          %
%     hol_term_pp.ml                                                          %
%     hol_thm_pp.ml                                                           %
%     new_printers.ml                                                         %
%     link_to_hol.ml                                                          %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Changes history:                                                           %
%                                                                             %
%  Version 0.0 (pre-release), 23rd March 1990                                 %
%                                                                             %
%     The parse-tree representations of types and terms used nodes labelled   %
%     with `NAME' for constant and variable names. It is sufficient to use    %
%     simply the name of the variable or constant concerned. The nodes        %
%     labelled `NAME' have therefore been stripped away.                      %
%                                                                             %
%     `assignable_print_term' is now set to the new term printer so that      %
%     goals are printed using the new printer.                                %
%                                                                             %
%  Version 1.0, 11th December 1990                                            %
%                                                                             %
%     The pretty-printing rules for terms have been modified so that long     %
%     lists of bound variables are broken across lines if necessary. In the   %
%     previous version the list of variables could not be split between       %
%     lines.                                                                  %
%                                                                             %
%  Version 1.1, 5th August 1991                                               %
%                                                                             %
%=============================================================================%

%-----------------------------------------------------------------------------%
% Load the compiled code into ml.                                             %
%-----------------------------------------------------------------------------%

let path st = library_pathname() ^ `/prettyp/PP_hol/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`hol_trees`;
         `precedence`;
         `hol_type_pp`;
         `hol_term_pp`;
         `hol_thm_pp`;
         `new_printers`;
         `link_to_hol`];;

%-----------------------------------------------------------------------------%
