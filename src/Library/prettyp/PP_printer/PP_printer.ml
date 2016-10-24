%=============================================================================%
%                                                                             %
%                             A General-Purpose                               %
%                               Pretty-Printer                                %
%                             for the HOL System                              %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Filename: PP_printer.ml (Main pretty-printing program)                     %
%  Version:  1.1                                                              %
%  Author:   Richard J. Boulton                                               %
%  Date:     5th August 1991                                                  %
%                                                                             %
%  Special instructions: none                                                 %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Load sub-files in the following order:                                     %
%                                                                             %
%     extents.ml                                                              %
%     strings.ml                                                              %
%     ptree.ml                                                                %
%     treematch.ml                                                            %
%     boxes.ml                                                                %
%     treetobox.ml                                                            %
%     boxtostring.ml                                                          %
%     print.ml                                                                %
%     utils.ml                                                                %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Changes history:                                                           %
%                                                                             %
%  Version 0.0 (pre-release), 23rd March 1990                                 %
%                                                                             %
%     Changes to the file `print.ml':                                         %
%                                                                             %
%     The function `insert_strings' (used by `pp') has been modified to       %
%     interface in a better way to the standard HOL pretty-printer. It now    %
%     uses `print_break' instead of line-feeds.                               %
%                                                                             %
%     The function `output_strings' has been modified to take a file handle   %
%     as argument instead of a file name.                                     %
%                                                                             %
%     A function `pp_write' has been added to pretty-print to a file given    %
%     the appropriate file handle.                                            %
%                                                                             %
%  Version 1.0, 11th December 1990                                            %
%                                                                             %
%     Pretty-printing box structure extended to allow sub-tree addresses to   %
%     be stored in the structure. This enables one to determine what part of  %
%     the print-tree was used to generate a sub-box (when applicable).        %
%                                                                             %
%  Version 1.1, 5th August 1991                                               %
%                                                                             %
%=============================================================================%

%-----------------------------------------------------------------------------%
% Load the compiled code into ml.                                             %
%-----------------------------------------------------------------------------%

let path st = library_pathname() ^ `/prettyp/PP_printer/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`extents`;
         `strings`;
         `ptree`;
         `treematch`;
         `boxes`;
         `treetobox`;
         `boxtostring`;
         `print`;
         `utils`];;

%-----------------------------------------------------------------------------%
