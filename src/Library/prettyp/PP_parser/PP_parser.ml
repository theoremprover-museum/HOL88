%=============================================================================%
%                                                                             %
%                             A General-Purpose                               %
%                               Pretty-Printer                                %
%                             for the HOL System                              %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Filename: PP_parser.ml (Compiler for pretty-printing language)             %
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
%     pp_lang1_pp.ml                                                          %
%     pp_lang2_pp.ml                                                          %
%     lex.ml                                                                  %
%     syntax.ml                                                               %
%     convert.ml                                                              %
%     generate.ml                                                             %
%     PP_to_ML.ml                                                             %
%                                                                             %
%-----------------------------------------------------------------------------%
%                                                                             %
%  Changes history:                                                           %
%                                                                             %
%  Version 0.0 (pre-release), 23rd March 1990                                 %
%                                                                             %
%     No changes.                                                             %
%                                                                             %
%  Version 1.0, 11th December 1990                                            %
%                                                                             %
%     No changes.                                                             %
%                                                                             %
%  Version 1.1, 5th August 1991                                               %
%                                                                             %
%=============================================================================%

%-----------------------------------------------------------------------------%
% Load the compiled code into ml.                                             %
%-----------------------------------------------------------------------------%

let path st = library_pathname() ^ `/prettyp/PP_parser/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`pp_lang1_pp`;
         `pp_lang2_pp`;
         `lex`;
         `syntax`;
         `convert`;
         `generate`;
         `PP_to_ML`];;

%-----------------------------------------------------------------------------%
