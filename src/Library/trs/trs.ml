%============================================================================%
%                                                                            %
%                                                                            %
%            A   T H E O R E M   R E T R I E V A L   S Y S T E M             %
%                                                                            %
%                               F O R   T H E                                %
%                                                                            %
%                            H O L   S Y S T E M                             %
%                                                                            %
%                                                                            %
%                           (c) R.J.Boulton 1990                             %
%                                                                            %
%----------------------------------------------------------------------------%
%                                                                            %
%  Filename: trs.ml                                                          %
%  Version:  1.0                                                             %
%  Author:   Richard J. Boulton                                              %
%  Date:     14th July 1990                                                  %
%                                                                            %
%  Special instructions: none                                                %
%                                                                            %
%----------------------------------------------------------------------------%
%                                                                            %
%  Load sub-files in the following order:                                    %
%                                                                            %
%     extents.ml                                                             %
%     sets.ml                                                                %
%     extract.ml                                                             %
%     struct.ml                                                              %
%     name.ml                                                                %
%     thmkind.ml                                                             %
%     matching.ml                                                            %
%     sidecond.ml                                                            %
%     search.ml                                                              %
%     user.ml                                                                %
%                                                                            %
%----------------------------------------------------------------------------%
%                                                                            %
%  Changes history: none                                                     %
%                                                                            %
%============================================================================%

% --------------------------------------------------------------------- %
% Add the trs help files to online help.                                %
% --------------------------------------------------------------------- %

let path1 = library_pathname() ^ `/trs/help/entries/`
and path2 = library_pathname() ^ `/trs/help/internals/`
in  print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path1;path2] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load the compiled code into ml.                                       %
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/trs/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`extents`;
         `sets`;
         `extract`;
         `struct`;
         `name`;
         `thmkind`;
         `matching`;
         `sidecond`;
         `search`;
         `user`];;

%----------------------------------------------------------------------------%
