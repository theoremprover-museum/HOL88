% --------------------------------------------------------------------- %
% 		Copyright (c) Jim Grundy 1992				%
%               All rights reserved                                     %
%									%
% Jim Grundy, hereafter referred to as `the Author', retains the	%
% copyright and all other legal rights to the Software contained in	%
% this file, hereafter referred to as `the Software'.			%
% 									%
% The Software is made available free of charge on an `as is' basis.	%
% No guarantee, either express or implied, of maintenance, reliability	%
% or suitability for any purpose is made by the Author.			%
% 									%
% The user is granted the right to make personal or internal use	%
% of the Software provided that both:					%
% 1. The Software is not used for commercial gain.			%
% 2. The user shall not hold the Author liable for any consequences	%
%    arising from use of the Software.					%
% 									%
% The user is granted the right to further distribute the Software	%
% provided that both:							%
% 1. The Software and this statement of rights is not modified.		%
% 2. The Software does not form part or the whole of a system 		%
%    distributed for commercial gain.					%
% 									%
% The user is granted the right to modify the Software for personal or	%
% internal use provided that all of the following conditions are	%
% observed:								%
% 1. The user does not distribute the modified software. 		%
% 2. The modified software is not used for commercial gain.		%
% 3. The Author retains all rights to the modified software.		%
%									%
% Anyone seeking a licence to use this software for commercial purposes	%
% is invited to contact the Author.					%
% --------------------------------------------------------------------- %
% CONTENTS: puts it all together in the right order.			%
% --------------------------------------------------------------------- %
%$Id: pair.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% Extend the help search path                                               %
print_newline();
print_string `Extending help search path`;
print_newline();
let path1 = (library_pathname())^`/pair/help/entries/`
and path2 = (library_pathname())^`/pair/help/thms/` in
    set_help_search_path (union [path1; path2] (help_search_path()));;

if not compiling then
(
    load ((library_pathname())^`/pair/syn`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/basic`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/both1`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/all`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/exi`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/both2`, get_flag_value `print_lib`);
    load ((library_pathname())^`/pair/conv`, get_flag_value `print_lib`)
);;

let pair_version =
    implode (rev (tl (tl (rev (tl (explode `$Revision: 3.1 $`))))));;

print_newline();
print_string (`pair Library (`^pair_version^`) loaded.`);
print_newline ();
print_string `Copyright (c) Jim Grundy 1992`;
print_newline ();;
print_string `All rights reserved`;
print_newline ();;
