% --------------------------------------------------------------------- %
%       Copyright (c) Jim Grundy 1992                                   %
%       All rights reserved                                             %
%                                                                       %
% Jim Grundy, hereafter referred to as `the Author', retains the        %
% copyright and all other legal rights to the Software contained in     %
% this file, hereafter referred to as `the Software'.                   %
%                                                                       %
% The Software is made available free of charge on an `as is' basis.    %
% No guarantee, either express or implied, of maintenance, reliability, %
% merchantability or suitability for any purpose is made by the Author. %
%                                                                       %
% The user is granted the right to make personal or internal use        %
% of the Software provided that both:                                   %
% 1. The Software is not used for commercial gain.                      %
% 2. The user shall not hold the Author liable for any consequences     %
%    arising from use of the Software.                                  %
%                                                                       %
% The user is granted the right to further distribute the Software      %
% provided that both:                                                   %
% 1. The Software and this statement of rights is not modified.         %
% 2. The Software does not form part or the whole of a system           %
%    distributed for commercial gain.                                   %
%                                                                       %
% The user is granted the right to modify the Software for personal or  %
% internal use provided that all of the following conditions are        %
% observed:                                                             %
% 1. The user does not distribute the modified software.                %
% 2. The modified software is not used for commercial gain.             %
% 3. The Author retains all rights to the modified software.            %
%                                                                       %
% Anyone seeking a licence to use this software for commercial purposes %
% is invited to contact the Author.                                     %
% --------------------------------------------------------------------- %
%============================================================================%
% CONTENTS: this file loads the compiled code for the library.               %
%============================================================================%
%$Id: load_code.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

if not compiling then
(
load ((library_pathname())^`/window/ml_ext`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/thms`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/hol_ext`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/tables`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/basic_close`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/eq_close`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/imp_close`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/win`, get_flag_value `print_lib`);
load ((library_pathname())^`/window/inter`, get_flag_value `print_lib`)
);;
