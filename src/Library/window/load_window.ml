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
% CONTENTS: used to load the library if it was not possible at first.        %
%============================================================================%
%$Id: load_window.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

let load_window (():void) =
    (
        if (not (mem `win` (ancestry()))) & (draft_mode()) then
        (
            print_string `Declaring theory win a new parent`;
            print_newline();
            new_parent `win`
        )
    );
    (
        if (mem `win` (ancestry())) then
            (
                print_string `Loading contents of window library:`;
                print_newline();
                load_library `window:load_code`
            )
        else
            failwith `theory win not loaded or not in draft mode`
    );;
