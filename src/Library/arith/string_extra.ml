%****************************************************************************%
% FILE          : string_extra.ml                                            %
% DESCRIPTION   : Additional functions for ML strings.                       %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 13th January 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% string_less : string -> string -> bool                                     %
%                                                                            %
% Lexicographical less-than on strings.                                      %
%----------------------------------------------------------------------------%

let string_less s1 s2 =
   letrec string_less' l1 l2 =
      if (null l2) then false
      if (null l1) then true
      else let a1 = ascii_code (hd l1)
           and a2 = ascii_code (hd l2)
           in  if (a1 < a2) then true
               if (a1 = a2) then string_less' (tl l1) (tl l2)
               else false
   in string_less' (explode s1) (explode s2);;
