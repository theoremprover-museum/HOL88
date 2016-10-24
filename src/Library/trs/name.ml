% name.ml                                               (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Abstract datatype for string wildcards %

abstype wildchar = string

   % Function to convert a wildchar into a string %

   with show_wildchar w = rep_wildchar w

      % : (wildchar -> string) %

   % Function to make a wildchar from a string %

   % A string can only be made into a wildchar if it is of length 1. %

   and  make_wildchar s =

      % : (string -> wildchar) %

      if (length o explode) s = 1
      then abs_wildchar s
      else failwith `make_wildchar -- wildchar must be a single character`;;


% Abstract type for patterns used to match theory names and theorem names %

% The string represents the pattern. The first of the wildchars is the    %
% character which is to be used to mean `match any character'. The second %
% wildchar is the character which is to be used to mean `match any number %
% of characters (including none)'.                                        %

abstype namepattern = string # wildchar # wildchar

   % Function to convert a namepattern into its representing type %

   with show_namepattern np = rep_namepattern np

      % : (namepattern -> string # wildchar # wildchar) %

   % Function to make a namepattern from a string and two wildchars %

   % This will only succeed if the two wildchars are different. The pattern %
   % is simplified here, so that it need not be done every time a match is  %
   % performed.                                                             %

   and make_namepattern (s,w1,wn) =

      % : (string # wildchar # wildchar -> namepattern) %

      % Function to simplify a pattern, so that matching is easier. %

      % For example with wild1 = `?` and wildn = `*`, the following %
      % transformations are made:                                   %
      %                                                             %
      % `a***b`   --> `a*b`                                         %
      % `a*?*b`   --> `a?*b`                                        %
      % `a**?*?`  --> `a??*`                                        %
      % `a?b?`    --> `a?b?`                                        %
      % `a*?**b*` --> `a?*b*`                                       %

     (let simplify wild1 wildn sp =

         % : (wildchar -> wildchar -> string -> string) %

         % Subsidiary function to do most of the work. %

         % The boolean value is used to keep track of whether or not a      %
         % `wildn' character has been encountered. While passing through a  %
         % sequence of wildcard characters, `b' will be set to true if a    %
         % `wildn' is encountered, and the `wildn' will be omitted. At the  %
         % end of the wildcard sequence, a `wildn' will be inserted and `b' %
         % will be reset to false.                                          %

        (letrec simplify' s1 sn b l =

            % : (string -> string -> bool -> string list -> string list) %

            if (null l)
            then if b then [sn] else []
            else if (hd l) = sn then simplify' s1 sn true (tl l)
                 if (hd l) = s1 then s1.(simplify' s1 sn b (tl l))
                 else if b
                      then sn.(hd l).(simplify' s1 sn false (tl l))
                      else (hd l).(simplify' s1 sn false (tl l))

         % Call subsidiary function with wildcards (converted to strings), %
         % `wildn' inactive, and with the pattern converted to a list of   %
         % single-character strings. Then convert the processed list back  %
         % to a string.                                                    %

         in implode (simplify' (show_wildchar wild1) (show_wildchar wildn)
                                                         false (explode sp))
        )

      in if w1 = wn
         then failwith `make_namepattern -- wildchars must be different`
         else abs_namepattern ((simplify w1 wn s),w1,wn)
     );;


% Function to convert a namepattern into the three strings representing it %

let show_full_namepattern np =

   % : (namepattern -> string # string # string) %

   let (s,w1,wn) = show_namepattern np
   in  (s,show_wildchar w1,show_wildchar wn);;


% Function to make a namepattern from three strings %

% The first string represents the pattern. The second is the wildcard        %
% character which means `match any character', and the third is the wildcard %
% character which means `match any number of characters (including none)'.   %

let make_full_namepattern (s,c1,cn) =

   % : (string # string # string -> namepattern) %

   make_namepattern (s,make_wildchar c1,make_wildchar cn);;


% Default values for wildcards in namepatterns %

let wildchar1 = `?`
and wildcharn = `*`;;


% Function to convert a string into a namepattern using the default %
% wildcard characters.                                              %

let autonamepattern s = 

   % : (string -> namepattern) %

   make_full_namepattern (s,wildchar1,wildcharn);;


% Function to match a namepattern against a string %

let namematch p s =

   % : (namepattern -> string -> bool) %

   % Extract components of namepattern. %

   let (spatt,wild1,wildn) = show_full_namepattern p

       % Function to perform the match %

       % The last two arguments are the pattern and string converted to  %
       % lists of single-character strings.                              %
       % The function has no data to return, so it either returns (),    %
       % or it fails. This is done rather than returning a boolean value %
       % so that exception handling can be used for backtracking.        %

       % If both the pattern and the string are exhausted, succeed.      %
       % If only the pattern is exhausted, fail.                         %
       % If the remainder of the pattern is `wildn' on its own, succeed. %
       % Any other pattern matched against a null string must fail.      %

       % If the first character in the pattern is `wildn', try matching  %
       % it against nothing, and if this fails, try matching it against  %
       % one or more characters of the string (by recursion).            %

       % If the first character of the pattern is `wild1', match it to   %
       % the first character of the string, and try to match the tails.  %
       % Do the same if the head of the pattern equals the head of the   %
       % string. If the heads differ, fail.                              %

       % Note that this function has been specially written to be        %
       % efficient for the pattern `wildn` (on its own), i.e. for the    %
       % pattern which means `match anything'.                           %

       % The function does not cater for quotation of the characters     %
       % used as wildcards.                                              %

   in  letrec stringmatch w1 wn pl sl =

          % : (string -> string -> string list -> string list -> void) %

          if (null pl)
          then if (null sl)
               then ()
               else failwith `no match`
          else if ((hd pl = wn) & (null (tl pl)))
               then ()
               else if (null sl)
                    then failwith `no match`
                    else if (hd pl) = wn then (  (stringmatch w1 wn (tl pl) sl)
                                              ?? [`no match`]
                                                 (stringmatch w1 wn pl (tl sl))
                                              )
                         if (hd pl) = w1 then
                               (stringmatch w1 wn (tl pl) (tl sl))
                         if (hd pl) = (hd sl) then
                               (stringmatch w1 wn (tl pl) (tl sl))
                         else failwith `no match`

       % Convert the pattern and the string to a list of        %
       % single-character strings, and attempt a match. If the  %
       % match succeeds return true. If it fails, return false. %

       in can (stringmatch wild1 wildn (explode spatt)) (explode s);;


%----------------------------------------------------------------------------%
