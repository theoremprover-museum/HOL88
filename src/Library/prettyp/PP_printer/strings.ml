% strings.ml                                                                  %
%-----------------------------------------------------------------------------%


%  String functions.  %


%  Function to obtain a sub-string of a string s. The first i characters are  %
%  discarded, and the next l characters are taken as the sub-string. The      %
%  function fails if the string is not long enough to meet the requirements.  %

let substr i l s =

   % : (int -> int -> string -> string) %

   letrec substr' i' l' sl sl' =

      % : (int -> int -> string list -> string list -> string list) %

      if (i' > 0)
      then if (null sl)
           then failwith `substr -- string too short`
           else substr' (i'-1) l' (tl sl) sl'
      else if (l' > 0)
           then if (null sl)
                then failwith `substr -- string too short`
                else substr' i' (l'-1) (tl sl) ((hd sl).sl')
           else rev sl'

   in implode (substr' i l (explode s) []);;


%  Function to find the number of characters in a string.  %

let strlen s =

   % : (string -> int) %

   length (explode s);;


%  Function to compute the length of the longest sequence of characters from  %
%  some set which begins a string.                                            %

let num_of_leading_chars chars s =

   % : (string list -> string -> int) %

   letrec num_of_leading n chars sl =

      % : (int -> string list -> string list -> int) %

      if (null sl)
      then n
      else if (mem (hd sl) chars)
           then num_of_leading (n+1) chars (tl sl)
           else n

   in num_of_leading 0 chars (explode s);;


%  Function to remove characters from the beginning of a string. Characters  %
%  are removed until a character is encountered which does not occur in the  %
%  set of specified characters.                                              %

let trim_leading_chars chars s =

   % : (string list -> string -> string) %

   letrec trim chars sl =

      % : (string list -> string list -> string list) %

      if (null sl)
      then []
      else if (mem (hd sl) chars)
           then trim chars (tl sl)
           else sl

   in (implode o (trim chars) o explode) s;;


%  Function to remove characters from the end of a string. Characters are    %
%  removed until a character is encountered which does not occur in the set  %
%  of specified characters.                                                  %

let trim_trailing_chars chars s =

   % : (string list -> string -> string) %

   letrec trim chars sl =

      % : (string list -> string list -> string List) %

      if (null sl)
      then []
      else let rest = trim chars (tl sl)
           in  if ((null rest) & (mem (hd sl) chars))
               then []
               else (hd sl).rest

   in (implode o (trim chars) o explode) s;;


%  Function to remove characters from the beginning and end of a string in  %
%  the manner of `trim_leading_chars' and `trim_trailing_chars'.            %

let trim_enclosing_chars chars s =

   % : (string list -> string -> string) %

   trim_trailing_chars chars (trim_leading_chars chars s);;


%  Function to test containment of string s2 in string s1.  %

letrec string_contains s1 s2 =

   % : (string -> string -> bool) %

   if ((strlen s2) > (strlen s1))
   then false
   else if ((substr 0 (strlen s2) s1) = s2)
        then true
        else string_contains ((implode o tl o explode) s1) s2;;


%  Function to test containment of string s within the strings sl.  %

letrec strings_contain sl s =

   % : (string list -> string -> bool) %

   itlist (\x y. (string_contains x s) or y) sl false;;


%  Function to make a string which is n copies of the string s.  %

letrec string_copies s n =

   % : (string -> int -> string) %

   if (n < 1)
   then ``
   else s ^ (string_copies s (n - 1));;


%-----------------------------------------------------------------------------%
