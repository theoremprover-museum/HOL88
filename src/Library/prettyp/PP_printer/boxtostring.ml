% boxtostring.ml                                                              %
%-----------------------------------------------------------------------------%

begin_section boxtostring;;

%  Function to join two strings with specified x-coordinates into one string  %

%  The function fails if the strings are overlapping.  %

let join_strings (s1,x1) (s2,x2) =

   % : (string # int -> string # int -> string # int) %

   if (x1 = x2)
   then if ((s1 = ``) or (s2 = ``))
        then (s1 ^ s2,x1)
        else failwith `join_strings -- overlapping strings`
   else if (x1 < x2)
        then let sep = x2 - (x1 + length (explode s1))
             in  if (sep < 0)
                 then failwith `join_strings -- overlapping strings`
                 else (s1 ^ (string_copies ` ` sep) ^ s2,x1)
        else let sep = x1 - (x2 + length (explode s2))
             in  if (sep < 0)
                 then failwith `join_strings -- overlapping strings`
                 else (s2 ^ (string_copies ` ` sep) ^ s1,x2);;


%  Function to merge two lists of strings with x and y-coordinates.  %

%  The two input lists should be in increasing order of y coordinate and    %
%  contain at most one string for each value of y.  The resulting list has  %
%  the same properties.                                                     %

letrec merge_string_lists sl1 sl2 =

   % : ((string # int # int) list -> (string # int # int) list ->    %
   %                                      (string # int # int) list) %

   if (null sl1)
   then sl2
   else if (null sl2)
        then sl1
        else let (s1,x1,y1) = hd sl1
             and (s2,x2,y2) = hd sl2
             in (if (y1 = y2) then
                   (let (s,x) = join_strings (s1,x1) (s2,x2)
                    in  (s,x,y1).(merge_string_lists (tl sl1) (tl sl2)))
                 if (y1 < y2) then
                    (hd sl1).(merge_string_lists (tl sl1) sl2)
                 if (y1 > y2) then
                    (hd sl2).(merge_string_lists sl1 (tl sl2))
                 else fail);;


%  Function to convert a box of text into a list of strings.  %

%  The x,y coordinates of the origin of the box must be specified.  %
%  The `labels' in the box are discarded.                           %

letrec stringify_print_box x y pb =

   % : (int -> int -> * print_box -> (string # int # int) list) %

   case pb
   of (N_box) . []
    | (A_box ((_,s),_)) . [s,x,y]
    | (L_box ((_,sep,pb1,pb2),_)) .
         (merge_string_lists (stringify_print_box x y pb1)
           (stringify_print_box (x + (print_box_width pb1) + (Int sep)) y pb2))
    | (C_box ((_,_,(x2,y2),pb1,pb2),_)) .
         (merge_string_lists (stringify_print_box x y pb1)
             (stringify_print_box (x + x2) (y + (Int y2)) pb2));;


%  Function to convert a list of strings (with coordinates) into a list of  %
%  strings suitable for use as output.                                      %

%  The y coordinates of the top and bottom of the block of text must be      %
%  specified. If any of the strings in the input list are out of the text    %
%  region specified, an error occurs. This error will only reach top-level   %
%  if debugging is set to true. Otherwise, the string `*error*' is inserted  %
%  in the text produced.                                                     %

letrec fill_in_strings debug t b sl =

   % : (bool -> int -> int -> (string # int # int) list -> string list) %

   if ((t = b) or (t > b))
   then if (null sl)
        then []
        else if debug
             then failwith `fill_in_strings -- string below specified region`
             else [`*error*`]
   else if (null sl)
        then (``).(fill_in_strings debug (t+1) b sl)
        else let (s,x,y) = hd sl
             in  if (x < 0)
                 then if debug
                      then failwith (`fill_in_strings -- ` ^
                                      `string to the left of specified region`)
                      else fill_in_strings debug t b ((`*error*`,0,y).(tl sl))
                 else if (y < t)
                      then if debug
                           then failwith (`fill_in_strings -- ` ^
                                             `string above specified region`)
                           else (`*error*`).(fill_in_strings debug t b (tl sl))
                      else if (y = t)
                           then ((string_copies ` ` x) ^ s).
                                   (fill_in_strings debug (t+1) b (tl sl))
                           else (``).(fill_in_strings debug (t+1) b sl);;


%  Function to convert a box of text into a list of strings suitable for  %
%  output.                                                                %

%  An indentation from the left margin must be specified. The `debug'  %
%  argument determines whether or not errors reach top-level.          %

%  The `labels' in the box are discarded.                              %

let print_box_to_strings debug i pb =

   % : (bool -> int -> * print_box -> string list) %

   fill_in_strings debug 0 (print_box_height pb) (stringify_print_box i 0 pb);;

print_box_to_strings;;
end_section boxtostring;;
let print_box_to_strings = it;;


%-----------------------------------------------------------------------------%
