% extents.ml                                                                  %
%-----------------------------------------------------------------------------%


%  General-purpose extentions to ML required by the pretty-printer.  %


%  Function to find the maximum element of a list of integers.  %

%  Fails if given a null list.  %

let max l =

   % : (int list -> int) %

   letrec max_fun m l =

      % : (int -> int list -> int) %

      if (null l)
      then m
      else if ((hd l) > m)
           then max_fun (hd l) (tl l)
           else max_fun m (tl l)

   in if (null l)
      then failwith `max -- null list given`
      else max_fun (hd l) (tl l);;


%  Function to find the minimum element of a list of integers.  %

%  Fails if given a null list.  %

let min l =

   % : (int list -> int) %

   letrec min_fun m l =

      % : (int -> int list -> int) %

      if (null l)
      then m
      else if ((hd l) < m)
           then min_fun (hd l) (tl l)
           else min_fun m (tl l)

   in if (null l)
      then failwith `min -- null list given`
      else min_fun (hd l) (tl l);;


%  Function to replace the values associated with a list of keys in an      %
%  association list. If a key is not in the association list it is added.   %
%  If a key occurs more than once, only one remains (unless the key occurs  %
%  more than once in the changes). The order of the keys is changed.        %

letrec change_assocl assocl changes =

   % : ((* # **) list -> (* # **) list -> (* # **) list) %

   if (null assocl)
   then changes
   else if (can (assoc (fst (hd assocl))) changes)
        then (change_assocl (tl assocl) changes)
        else (hd assocl).(change_assocl (tl assocl) changes);;


%  Abstract datatype for natural numbers (where zero is taken to be natural)  %

abstype nat = int
   with Nat n = if (n < 0)
                then failwith `Nat -- number cannot be negative`
                else abs_nat n
   and  Int n = rep_nat n
   and  print_nat n = print_int (rep_nat n);;

%  Directive to print natural numbers as if they were integers.  %

top_print print_nat;;


%  Function to find the current display width.  %

let get_margin (():void) =

   % : (void -> int) %

   let old = set_margin 0
   in  let new = set_margin old
       in  old;;


%-----------------------------------------------------------------------------%
