% sets.ml                                               (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Function to determine whether a list contains any repetitions %

letrec no_rep l =

   % : (* list -> bool) %

   if (null l)
   then true
   else if (mem (hd l) (tl l))
        then false
        else no_rep (tl l);;


% Function to remove any repetitions in a list %

letrec remove_rep l =

   % : (* list -> * list) %

   if (null l)
   then []
   else if (mem (hd l) (tl l))
        then (remove_rep (tl l))
        else (hd l).(remove_rep (tl l));;


% Function to determine if one list (containing no repetitions) is a %
% subset of another list (containing no repetitions).                %

% The function tests if subl is a subset of l by subtracting (setwise) l %
% from subl. If this gives a null list, then subl is a subset of l.      %

let is_subset l subl = null (subtract subl l);;

   % : (* list -> * list -> bool) %


%----------------------------------------------------------------------------%
