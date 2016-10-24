% lib.ml --- Some utility functions
%
let merge_sort p =
   letrec merge list1 list2 = 
      if (null list1)
      then list2
      else if (null list2)
           then list1
           else if p (hd list1) (hd list2)
                then (hd list1) . (merge (tl list1) list2)
                else (hd list2) . (merge list1 (tl list2))
  in
  letrec pass alist = 
     if (length alist < 2)
     then alist
     else (merge (hd alist) (hd (tl alist))) . (pass (tl (tl alist)))
  in
  letrec sort alist = 
     if (null alist)
     then []
     else if (length alist = 1)
          then (hd alist)
          else sort (pass alist)
  in
  sort o (map (\x . [x]));;

% Split around a predicate.
  Example.
  kb_split (curry $= 3) [1;2;3;4;5;4;3;2;1;3];;
  ([3; 3; 3], [1; 2; 4; 5; 4; 2; 1]) : (int list # int list)
%
letrec kb_split p alist = 
   let cons = curry $.
   in
   if (null alist)
   then ([],[])
   else let (a,rst) = ((hd alist),tl alist)
        in
        (if (p a) then ((cons a)#I) else (I#(cons a)))
        (kb_split p rst);;


let is_subset s1 s2 = forall (\i. mem i s2) s1;;

letrec op_mem eq_func i  = fun [] . false |
                            (a . b) . if (eq_func i a) 
                                      then true
                                      else (op_mem eq_func i b);;

letrec op_union eq_func list1 list2 =
  if (null list1)
  then list2
  else if (null list2)
       then list1
       else let a = hd list1
            and rst = tl list1
            in
            if (op_mem eq_func a list2)
            then (op_union eq_func rst list2)
            else a . (op_union eq_func rst list2);;

let op_U eq_func set_o_sets = itlist (op_union eq_func) set_o_sets [];;

letrec iota bot top = 
   if (bot > top) 
   then []
   else bot . (iota (bot+1) top);;


letrec rev_itlist2 f list1 list2 base =
  if ((null list1) & (null list2))
  then base
  else if ((null list1) or (null list2))
       then failwith `different length lists to rev_itlist2`
       else let a = hd list1
            and b = hd list2
            and rst1 = tl list1
            and rst2 = tl list2
            in
            rev_itlist2 f rst1 rst2 (f a b base);;

letrec kb_map2 f list1 list2 =
   if (null list1) & (null list2)
   then []
   else (f (hd list1) (hd list2)) . (kb_map2 f (tl list1) (tl list2));;

letrec forall2 p list1 list2 =
   (null list1 & null list2) or
   ((p (hd list1) (hd list2)) &
    (forall2 p (tl list1) (tl list2)));;

let rotate alist = 
   letrec rot n alist = 
     if (n=0)
     then []
     else if (null alist)
          then failwith `rotate`
          else alist . (rot (n-1) ((tl alist)@[hd alist]))
   in
   rot (length alist) alist;;

% Generate all n! permutations of a list with permute. %
letrec perm alist =
   if (null alist)
   then []
   else if (null (tl alist))
        then [alist]
        else map (curry $. (hd alist)) (permute (tl alist))

and
    permute al = flat (map perm (rotate al));;


let remove_once item alist = snd (remove (curry $= item) alist);;

letrec multiset_diff m1 m2 =
   if (null m1)
   then []
   else if (null m2)
        then m1
        else let a = hd m1
             and rst = tl m1
             in
             if (mem a m2)
             then multiset_diff rst (remove_once a m2)
             else a . (multiset_diff rst m2);;

let multiset_gt order m1 m2 =
   let m1' = multiset_diff m1 m2
   and m2' = multiset_diff m2 m1
   in
   if (null m1') 
   then false
   else if (null m2') 
        then true
        else exists (\x. forall (order x) m2') m1';;


% Extends an ordering on elements of a type to a lexicographic ordering on
  lists of elements of that type.
%
letrec lex_gt order list1 list2 =
   if (null list1 & null list2)
   then false
   else let item1 = hd list1
        and rst1 = tl list1
        and item2 = hd list2
        and rst2 = tl list2
        in
        if (order item1 item2) 
        then true
        else if (item1 = item2) 
             then lex_gt order rst1 rst2
             else false;;

