% order.ml

  Term orderings. The definitive reference is Dershowitz in
  the Journal of Symbolic Computation 1987, one of the great 
  papers in the field.
%

letrec is_subterm_of tm1 tm2 =
   if (is_comb tm2)
   then let tm2_args = snd (strip_comb tm2)
        in
        exists (\x. (x=tm1) or (is_subterm_of tm1 x)) tm2_args
   else false;;


let perm_cong t1 t2 =
   if (is_comb t1 & is_comb t2)
   then let (c1,args1) = strip_comb t1
        and (c2,args2) = strip_comb t2
        in
        (c1=c2) &
        (exists (\x. x = args2) (permute args1))
   else false;;



% rpo is true when t1 > t2 under recursive path ordering of Dershowitz.
  Variables cannot be included in the base ordering, which is a partial
  ordering.
%
letrec rpo po tm1 tm2 =
   if (is_var tm1)
   then false
   else if (is_const tm1)
        then if (is_const tm2)
             then po tm1 tm2
             else
             if (is_var tm2) 
             then false
             else
             if (is_comb tm2)
             then let (c2,args2) = strip_comb tm2
                  in
                  if (po tm1 c2)
                  then forall (rpo po tm1) args2
                  else false
             else failwith `rpo: encountered abs`
        else if (is_comb tm1)
             then let (c1,args1) = strip_comb tm1
                  in
                  if (is_const tm2)
                  then if (po c1 tm2)
                       then true
                       else is_subterm_of tm2 tm1
                  else
                  if (is_var tm2)
                  then is_subterm_of tm2 tm1
                  else
                  if (is_comb tm2)
                  then let (c2,args2) = strip_comb tm2
                       in
                       (exists (\x. (rpo po x tm2) or
                                    (x = tm2) or
                                    (perm_cong x tm2))
                               args1)
                       or
                       (if (c1 = c2)
                        then (multiset_gt (rpo po) args1 args2)
                        else if (po c1 c2) 
                             then (forall (rpo po tm1) args2)
                             else false)
                  else failwith `rpo: encountered abs`
             else  failwith `rpo: encountered abs`;;


% lrpo is true when t1 > t2 under lexicographic version of recursive path
  ordering. Base ordering is assumed to be a partial order.
%
letrec lrpo po tm1 tm2 =
  if (is_var tm1)
  then false
  else if (is_const tm1)
       then if (is_const tm2)
            then po tm1 tm2
            else if (is_var tm2)
                 then false
                 else if (is_comb tm2)
                      then let (c2,args2) = strip_comb tm2
                           in
                           if (po tm1 c2)
                           then forall (lrpo po tm1) args2
                           else false
                      else failwith `lrpo: encountered abs`
       else if (is_comb tm1)
            then let (c1,args1) = strip_comb tm1
                 in
                 if (is_const tm2)
                 then if (po c1 tm2)
                      then true
                      else is_subterm_of tm2 tm1
                 else if (is_var tm2)
                      then is_subterm_of tm2 tm1
                      else if (is_comb tm2)
                           then let (c2,args2) = strip_comb tm2
                                in
                                (exists (\x. (lrpo po x tm2) or
                                             (x = tm2))
                                        args1)
                                or
                                (if (c1 = c2)
                                 then ((lex_gt (lrpo po) args1 args2) &
                                       (forall (\x. lrpo po tm1 x)
                                               (tl args2)))
                                 else if (po c1 c2)
                                      then (forall (lrpo po tm1) args2)
                                      else false)
                           else failwith `lrpo: encountered abs`
            else failwith `lrpo: encountered abs`;;

% The recursive path ordering with status
%
letrec rpos status po tm1 tm2 =
  if (is_var tm1)
  then false
  else if (is_const tm1)
       then if (is_const tm2)
            then po tm1 tm2
            else if (is_var tm2)
                 then false
                 else if (is_comb tm2)
                      then let (c2,args2) = strip_comb tm2
                           in
                           (po tm1 c2) & forall (rpos status po tm1) args2
                      else failwith `rpos: encountered abs`
       else if (is_comb tm1)
            then let (c1,args1) = strip_comb tm1
                 in
                 if (is_const tm2)
                 then ((po c1 tm2) or (is_subterm_of tm2 tm1))
                 else if (is_var tm2)
                      then is_subterm_of tm2 tm1
                      else if (is_comb tm2)
                           then let (c2,args2) = strip_comb tm2
                                in
                                ((exists (\x. (rpos status po x tm2) or
                                              (x = tm2) or
                                              (if (status c1)
                                               then false 
                                               else perm_cong x tm2))
                                         args1)
                                or
                                (if (c1 = c2) 
                                 then if (status c1)
                                      then ((lex_gt (rpos status po) args1 args2) &
                                            (forall (\x. rpos status po tm1 x) 
                                                    (tl args2)))
                                      else multiset_gt (rpos status po) args1 args2
                                 else (po c1 c2) & (forall (rpos status po tm1) args2)))
                           else failwith `lrpo: encountered abs`
            else failwith `lrpo: encountered abs`;;


