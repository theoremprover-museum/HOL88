%****************************************************************************%
% FILE          : sup-inf.ml                                                 %
% DESCRIPTION   : SUP-INF method for deciding a subset of Presburger         %
%                 arithmetic (R.E.Shostak, JACM Vol.24 No.4 Pages 529-543)   %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%============================================================================%
% SUP-INF algorithm                                                          %
%============================================================================%

%----------------------------------------------------------------------------%
% Datatype for representing the bounds of a normalised expression            %
%----------------------------------------------------------------------------%

rectype bound = Bound of rat # (string # rat) list
              | Max_bound of bound list
              | Min_bound of bound list
              | Pos_inf
              | Neg_inf;;

%----------------------------------------------------------------------------%
% Datatype for representing the bounds of an non-normalised expression       %
%----------------------------------------------------------------------------%

rectype internal_bound = Ibound of bound
                       | Mult_ibound of rat # internal_bound
                       | Plus_ibound of internal_bound # internal_bound
                       | Max_ibound of internal_bound list
                       | Min_ibound of internal_bound list;;

%----------------------------------------------------------------------------%
% solve_ineqs :                                                              %
%    (int # (string # int) list) list ->                                     %
%    string ->                                                               %
%    ((rat # (string # rat) list) list # (rat # (string # rat) list) list)   %
%----------------------------------------------------------------------------%

letrec solve_ineqs ineqs var =
   if (null ineqs)
   then ([],[])
   else let (const,bind) = hd ineqs
        and (restl,restr) = solve_ineqs (tl ineqs) var
        in  (let i = snd (assoc var bind)
             in  let const' = Rat (const,(-i))
                 and bind' = map (I # (\n. Rat (n,(-i))))
                                (filter (\(name,_) . not (name = var)) bind)
             in  if (i < 0)
                 then (((const',bind').restl),restr)
                 else (restl,((const',bind').restr)))
          ? (restl,restr);;

%----------------------------------------------------------------------------%
% UPPER : (int # (string # int) list) list -> string -> bound                %
%----------------------------------------------------------------------------%

let UPPER s x =
   let uppers = fst (solve_ineqs s x)
   in  if (null uppers)
       then Pos_inf
       else if (null (tl uppers))
            then Bound (hd uppers)
            else Min_bound (map Bound uppers);;

%----------------------------------------------------------------------------%
% LOWER : (int # (string # int) list) list -> string -> bound                %
%----------------------------------------------------------------------------%

let LOWER s x =
   let lowers = snd (solve_ineqs s x)
   in  if (null lowers)
       then Neg_inf
       else if (null (tl lowers))
            then Bound (hd lowers)
            else Max_bound (map Bound lowers);;

%----------------------------------------------------------------------------%
% SIMP_mult : rat -> bound -> bound                                          %
%----------------------------------------------------------------------------%

letrec SIMP_mult r b =
   case b
   of (Bound (const,bind)) .
         (Bound (rat_mult r const,map (I # (rat_mult r)) bind))
    | (Max_bound bl) .
         (if ((Numerator r) < 0)
          then (Min_bound (map (SIMP_mult r) bl))
          else (Max_bound (map (SIMP_mult r) bl)))
    | (Min_bound bl) .
         (if ((Numerator r) < 0)
          then (Max_bound (map (SIMP_mult r) bl))
          else (Min_bound (map (SIMP_mult r) bl)))
    | Pos_inf . (if ((Numerator r) < 0) then Neg_inf else Pos_inf)
    | Neg_inf . (if ((Numerator r) < 0) then Pos_inf else Neg_inf);;

%----------------------------------------------------------------------------%
% sum_bindings :                                                             %
%    (string # rat) list -> (string # rat) list -> (string # rat) list       %
%----------------------------------------------------------------------------%

letrec sum_bindings bind1 bind2 =
   if (null bind1) then bind2
   if (null bind2) then bind1
   else (let (name1,coeff1) = hd bind1
         and (name2,coeff2) = hd bind2
         in  if (name1 = name2) then
                (let coeff = rat_plus coeff1 coeff2
                 and bind = sum_bindings (tl bind1) (tl bind2)
                 in  if ((Numerator coeff) = 0)
                     then bind
                     else (name1,coeff).bind)
             if (string_less name1 name2) then
                (name1,coeff1).(sum_bindings (tl bind1) bind2)
             else (name2,coeff2).(sum_bindings bind1 (tl bind2)));;

%----------------------------------------------------------------------------%
% SIMP_plus : bound -> bound -> bound                                        %
%----------------------------------------------------------------------------%

letrec SIMP_plus b1 b2 =
   (case (b1,b2)
    of (Bound (const1,bind1),Bound (const2,bind2)) .
          (Bound (rat_plus const1 const2,sum_bindings bind1 bind2))
     | (Bound _,Max_bound bl) . (Max_bound (map (SIMP_plus b1) bl))
     | (Bound _,Min_bound bl) . (Min_bound (map (SIMP_plus b1) bl))
     | (Bound _,Pos_inf) . Pos_inf
     | (Bound _,Neg_inf) . Neg_inf
     | (Max_bound bl,_) . (Max_bound (map (\b. SIMP_plus b b2) bl))
     | (Min_bound bl,_) . (Min_bound (map (\b. SIMP_plus b b2) bl))
     | (Pos_inf,Pos_inf) . Pos_inf
     | (Pos_inf,Neg_inf) . fail
     | (Pos_inf,_) . (SIMP_plus b2 b1)
     | (Neg_inf,Neg_inf) . Neg_inf
     | (Neg_inf,Pos_inf) . fail
     | (Neg_inf,_) . (SIMP_plus b2 b1)
   ) ? failwith `SIMP_plus`;;

%----------------------------------------------------------------------------%
% SIMP : internal_bound -> bound                                             %
%----------------------------------------------------------------------------%

letrec SIMP ib =
   case ib
   of (Ibound b) . b
    | (Mult_ibound (r,ib')) . (SIMP_mult r (SIMP ib'))
    | (Plus_ibound (ib1,ib2)) . (SIMP_plus (SIMP ib1) (SIMP ib2))
    | (Max_ibound ibl) . (Max_bound (map SIMP ibl))
    | (Min_ibound ibl) . (Min_bound (map SIMP ibl));;

%----------------------------------------------------------------------------%
% SUPP : (string # bound) -> bound                                           %
% INFF : (string # bound) -> bound                                           %
%----------------------------------------------------------------------------%

letrec SUPP (x,y) =
   case y
   of (Bound (_,[])) . y
    | Pos_inf . y
    | Neg_inf . y
    | (Min_bound bl) . (Min_bound (map (\y. SUPP (x,y)) bl))
    | (Bound (const,bind)) .
         (let b = snd (assoc x bind) ? rat_zero
          and bind' = filter (\p. not (fst p = x)) bind
          in  if ((null bind') & (const = rat_zero) & (b = rat_one))
              then Pos_inf
              else let b' = rat_minus rat_one b
                   in  if (Numerator b' < 0) then Pos_inf
                       if (Numerator b' > 0) then
                          (Bound (rat_div const b',
                                  map (I # (\r. rat_div r b')) bind'))
                       else if (not (null bind')) then Pos_inf
                            if (Numerator const < 0) then Neg_inf
                            else Pos_inf)
    | (_) . failwith `SUPP`;;

letrec INFF (x,y) =
   case y
   of (Bound (_,[])) . y
    | Pos_inf . y
    | Neg_inf . y
    | (Max_bound bl) . (Max_bound (map (\y. INFF (x,y)) bl))
    | (Bound (const,bind)) .
         (let b = snd (assoc x bind) ? rat_zero
          and bind' = filter (\p. not (fst p = x)) bind
          in  if ((null bind') & (const = rat_zero) & (b = rat_one))
              then Neg_inf
              else let b' = rat_minus rat_one b
                   in  if (Numerator b' < 0) then Neg_inf
                       if (Numerator b' > 0) then
                          (Bound (rat_div const b',
                                  map (I # (\r. rat_div r b')) bind'))
                       else if (not (null bind')) then Neg_inf
                            if (Numerator const > 0) then Pos_inf
                            else Neg_inf)
    | (_) . failwith `INFF`;;

%----------------------------------------------------------------------------%
% occurs_in_bound : string -> bound -> bool                                  %
%----------------------------------------------------------------------------%

letrec occurs_in_bound v b =
   case b
   of (Bound (_,bind)) . (mem v (map fst bind))
    | (Max_bound bl) .
         (itlist (\x y. x or y) (map (occurs_in_bound v) bl) false)
    | (Min_bound bl) .
         (itlist (\x y. x or y) (map (occurs_in_bound v) bl) false)
    | (_) . false;;

%----------------------------------------------------------------------------%
% occurs_in_ibound : string -> internal_bound -> bool                        %
%----------------------------------------------------------------------------%

letrec occurs_in_ibound v ib =
   case ib
   of (Ibound b) . (occurs_in_bound v b)
    | (Mult_ibound (_,ib')) . (occurs_in_ibound v ib')
    | (Plus_ibound (ib1,ib2)) .
         ((occurs_in_ibound v ib1) or (occurs_in_ibound v ib2))
    | (Max_ibound ibl) .
         (itlist (\x y. x or y) (map (occurs_in_ibound v) ibl) false)
    | (Min_ibound ibl) .
         (itlist (\x y. x or y) (map (occurs_in_ibound v) ibl) false);;

%----------------------------------------------------------------------------%
% SUP : (int # (string # int) list) list ->                                  %
%       (bound # (string list)) ->                                           %
%       internal_bound                                                       %
% INF : (int # (string # int) list) list ->                                  %
%       (bound # (string list)) ->                                           %
%       internal_bound                                                       %
%----------------------------------------------------------------------------%

letrec SUP s (J,H) =
   case J
   of (Bound (_,[])) . (Ibound J)
    | Pos_inf . (Ibound J)
    | Neg_inf . (Ibound J)
    | (Min_bound bl) . (Min_ibound (map (\j. SUP s (j,H)) bl))
    | (Bound (const,bind)) .
         (let (rv.bind') = bind
          in  let (v,r) = rv
          in  if ((const = rat_zero) & (null bind'))
              then (if (r = rat_one) then
                       (if (mem v H)
                        then Ibound J
                        else let Q = UPPER s v
                             in  let Z = SUP s (Q,union H [v])
                             in  Ibound (SUPP (v,SIMP Z)))
                    if (Numerator r < 0)
                    then (Mult_ibound
                           (r,INF s (Bound (rat_zero,[v,rat_one]),H)))
                    else (Mult_ibound
                           (r,SUP s (Bound (rat_zero,[v,rat_one]),H)))
                   )
              else let B' = SUP s (Bound (const,bind'),union H [v])
                   and rvb = Bound (rat_zero,[rv])
                   in  if (occurs_in_ibound v B')
                       then let J' = SIMP (Plus_ibound (Ibound rvb,B'))
                            in  SUP s (J',H)
                       else Plus_ibound (SUP s (rvb,H),B'))
    | (_) . failwith `SUP`

and INF s (J,H) =
   case J
   of (Bound (_,[])) . (Ibound J)
    | Pos_inf . (Ibound J)
    | Neg_inf . (Ibound J)
    | (Max_bound bl) . (Max_ibound (map (\j. INF s (j,H)) bl))
    | (Bound (const,bind)) .
         (let (rv.bind') = bind
          in  let (v,r) = rv
          in  if ((const = rat_zero) & (null bind'))
              then (if (r = rat_one) then
                       (if (mem v H)
                        then Ibound J
                        else let Q = LOWER s v
                             in  let Z = INF s (Q,union H [v])
                             in  Ibound (INFF (v,SIMP Z)))
                    if (Numerator r < 0)
                    then (Mult_ibound
                           (r,SUP s (Bound (rat_zero,[v,rat_one]),H)))
                    else (Mult_ibound
                           (r,INF s (Bound (rat_zero,[v,rat_one]),H)))
                   )
              else let B' = INF s (Bound (const,bind'),union H [v])
                   and rvb = Bound (rat_zero,[rv])
                   in  if (occurs_in_ibound v B')
                       then let J' = SIMP (Plus_ibound (Ibound rvb,B'))
                            in  INF s (J',H)
                       else Plus_ibound (INF s (rvb,H),B'))
    | (_) . failwith `INF`;;

%----------------------------------------------------------------------------%
% eval_max_bound : bound list -> bound                                       %
%----------------------------------------------------------------------------%

letrec eval_max_bound bl =
   if (null bl) then failwith `eval_max_bound`
   if (null (tl bl)) then (hd bl)
   else let b = hd bl
        and max = eval_max_bound (tl bl)
        in  case (b,max)
            of (Pos_inf,_) . Pos_inf
             | (_,Pos_inf) . Pos_inf
             | (Neg_inf,_) . max
             | (_,Neg_inf) . b
             | (Bound (r1,[]),Bound (r2,[])) .
                  (if (Numerator (rat_minus r1 r2) < 0) then max else b)
             | (_) . failwith `eval_max_bound`;;

%----------------------------------------------------------------------------%
% eval_min_bound : bound list -> bound                                       %
%----------------------------------------------------------------------------%

letrec eval_min_bound bl =
   if (null bl) then failwith `eval_min_bound`
   if (null (tl bl)) then (hd bl)
   else let b = hd bl
        and min = eval_min_bound (tl bl)
        in  case (b,min)
            of (Pos_inf,_) . min
             | (_,Pos_inf) . b
             | (_,Neg_inf) . Neg_inf
             | (Neg_inf,_) . Neg_inf
             | (Bound (r1,[]),Bound (r2,[])) .
                  (if (Numerator (rat_minus r1 r2) < 0) then b else min)
             | (_) . failwith `eval_min_bound`;;

%----------------------------------------------------------------------------%
% eval_bound : bound -> bound                                                %
%----------------------------------------------------------------------------%

letrec eval_bound b =
   case b
   of (Bound (_,[])) . b
    | (Max_bound bl) . (eval_max_bound (map eval_bound bl))
    | (Min_bound bl) . (eval_min_bound (map eval_bound bl))
    | Pos_inf . b
    | Neg_inf . b;;

%----------------------------------------------------------------------------%
% SUP_INF :                                                                  %
%    (int # (string # int) list) list -> (string # bound # bound) list       %
%----------------------------------------------------------------------------%

let SUP_INF set =
   let vars_of_coeffs coeffsl = setify (flat (map ((map fst) o snd) coeffsl))
   in
   let vars = vars_of_coeffs set
   and make_bound v = Bound (rat_zero,[v,rat_one])
   and eval = eval_bound o SIMP
   in  map (\v. let b = make_bound v
                in  (v,eval (INF set (b,[])),eval (SUP set (b,[])))) vars;;

