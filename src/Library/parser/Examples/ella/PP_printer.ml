
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


letrec space n =

   % : (int -> string) %

   if (n < 1)
   then ``
   else ` ` ^ (space (n-1));;


let split_list (nh,nt) l =

   % : ((int # int) -> * list -> (* list # * list # * list)) %

   letrec get_head n lh lt =

      % : (int -> * list -> * list -> (* list # * list)) %

      if ((n < 0) or (n = 0))
      then (lh,lt)
      else if (null lt)
           then failwith `split_list -- insufficient elements in list`
           else get_head (n - 1) (lh @ [hd lt]) (tl lt)

   in let (h,r) = get_head nh [] l
      and nm = (length l) - (nh + nt)
      in  if (nm < 0)
          then failwith `split_list -- insufficient elements in list`
          else (h,get_head nm [] r);;


letrec replace assocl (key,new) =

   % : ((* # **) list -> (* # **) -> (* # **) list) %

   if (null assocl)
   then []
   else if (key = (fst (hd assocl)))
        then (key,new).(tl assocl)
        else (hd assocl).(replace (tl assocl) (key,new));;


letrec replacel assocl changes =

   % : ((* # **) list -> (* # **) list -> (* # **) list) %

   if (null changes)
   then assocl
   else replacel (replace assocl (hd changes)) (tl changes);;


abstype nat = int
   with Nat n = if (n < 0)
                then failwith `Nat -- number cannot be negative`
                else abs_nat n
   and  Int n = rep_nat n
   and  print_nat n = print_int (rep_nat n);;

top_print print_nat;;


let get_margin () =

   % : (void -> int) %

   let old = set_margin 0
   in  let new = set_margin old
       in  old;;

rectype print_tree = Print_node of string # print_tree list;;


let print_tree_name pt =

   % : (print_tree -> string) %

   case pt of (Print_node (s,_)) . s;;


let print_tree_children pt =

   % : (print_tree -> print_tree list) %

   case pt of (Print_node (_,l)) . l;;

type metavar_binding = Bound_name of string
                     | Bound_names of string list
                     | Bound_child of print_tree
                     | Bound_children of print_tree list;;


lettype print_binding = (string # metavar_binding) list;;


lettype print_test = (string # int) list -> print_binding -> bool;;


rectype print_patt_tree = Print_metavar of name_metavar # child_metavar list
                        | Print_loop of print_patt_tree # string #
                                           string list # print_patt_tree

and name_metavar = Wild_name
                 | Const_name of string
                 | Var_name of string

and child_metavar = Wild_child
                  | Wild_children
                  | Patt_child of print_patt_tree
                  | Var_child of string
                  | Var_children of string;;


lettype print_pattern = string # print_patt_tree # print_test;;


let lookup_metavar pbind mvar =

   % : (print_binding -> string -> metavar_binding) %

   (snd (assoc mvar pbind))
      ? failwith `lookup_metavar -- Metavariable not found in binding`;;


letrec print_merge pb1 pb2 =

   % : (print_binding -> print_binding -> print_binding) %

   if (null pb2)
   then pb1
   else ((let p = assoc (fst (hd pb2)) pb1
          in  if ((snd p) = (snd(hd pb2)))
              then (print_merge pb1 (tl pb2))
              else failwith `print_merge`)

        ??[`find`] (hd pb2).(print_merge pb1 (tl pb2))

        );;


letrec raise_binding pb =

   % : (print_binding -> print_binding) %

   if (null pb)
   then []
   else let (m,b) = hd pb
        in  (m,case b
               of (Bound_name s) . (Bound_names [s])
                | (Bound_names _) . b
                | (Bound_child pt) . (Bound_children [pt])
                | (Bound_children _) . b
            ).(raise_binding (tl pb));;


letrec raise_bindings pb1 pb2 =

   % : (print_binding -> print_binding -> print_binding) %

   if (null pb1)
   then if (null pb2)
        then []
        else failwith `raise_bindings -- inconsistent bindings`
   else if (null pb2)
        then failwith `raise_bindings -- inconsistent bindings`
        else let (m1,b1) = (hd pb1)
             and (m2,b2) = (hd pb2)
             in  if (m1 = m2)
                 then (m1,case (b1,b2)
                          of (Bound_name s1,Bound_name s2) .
                                (Bound_names (s1.[s2]))
                           | (Bound_name s1,Bound_names sl2) .
                                (Bound_names (s1.sl2))
                           | (Bound_names sl1,Bound_name s2) .
                                (Bound_names (sl1 @ [s2]))
                           | (Bound_names sl1,Bound_names sl2) .
                                (Bound_names (sl1 @ sl2))
                           | (Bound_child pt1,Bound_child pt2) .
                                (Bound_children (pt1.[pt2]))
                           | (Bound_child pt1,Bound_children ptl2) .
                                (Bound_children (pt1.ptl2))
                           | (Bound_children ptl1,Bound_child pt2) .
                                (Bound_children (ptl1 @ [pt2]))
                           | (Bound_children ptl1,Bound_children ptl2) .
                                (Bound_children (ptl1 @ ptl2))
                           | (_) . failwith `raise_bindings -- ` ^
                                               `inconsistent bindings`
                      ).(raise_bindings (tl pb1) (tl pb2))
                 else failwith `raise_bindings -- inconsistent bindings`;;


letrec print_tree_match ptpatt pt =

   % : (print_patt_tree -> print_tree -> print_binding) %

   letrec name_match m s =

      % : (name_metavar -> string -> print_binding) %

      case m
      of (Wild_name) . []
       | (Const_name s') .
            (if (s = s')
             then []
             else failwith `print_tree_match`)
       | (Var_name s') . [s',Bound_name s]

   and children_match ml ptl =

      % : (child_metavar list -> print_tree list -> print_binding) %

      letrec correspond ml' ptl' =

         % : (child_metavar list -> print_tree list ->                      %
         %                        (child_metavar # (print_tree list)) list) %

         if (null ml')
         then if (null ptl')
              then []
              else failwith `print_tree_match`
         else case (hd ml')
              of (Wild_children) .
                    ( (let (_,l,r) = split_list (0,length (tl ml')) ptl'
                       in  ((hd ml'),l).(correspond (tl ml') r))
                    ? failwith `print_tree_match`
                    )
               | (Var_children _) .
                    ( (let (_,l,r) = split_list (0,length (tl ml')) ptl'
                       in  ((hd ml'),l).(correspond (tl ml') r))
                    ? failwith `print_tree_match`
                    )
               | (_) .
                    (if (null ptl')
                     then failwith `print_tree_match`
                     else ((hd ml'),[hd ptl']).(correspond (tl ml') (tl ptl'))
                    )

      and child_match m ptl' =

         % : (child_metavar -> print_tree list -> print_binding) %

         case (m,ptl')
         of (Wild_child,_) . []
          | (Wild_children,_) . []
          | (Patt_child ptpatt',[pt']) . (print_tree_match ptpatt' pt')
          | (Var_child s,[pt']) . [s,Bound_child pt']
          | (Var_children s,ptl') . [s,Bound_children ptl']
          | (_) . failwith `print_tree_match -- ` ^
                              `inconsistent arguments to child_match`

      and merge l =

         % : ((child_metavar # (print_tree list)) list -> print_binding) %

         if (null l)
         then []
         else print_merge (child_match (fst (hd l)) (snd (hd l)))
                                                              (merge (tl l))
      in merge (correspond ml ptl)

   and loop_match ptpatt' s fixedpb subpatt pb pt' =

      % : (print_patt_tree -> string -> print_binding -> print_patt_tree ->   %
      %          print_binding -> print_tree -> (print_binding # print_tree)) %

      let traps = [`print_tree_match`;`print_merge`]
      in  (let mainpb = print_tree_match ptpatt' pt'
           in  let newpt = lookup_loop_metavar mainpb s
               in  let newpb = print_merge
                                  (print_merge mainpb
                                              (print_tree_match subpatt newpt))
                                     fixedpb
                   in  loop_match ptpatt' s fixedpb subpatt
                                     (raise_bindings pb newpb) newpt
          ) ?? traps (pb,pt')

   and lookup_loop_metavar pb s =

      % : (print_binding -> string -> print_tree) %

      case (lookup_metavar pb s)
      of (Bound_child pt') . pt'
       | (_) . failwith `print_tree_match -- attempt to loop on non-print_tree`

   in case ptpatt
      of (Print_metavar (nm,cml)) .
            (print_merge (children_match cml (print_tree_children pt))
                            (name_match nm (print_tree_name pt)))
       | (Print_loop (ptpatt',s,fixl,subpatt)) .
            (let mainpb = print_tree_match ptpatt' pt
             in  let newpt = lookup_loop_metavar mainpb s
                 in  let pb = print_merge mainpb
                                             (print_tree_match subpatt newpt)
                     in  let fixedpb = filter (\p. mem (fst p) fixl) pb
                         in  let (pb',pt') =
                                    loop_match ptpatt' s fixedpb subpatt
                                                                    pb newpt
                             in  replacel (raise_binding pb')
                                             ((s,Bound_child pt').fixedpb));;


let print_pattern_match (ppatt:print_pattern) context params pt =

   % : (print_pattern -> string -> (string # int) list -> print_tree ->     %
   %                                                         print_binding) %

   if (((fst ppatt) = ``) or ((fst ppatt) = context))
   then let result = (print_tree_match (fst (snd ppatt)) pt)
        in  (if ((snd (snd ppatt)) params result)
             then result
             else failwith `print_pattern_match`)
   else failwith `print_pattern_match`;;


letrec change_params params param_changes =

   % : ((string # int) list -> (string # int) list -> (string # int) list) %

   if (null params)
   then param_changes
   else if (can (assoc (fst (hd params))) param_changes)
        then (change_params (tl params) param_changes)
        else (hd params).(change_params (tl params) param_changes);;

rectype print_box = Null_box
                  | Atomic_box of string
                  | Compound_box of (nat # nat # nat) # nat #
                                       (print_box # int # int) #
                                          (print_box # int # int);;


let print_box_io pb =

   % : (print_box -> int) %

   case pb
   of (Null_box) . 0
    | (Atomic_box _) . 0
    | (Compound_box ((io,_,_),_)) . (Int io);;


let print_box_width pb =

   % : (print_box -> int) %

   case pb
   of (Null_box) . 0
    | (Atomic_box s) . (length (explode s))
    | (Compound_box ((_,width,_),_)) . (Int width);;


let print_box_fo pb =

   % : (print_box -> int) %

   case pb
   of (Null_box) . 0
    | (Atomic_box s) . (length (explode s))
    | (Compound_box ((_,_,fo),_)) . (Int fo);;


let print_box_height pb =

   % : (print_box -> int) %

   case pb
   of (Null_box) . 0
    | (Atomic_box _) . 1
    | (Compound_box (_,height,_)) . (Int height);;


let print_box_sizes pb =

   % : (print_box -> (int # int # int) # int) %

   case pb
   of (Null_box) . ((0,0,0),0)
    | (Atomic_box s) . (let w = length (explode s) in ((0,w,w),1))
    | (Compound_box ((io,w,fo),h,_)) . ((Int io,Int w,Int fo),Int h);;


% join_boxes does not work properly with boxes of zero height. %

let join_boxes x y pb1 pb2 =

   % : (int -> int -> print_box -> print_box -> print_box) %

   let ((io1,w1,fo1),h1) = print_box_sizes pb1
   and ((io2,w2,fo2),h2) = print_box_sizes pb2
   in  let lo = x - io2
       and ro = (w2 - io2) - (w1 - x)
       in  let io = if (lo < 0) then (io1 - lo) else io1
           and w  = if (lo < 0)
                    then if (ro < 0) then (w1 - lo) else w2
                    else if (ro < 0) then w1 else (w2 + lo)
           and fo = if (lo < 0) then fo2 else (fo2 + lo)
           and h  = h1 + h2 + y
           and x1 = 0
           and y1 = 0
           and x2 = x - io1
           and y2 = h1 + y
           in  (Compound_box
                   ((Nat io,Nat w,Nat fo),Nat h,(pb1,x1,y1),(pb2,x2,y2)));;
   

let join_H_boxes dx pb1 pb2 =

   % : (nat -> print_box -> print_box -> print_box) %

   case (pb1,pb2)
   of (Null_box,_) . pb2
    | (_,Null_box) . pb1
    | (Atomic_box s1,Atomic_box s2) .
         (Atomic_box (s1 ^ (space (Int dx)) ^ s2))
    | (_) . (join_boxes ((print_box_fo pb1) + (Int dx)) (-1) pb1 pb2);;


let join_V_boxes di dh pb1 pb2 =

   % : (int -> nat -> print_box -> print_box -> print_box) %

   case (pb1,pb2)
   of (Null_box,_) . pb2
    | (_,Null_box) . pb1
    | (_) . (join_boxes ((print_box_io pb1) + di) (Int dh) pb1 pb2);;


type print_indent = Abs of int
                  | Inc of int;;


type unbuilt_box = UB_H of (int -> int -> print_box) #
                           (nat # (int -> int -> print_box)) list
                 | UB_V of (int -> int -> print_box) #
                           ((print_indent # nat) #
                               (int -> int -> print_box)) list
                 | UB_HV of (int -> int -> print_box) #
                            ((nat # print_indent # nat) #
                                (int -> int -> print_box)) list
                 | UB_HoV of (int -> int -> print_box) #
                             ((nat # print_indent # nat) #
                                 (int -> int -> print_box)) list;;


let build_H_box m i box boxl =

   % : (int -> int -> (int -> int -> print_box) ->              %
   %       (nat # (int -> int -> print_box)) list -> print_box) %

   letrec f pb m' i boxl' =

      % : (print_box -> int -> int ->                              %
      %       (nat # (int -> int -> print_box)) list -> print_box) %

      if (null boxl')
      then pb
      else let (dx,pbfn) = hd boxl'
           in  let m'' = m' + 1 + (Int dx)
               and i' = i + ((print_box_fo pb) - (print_box_io pb)) + (Int dx)
               in  f (join_H_boxes dx pb (pbfn m'' i')) m'' i (tl boxl')

   and gaps boxl' =

      % : ((nat # (int -> int -> print_box)) list -> int) %

      itlist (\x n. (Int (fst x)) + n) boxl' 0

   in let m' = m - ((gaps boxl) + (length boxl))
      in  f (box m' i) m' i boxl;;


let build_V_box m i box boxl =

   % : (int -> int -> (int -> int -> print_box) ->                            %
   %    ((print_indent # nat) # (int -> int -> print_box)) list -> print_box) %

   letrec f pb m i i' boxl' =

      % : (print_box -> int -> int -> int ->                               %
      %      ((print_indent # nat) # (int -> int -> print_box)) list ->    %
      %                                                         print_box) %

      if (null boxl')
      then pb
      else let ((pi,dh),pbfn) = hd boxl'
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               in  f (join_V_boxes di dh pb (pbfn m (i + di)))
                                          m i (i + di) (tl boxl')

   in f (box m i) m i i boxl;;


let build_HV_box m i box boxl =

   % : (int -> int -> (int -> int -> print_box) ->                            %
   %       ((nat # print_indent # nat) # (int -> int -> print_box)) list ->   %
   %                                                               print_box) %

   letrec fH newboxl newbox m i i' boxl' =

      % : ((int # nat # print_box) list ->                                    %
      %     (int # nat # print_box) -> int -> int -> int ->                   %
      %      ((nat # print_indent # nat) # (int -> int -> print_box)) list -> %
      %                                         (int # nat # print_box) list) %

      if (null boxl')
      then newbox.newboxl
      else let ((dx,pi,dh),pbfn) = hd boxl'
           and (newdi,newdh,pb) = newbox
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               and no_break_indent =
                      (Int dx) + (print_box_fo pb) - (print_box_io pb)
               in  if ((di - (i' - i)) < no_break_indent)
                   then let newb = pbfn m (i + di)
                        in  let newhb = join_H_boxes dx pb newb
                            in  if (((print_box_width newhb) > m) or
                                    ((print_box_width newhb) -
                                             (print_box_io newhb)
                                        > (m - max [i';0])))
                                then fH (newbox.newboxl) (di,dh,newb) m i
                                                          (i + di) (tl boxl')
                                else fH newboxl (newdi,newdh,newhb) m i i'
                                                                   (tl boxl')
                   else let newhb = join_H_boxes dx pb
                                       (pbfn m (i' + no_break_indent))
                        in  fH newboxl (newdi,newdh,newhb) m i i' (tl boxl')

   in let newboxl = fH [] (0,Nat 0,box m i) m i i boxl
      in  itlist (\(di,dh,pb2) pb1. join_V_boxes di dh pb1 pb2) newboxl
                                                                  Null_box;;


let build_HoV_box m i box boxl =

   % : (int -> int -> (int -> int -> print_box) ->                            %
   %       ((nat # print_indent # nat) # (int -> int -> print_box)) list ->   %
   %                                                               print_box) %

   letrec f newboxl m i i' boxl' =

      % : ((nat # int # nat # print_box) list -> int -> int -> int ->         %
      %      ((nat # print_indent # nat) # (int -> int -> print_box)) list -> %
      %                                   (nat # int # nat # print_box) list) %

      if (null boxl')
      then newboxl
      else let ((dx,pi,dh),pbfn) = hd boxl'
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               in  f ((dx,di,dh,pbfn m (i + di)).newboxl) m i (i + di)
                                                                 (tl boxl')

   in let newb = box m i
      and newboxl = f [] m i i boxl
      in  let newhb = itlist (\(dx,di,dh,pb2) pb1. join_H_boxes dx pb1 pb2)
                                                                  newboxl newb
          in  let hw = print_box_width newhb
              and hio = print_box_io newhb
              in  if ((hw > m) or (hw - hio > (m - max [i;0])))
                  then let newvb =
                          itlist
                             (\(dx,di,dh,pb2) pb1. join_V_boxes di dh pb1 pb2)
                                                                   newboxl newb
                       in  let vw = print_box_width newvb
                           and vio = print_box_io newvb
                           in  if ((hw > vw) or (hw - hio > vw - vio))
                               then newvb
                               else newhb
                  else newhb;;


let build_print_box m i unbox =

   % : (int -> int -> unbuilt_box -> print_box) %

   case unbox
   of (UB_H (box,boxl))   . (build_H_box m i box boxl)
    | (UB_V (box,boxl))   . (build_V_box m i box boxl)
    | (UB_HV (box,boxl))  . (build_HV_box m i box boxl)
    | (UB_HoV (box,boxl)) . (build_HoV_box m i box boxl);;

lettype print_int_exp = (string # int) list -> print_binding -> int;;


rectype print_box_spec = H_box of (nat # print_object) list
                       | V_box of ((print_indent # nat) # print_object) list
                       | HV_box of ((nat # print_indent # nat) # print_object)
                                                                           list
                       | HoV_box of ((nat # print_indent # nat) # print_object)
                                                                           list

and print_format = PF_empty
                 | PF of print_box_spec
                 | PF_branch of print_test # print_format # print_format

and print_object = PO_constant of string
                 | PO_leaf of string # (string -> string)
                 | PO_subcall of (string #
                                  (print_tree list -> print_tree list))
                               # (string # print_int_exp) list
                 | PO_context_subcall of string
                                       # (string #
                                          (print_tree list -> print_tree list))
                                       # (string # print_int_exp) list
                 | PO_format of print_format
                 | PO_expand of print_box_spec;;


let PF_H = PF o H_box
and PF_V = PF o V_box
and PF_HV = PF o HV_box
and PF_HoV = PF o HoV_box;;


lettype print_rule = print_pattern # print_format;;


lettype print_rule_function = string -> (string # int) list -> print_tree ->
                                               (print_binding # print_format);;


letrec print_rule_fun prl context params pt =

   % : (print_rule list -> string -> (string # int) list -> print_tree ->    %
   %                                         (print_binding # print_format)) %

   % : (print_rule list -> print_rule_function) %

   if (null prl)
   then failwith `print_rule_fun`
   else let traps = [`print_pattern_match`;`print_tree_match`;`print_merge`]
        in  (  (print_pattern_match (fst (hd prl)) context params pt,
                                                           snd (hd prl))
            ?? traps (print_rule_fun (tl prl) context params pt)
            );;


ml_curried_infix `then_try`;;

let then_try prf1 prf2 =

   % : (print_rule_function -> print_rule_function -> print_rule_function) %

   (\context params pt. (  (prf1 context params pt)
                        ?? [`print_rule_fun`] (prf2 context params pt)
                        )) : print_rule_function;;


let raw_tree_rules =

   % : (print_rule list) %

   [(``,Print_metavar (Var_name `n`,[Var_children `cl`;Var_child `c`]),
                                                            (\x y. true)),
       (PF_HV [(Nat 0,Abs 0,Nat 0),
               PO_leaf (`n`,(\s.s));
               (Nat 0,Abs 3,Nat 0),
               PO_format
                  (PF_H [Nat 0,
                         PO_constant `(`;
                         Nat 0,
                         PO_format
                            (PF_HoV [(Nat 0,Abs 0,Nat 0),
                                     PO_expand (H_box [Nat 0,
                                                       PO_subcall
                                                          ((`cl`,(\l.l)),[]);
                                                       Nat 0,
                                                       PO_constant `,`]);
                                     (Nat 0,Abs 0,Nat 0),
                                     PO_subcall ((`c`,(\l.l)),[])]);
                         Nat 0,
                         PO_constant `)`])]);
    (``,Print_metavar (Var_name `n`,[]),(\x y. true)),
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))])
   ] : print_rule list;;


let raw_tree_rules_fun =

   % : (print_rule_function) %

   print_rule_fun raw_tree_rules;;


letrec expand_binding pb =

   % : (print_binding -> print_binding list) %

   letrec split_binding b pb' =

      % : (bool -> print_binding -> (print_binding # print_binding # bool)) %

      if (null pb')
      then ([],[],b)
      else let (pbhead,pbtail,flag) = split_binding b (tl pb')
           and (m,mb) = hd pb'
           in  let (h,t,f) =
                  case mb
                  of (Bound_name _) . ((m,mb),(m,mb),flag)
                   | (Bound_names sl) .
                        (if (null sl)
                         then ((m,mb),(m,mb),flag)
                         else ((m,Bound_name (hd sl)),
                                  (m,Bound_names (tl sl)),true))
                   | (Bound_child _) . ((m,mb),(m,mb),flag)
                   | (Bound_children ptl) .
                        (if (null ptl)
                         then ((m,mb),(m,mb),flag)
                         else ((m,Bound_child (hd ptl)),
                                  (m,Bound_children (tl ptl)),true))
               in  ((h.pbhead),(t.pbtail),f)

   in let (newpb,restpb,more_to_do) = split_binding false pb
      in  if more_to_do
          then newpb.(expand_binding restpb)
          else [];;


letrec print_tree_to_box m i prf context params pt =

   % : (int -> int -> print_rule_function -> string -> (string # int) list -> %
   %                                                 print_tree -> print_box) %

   let (pbind,pf) =
      (  (prf context params pt)
      ?? [`print_rule_fun`] (raw_tree_rules_fun context params pt)
      )
   in  print_format_fun pt m i prf context params pf pbind

and print_box_spec_fun oldpt m i prf context params pbind pbs =

   % : (print_tree -> int -> int -> print_rule_function -> string ->          %
   %     (string # int) list -> print_binding -> print_box_spec -> print_box) %

   let f pof xpol =

      % : ((print_rule_function -> string -> (string # int) list ->           %
      %      print_binding -> print_object -> (int -> int -> print_box) list) %
      %    -> (* # print_object) list ->                                      %
      %     (int -> int -> print_box) # (* # (int -> int -> print_box)) list) %

      let xpbfnl = flat (map (\(x,po). map (\pbfn. (x,pbfn)) (pof po)) xpol)
      in  if (null xpbfnl)
          then failwith `print_box_spec_fun`
          else (snd (hd xpbfnl),tl xpbfnl)

   and pof = print_object_fun oldpt prf context params pbind

   in  build_print_box m i
          (case pbs
           of (H_box xpol) . (UB_H (f pof xpol))
            | (V_box xpol) . (UB_V (f pof xpol))
            | (HV_box xpol) . (UB_HV (f pof xpol))
            | (HoV_box xpol) . (UB_HoV (f pof xpol)))

and print_format_fun oldpt m i prf context params pf pbind =

   % : (print_tree -> int -> int -> print_rule_function -> string ->         %
   %      (string # int) list -> print_format -> print_binding -> print_box) %

   case pf
   of (PF_empty) . Null_box
    | (PF pbs) . (  (print_box_spec_fun oldpt m i prf context params pbind pbs)
                 ?? [`print_box_spec_fun`] Null_box
                 )
    | (PF_branch (ptest,pf1,pf2)) .
         (if (ptest params pbind)
          then (print_format_fun oldpt m i prf context params pf1 pbind)
          else (print_format_fun oldpt m i prf context params pf2 pbind))

and print_object_fun oldpt prf context params pbind po =

   % : (print_tree -> print_rule_function -> string -> (string # int) list -> %
   %                print_binding -> print_object -> (int -> print_box) list) %

   case po
   of (PO_constant s) . [\m i. Atomic_box s]
    | (PO_leaf (metavar,string_fun)) .
         (case (lookup_metavar pbind metavar)
          of (Bound_name s) . [\m i. Atomic_box (string_fun s)]
           | (Bound_names sl) .
                (map (\s m i. Atomic_box (string_fun s)) sl)
           | (_) . failwith `print_tree_to_box -- ` ^
               `type of metavariable in pattern does n't match type in format`)
    | (PO_subcall ((metavar,list_fun),param_changes)) .
         (let ptl = case (if (metavar = ``)
                          then (Bound_child oldpt)
                          else (lookup_metavar pbind metavar))
                    of (Bound_child pt) . [pt]
                     | (Bound_children ptl) . ptl
                     | (_) . failwith (`print_tree_to_box -- ` ^
                                       `type of metavariable in pattern ` ^
                                       `does n't match type in format`)
          in  map (\pt m i. print_tree_to_box m i prf context
                               (change_params params
                                   (map (\(s,f). s,(f params pbind))
                                                         param_changes)) pt)
                               (list_fun ptl))
    | (PO_context_subcall (new_context,x)) .
         (print_object_fun oldpt prf new_context params pbind (PO_subcall x))
    | (PO_format pf) .
         [\m i. print_format_fun oldpt m i prf context params pf pbind]
    | (PO_expand x) .
         (map (\pbind' m i.
                  print_format_fun oldpt m i prf context params (PF x) pbind')
              (expand_binding pbind)
         );;

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
                 else (s1 ^ (space sep) ^ s2,x1)
        else let sep = x1 - (x2 + length (explode s2))
             in  if (sep < 0)
                 then failwith `join_strings -- overlapping strings`
                 else (s2 ^ (space sep) ^ s1,x2);;


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


letrec stringify_print_box x y pb =

   % : (int -> int -> print_box -> (string # int # int) list) %

   case pb
   of (Null_box) . []
    | (Atomic_box s) . [s,x,y]
    | (Compound_box (_,_,(pb1,x1,y1),(pb2,x2,y2))) .
         (merge_string_lists (stringify_print_box (x+x1) (y+y1) pb1)
                                (stringify_print_box (x+x2) (y+y2) pb2));;


letrec fill_in_strings t b sl =

   % : (int -> int -> (string # int # int) list -> string list) %

   if ((t = b) or (t > b))
   then if (null sl)
        then []
        else failwith `fill_in_strings -- string below specified region`
   else if (null sl)
        then (``).(fill_in_strings (t+1) b sl)
        else let (s,x,y) = hd sl
             in  if (x < 0)
                 then failwith (`fill_in_strings -- ` ^
                                   `string to the left of specified region`)
                 else if (y < t)
                      then failwith (`fill_in_strings -- ` ^
                                        `string above specified region`)
                      else if (y = t)
                           then ((space x) ^ s).
                                   (fill_in_strings (t+1) b (tl sl))
                           else (``).(fill_in_strings (t+1) b sl);;


let print_box_to_strings i pb =

   % : (int -> print_box -> string list) %

   fill_in_strings 0 (print_box_height pb) (stringify_print_box i 0 pb);;

let display_strings sl =

   % : (string list -> void) %

   do (map (\s. tty_write (s ^ `\L`)) sl);;


let output_strings file app sl =

   % : (string -> bool -> string list -> void) %

   let port = if app
              then append_openw file
              else openw file
   in  do (map (\s. write (port,(s ^ `\L`))) sl;
           close port);;


let insert_strings sl =

   % : (string list -> void) %

   letrec terminate_strings sl' =

      % : (string list -> string list) %

      if (null sl')
      then []
      else if (null (tl sl'))
           then [hd sl']
           else ((hd sl') ^ `\L`).(terminate_strings (tl sl'))

   in do (map print_string (terminate_strings sl));;


let pretty_print m i prf context params pt =

   % : (int -> int -> print_rule_function -> string -> (string # int) list -> %
   %                                                      print_tree -> void) %

   (display_strings o (print_box_to_strings i))
      (print_tree_to_box m i prf context params pt);;


let pp prf context params pt =

   % : (print_rule_function -> string -> (string # int) list -> print_tree -> %
   %                                                                    void) %

   (insert_strings o (print_box_to_strings 0))
      (print_tree_to_box (get_margin ()) 0 prf context params pt);;

ml_curried_infix `is_a_member_of`;;

let is_a_member_of metavar sl =

   % : (string -> string list -> print_test) %

   (\params pbind.
       mem (case (lookup_metavar pbind metavar)
            of (Bound_name s) . s
             | (_) . failwith (`is_a_member_of -- used on a metavar that is ` ^
                               `not bound to a name`)) sl) : print_test;;


let bound_number s =

   % : (string -> ((string # int) list -> print_binding -> int)) %

   (\params (pbind:print_binding).
       (snd (assoc s params))
          ? failwith (`bound_number -- `^s^` not in parameters`));;


let bound_name meta =

   % : (string -> ((string # int) list -> print_binding -> string)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_name -- \``^meta^`' not a metavariable`))
       of (Bound_name s) . s
        | (_) . failwith
                   (`bound_name -- metavar \``^meta^`' not bound to a name`));;


let bound_names meta =

   % : (string -> ((string # int) list -> print_binding -> string list)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_names -- \``^meta^`' not a metavariable`))
       of (Bound_names sl) . sl
        | (_) . failwith
                   (`bound_names -- metavar \``^meta^`' not bound to names`));;


let bound_child meta =

   % : (string -> ((string # int) list -> print_binding -> print_tree)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_child -- \``^meta^`' not a metavariable`))
       of (Bound_child pt) . pt
        | (_) . failwith (`bound_child -- metavar \``^meta^
                          `' not bound to a child`));;


let bound_children meta =

   % : (string -> ((string # int) list -> print_binding -> string)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith
                     (`bound_children -- \``^meta^`' not a metavariable`))
       of (Bound_children ptl) . ptl
        | (_) . failwith (`bound_children -- metavar \``^meta^
                          `' not bound to children`));;


let apply0 f =

   % : (* -> ((string # int) list -> print_binding -> *)) %

   (\(params:(string # int) list) (pbind:print_binding). f);;


let apply1 f val =

   % : ((* -> **) -> ((string # int) list -> print_binding -> *) ->   %
   %                    ((string # int) list -> print_binding -> **)) %

   (\(params:(string # int) list) (pbind:print_binding).
       f (val params pbind));;


let apply2 f val1 val2 =

   % : ((* -> ** -> **) ->                                %
   %    ((string # int) list -> print_binding -> *) ->    %
   %    ((string # int) list -> print_binding -> **) ->   %
   %       ((string # int) list -> print_binding -> ***)) %

   (\(params:(string # int) list) (pbind:print_binding).
       f (val1 params pbind) (val2 params pbind));;
