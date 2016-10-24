%   conversion package.

    david shepherd
    INMOS ltd
    31mar89
    <des@inmos.co.uk>

    do similar things with conversions as with tactics

    use: "open term surgery"

    allows user to take a term and interactively move
    through its subterms applying conversion where necessary.
    Through use of director strings these conversions can be
    recorded in an ML script to reprove the theorem.
%

%   the 3 elements of the state %

letref conv_state = []:(string#conv)list;;
letref conv_term = "T";;
letref curr_term = "T";;

%   set_conv t --- sets the term for the conversion package to use to t %

let set_conv (t:term) = conv_state := [``,ALL_CONV];conv_term:=t;curr_term:=t;;


%   build up director string from a conversion state %

letrec get_director_string = fun [] . ``
                      | ((ch,_).cs) . (get_director_string cs) ^ ch;;

%   take a director string and return the appropriate conversional to
    do that movement %

let string_to_conv s =
    letrec f c = fun [] . c
               | (x.xs) . if x=`a` then f (c o RAND_CONV) xs else
                          if x=`f` then f (c o RATOR_CONV) xs else
                          if x=`b` then f (c o ABS_CONV) xs else
                          failwith `bad director string`
    in f I (explode s);;

%   extract a subterm from a given term t using director string s %

let get_term s t =
    letrec f t = fun [] . t
               | (x.xs) . if x=`a` then f (snd (dest_comb t)) xs else
                          if x=`f` then f (fst (dest_comb t)) xs else
                          if x=`b` then f (snd (dest_abs t)) xs else
                          failwith `bad director string`
    in f t (explode s);;

%   get the conversion represented by conv_state %

let get_conv conv_st =
  letrec f = fun [] . ALL_CONV
               | ((change,conv).cl) . (string_to_conv change) (conv THENC (f cl))
  in  f (rev conv_st);;

%   get the conversional to move to current term pointed to by conv_state %

let get_pos conv_st = string_to_conv(get_director_string conv_st);;

%   show the sub term which is the current context %

let show_conv () = print_term (get_term (get_director_string conv_state) curr_term); print_newline();();;

%   apply a conversion at the current context %

let apply c = let t = ((get_pos conv_state) c) curr_term
              in let (_,rhs) = dest_eq (concl t) 
              in curr_term:=rhs;
              let (ch,co).cl = conv_state
              in conv_state := (ch,co THENC c).cl;
              ();;

%   apply all convertions so far to original term and return the theorem %

let convert () = (get_conv conv_state) conv_term;;

%   return director string of current context -- use to paste into ML script %

let whereami () = get_director_string conv_state;;

% dir_CONV s c applies conversion c at target indicated by s %

let dir_CONV s c = (string_to_conv s) c;;

% now some extra movement operators %

% move into operator of a function application %

let inrat () = 
    let t = get_term(get_director_string conv_state) curr_term
    in if (is_comb t) then conv_state := (`f`,ALL_CONV).conv_state
                      else failwith `not an application`;
    ();;

% move into operand of a function application %

let inran () = 
    let t = get_term(get_director_string conv_state) curr_term
    in if (is_comb t) then conv_state := (`a`,ALL_CONV).conv_state
                      else failwith `not an application`;
    ();;

% move into body of an abstraction %

let inabs () = 
    let t = get_term(get_director_string conv_state) curr_term
    in if (is_abs t) then conv_state := (`b`,ALL_CONV).conv_state
                      else failwith `not an application`;
    ();;

% move out one level of context %

let out () = if (null (tl conv_state)) then failwith `outermost level`
             else let (ch1,co1).(ch2,co2).cl = conv_state
                  in  conv_state := (ch2,co2 THENC ((string_to_conv ch1) co1)).cl;();;

% move into body of an abstraction or binder %

let inbody() = 
   let t = get_term (get_director_string conv_state) curr_term
   in   if (is_abs t) then conv_state := (`b`,ALL_CONV).conv_state
   else if ((is_binder o fst o dest_const o fst o dest_comb) t)
           then conv_state := (`ab`,ALL_CONV).conv_state
           else fail
   ? failwith `no body`;
   ();;

% move into left half of binary function application %

let inleft() = 
   let t = get_term (get_director_string conv_state) curr_term
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then conv_state := (`fa`,ALL_CONV).conv_state
           else failwith `not a binary function`;
   ();;

% move into right half of binary function application %

let inright() = 
   let t = get_term (get_director_string conv_state) curr_term
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then conv_state := (`a`,ALL_CONV).conv_state
           else failwith `not a binary function`;
   ();;


% Some conversions to all rewriting at targets %

let GEN_REWRITE_CONV rewrite_fun built_in_rewrites =
 let basic_net = mk_conv_net built_in_rewrites
 in
 \thl.
  let conv = rewrite_fun
             (REWRITES_CONV(merge_term_nets (mk_conv_net thl) basic_net))
  in
  \t. conv t;;

% names in lower case as REWRITE_CONV already defined %

let pure_rewrite_CONV      = GEN_REWRITE_CONV TOP_DEPTH_CONV []
and rewrite_CONV           = GEN_REWRITE_CONV TOP_DEPTH_CONV basic_rewrites
and pure_once_rewrite_CONV = GEN_REWRITE_CONV ONCE_DEPTH_CONV []
and once_rewrite_CONV      = GEN_REWRITE_CONV ONCE_DEPTH_CONV basic_rewrites;;
