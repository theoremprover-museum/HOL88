%   conversion package.

    david shepherd
    INMOS ltd
    27sep89
    <des@inmos.co.uk>

    do similar things with conversions as with tactics

    use: "open term surgery"

    allows user to take a term and interactively move
    through its subterms applying conversion where necessary.
    Through use of director strings these conversions can be
    recorded in an ML script to reprove the theorem.

    also at the end some dubious "interactive-only" tactics
    supplied complete with suitable warning.
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
                          if x=`l` then f (c o RATOR_CONV o RAND_CONV) xs else
                          if x=`r` then f (c o RAND_CONV) xs else
                          if x=`q` then f (c o RAND_CONV o ABS_CONV) xs else
                          failwith `bad director string`
    in f I (explode s);;

%   extract a subterm from a given term t using director string s %

let get_term s t =
    letrec f t = fun [] . t
               | (x.xs) . if x=`a` then f (snd (dest_comb t)) xs else
                          if x=`f` then f (fst (dest_comb t)) xs else
                          if x=`b` then f (snd (dest_abs t)) xs else
                          if x=`l` then f ((snd o dest_comb o fst o dest_comb) t) xs else
                          if x=`r` then f (snd (dest_comb t)) xs else
                          if x=`q` then f ((snd o dest_abs o snd o dest_comb) t) xs else
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

let dir_CONV_RULE s c = CONV_RULE(dir_CONV s c);;

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
           then conv_state := (`q`,ALL_CONV).conv_state
           else fail
   ? failwith `no body`;
   ();;

% move into left half of binary function application %

let inleft() = 
   let t = get_term (get_director_string conv_state) curr_term
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then conv_state := (`l`,ALL_CONV).conv_state
           else failwith `not a binary function`;
   ();;

% move into right half of binary function application %

let inright() = 
   let t = get_term (get_director_string conv_state) curr_term
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then conv_state := (`r`,ALL_CONV).conv_state
           else failwith `not a binary function`;
   ();;


% Some conversions to all rewriting at targets %

let REWRITES_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm;;

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

% Sub_goal package interface %

%   SET_CONVERT_TAC

    basically an ALL_TAC that side effects by setting up conversion goal
%

let (SET_CONVERT_TAC:tactic) g = let x = set_conv (snd g) in (ALL_TAC g);;


%   CONVERT_TAC

    do apply the conversion that you've just built up
%

let CONVERT_TAC g = CONV_TAC(get_conv conv_state)g;;

%   DIR_CONV_TAC

    apply a conversion at a specified point
%

let dir_CONV_TAC s c = CONV_TAC(dir_CONV s c);;

% 8sep89 [DES] extra "tactics" for limiting rewriting etc.	%
% first another referrence variable to point at a term		%
%								%
%		***** WARNING *****				%
%								%
% These tactics can *ONLY* be used when sketching out the proof %
% of a goal as when combined with tacticals all the side	%
% effects on at_tac_position happen as the parser evaluates the %
% tactic. They should be used to find the proof and then the	%
% appropriate conversions should be substituted along with the	%
% use of dir_CONV_TAC.						%
%								%
% Because of this these tactics should be used with care and	%
% any proof script tested immediately to check you've done the	%
% correct changes from at_tactics to conversions.		%
%								%
% Notwithstanding the comments above these tactics are useful	%
% when manipulating large terms -- in the first example I used	%
% them on by restricting the trees that were rewritten I cut	%
% the execution time of a proof from 40mins to 15mins !		%

letref at_tac_position = ``;;

let inrat_tac :tactic = \g.
    let t = get_term at_tac_position (snd g)
    in if (is_comb t) then at_tac_position := at_tac_position ^ `f`
                      else failwith `not an application`;
    ALL_TAC g;;

% move into operand of a function application %

let inran_tac :tactic = \g. 
    let t = get_term at_tac_position (snd g)
    in if (is_comb t) then at_tac_position := at_tac_position ^ `a`
                      else failwith `not an application`;
    ALL_TAC g;;

% move into body of an abstraction %

let inabs_tac :tactic = \g. 
    let t = get_term at_tac_position (snd g)
    in if (is_abs t) then at_tac_position := at_tac_position ^ `b`
                      else failwith `not an application`;
    ALL_TAC g;;

% move out one level of context %

let out_tac :tactic = \g. if (at_tac_position=``) then failwith `outermost level`
             else 
    letrec f xs = if (tl xs = []) then [] else (hd xs).(f (tl xs))
    in  at_tac_position := implode (f (explode at_tac_position));
    ALL_TAC g;;

% move into body of an abstraction or binder %

let inbody_tac :tactic = \g. 
   let t = get_term  at_tac_position (snd g)
   in   if (is_abs t) then at_tac_position := at_tac_position ^ `b`
   else if ((is_binder o fst o dest_const o fst o dest_comb) t)
           then at_tac_position := at_tac_position ^ `ab`
           else fail
   ? failwith `no body`;
   ALL_TAC g;;

% move into left half of binary function application %

let inleft_tac :tactic = \g. 
   let t = get_term  at_tac_position (snd g)
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then at_tac_position := at_tac_position ^ `fa`
           else failwith `not a binary function`;
   ALL_TAC g;;

% move into right half of binary function application %

let inright_tac :tactic = \g. 
   let t = get_term  at_tac_position (snd g)
   in   if (is_comb t) & ((is_comb o fst o dest_comb) t) 
           then at_tac_position := at_tac_position ^ `a`
           else failwith `not a binary function`;
   ALL_TAC g;;


% show_tac_pos: show current position %

let show_tac_pos () =
    let (asl,g) = top_goal()
    in  print_term (get_term at_tac_position g);
  print_newline();
  at_tac_position;;

let set_tac_pos s :tactic = \g.
    at_tac_position := s;
    ALL_TAC g;;

let reset_tac_pos = set_tac_pos``;;

let conv_at_tac c = dir_CONV_TAC at_tac_position c;;

let rewrite_at_tac = (conv_at_tac o rewrite_CONV);;
let once_rewrite_at_tac = (conv_at_tac o once_rewrite_CONV);;
let pure_rewrite_at_tac = (conv_at_tac o pure_rewrite_CONV);;
let pure_once_rewrite_at_tac = (conv_at_tac o pure_once_rewrite_CONV);;


