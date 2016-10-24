%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        lcf-net.ml                                            %
%                                                                             %
%     DESCRIPTION:      Nets file from LCF.  Currently superceded by          %
%                       hol-nets.ml, but containing some code that might be   %
%                       usefule if backchaining is ever implemented.          %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

%
ML interface to Lisp-coded ol network functions.
These provide the ability to store data indexed by terms or formulas,
particularly for simplification.

Since "dml" cannot define objects of abstract types,
  they are defined with type "* list" instead of "* term_net" or "* form_net".
This abstract type definition introduces the correct types.
Polymorphism works because "* list" involves a type variable.
This is a hack but there seems to be no ideal solution.
%

abstype * term_net = * list
with nil_term_net = 
     abs_term_net []
and  enter_term (tm,data) tnet = 
     abs_term_net (enter_term_rep (data,tm, rep_term_net tnet))
and  lookup_term tnet tm = 
     lookup_term_rep (rep_term_net tnet, tm)
and  merge_term_nets tnet1 tnet2 =
     abs_term_net (merge_nets_rep (rep_term_net tnet1, rep_term_net tnet2))
;;


abstype * form_net = * list
with nil_form_net = 
     abs_form_net []
and  enter_form (fm,data) fnet = 
     abs_form_net (enter_form_rep (data,fm, rep_form_net fnet))
and  lookup_form fnet fm = 
     lookup_form_rep (rep_form_net fnet, fm)
and  merge_form_nets fnet1 fnet2 =
     abs_form_net (merge_nets_rep (rep_form_net fnet1, rep_form_net fnet2))
;;

% The following is for HOL --- added by MJCG %

let nil_form_net     = nil_term_net
and enter_form       = enter_term
and lookup_form      = lookup_term
and merge_form_nets  = merge_term_nets;;


%beta-conversion, paired with the appropriate pattern%
let BETA_CONV2 = "(\x:*.y:**)z", K BETA_CONV;;


%
Match a given part of "th" to a formula, instantiating "th"
The part should be free in the theorem, except for outer bound variables.
Returns the pattern used for matching, and a function to match and instantiate
the theorem.
%
let PART_FMATCH2 partfn th =
    let pth = GSPEC (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let match = form_match pat in
    pat, (\fm. INST_TY_TERM (match fm) pth);;



%
Match a given part of "th" to a term, instantiating "th"
The part should be free in the theorem, except for outer bound variables.
%
let PART_TMATCH2 partfn th =
    let pth = GSPEC (GEN_ALL th)  in
    let pat = partfn(concl pth) in  
    let match = term_match pat in
    pat, (\t. INST_TY_TERM (match t) pth);;


%
Conversion for implicative rewrites |- !x1 ... xn. A1 ==> ... ==> Am ==> t==u
Returns the pattern it matches, for building the net.
Proves the instantiated antecedents A1' ... An' using the tactic
%
let IMP_REW_CONV2 =
 set_fail_prefix `IMP_REW_CONV`
  (\irth.	%fail if thm has the wrong form%
    let t,u = 
	(dest_equiv o snd o strip_imp o snd o strip_forall o concl) irth 
    in
    let pat,matchfn = 
	PART_TMATCH2 (fst o dest_equiv o snd o strip_imp) irth 
    in
    if (can matchfn u)  then failwith `rewriting would loop`
    else
    pat,
    \(tac:tactic) tm.
    let irth' = matchfn tm in
    let antel,() = strip_imp (concl irth') in
    let ANTEL = map (\w. TAC_PROOF ( ([],w), tac )) antel in
    LIST_MP ANTEL irth');;



let IMP_REW_FCONV2 =
 set_fail_prefix `IMP_REW_FCONV2`
  (\irth.	%fail if thm has the wrong form%
    let b,c = 
	(dest_iff o snd o strip_imp o snd o strip_forall o concl) irth 
    in
    let pat, matchfn = PART_FMATCH2 (fst o dest_iff o snd o strip_imp) irth 
    in
    if can matchfn c then failwith `rewriting would loop`
    else
    pat,
    \(tac:tactic) fm.
    let irth' = matchfn fm in
    let antel,() = strip_imp (concl irth') in
    let thl = map (\w. TAC_PROOF ( ([],w), tac )) antel in
    LIST_MP thl irth');;



%Use the theorem for term rewriting or formula rewriting if possible.
Enter it into existing term/formula nets.
%
let use_rewrite_lemma th (cnet,fcnet) =
    let can_thl = IMP_CANON th in
    (rev_itlist enter_term
       (mapfilter IMP_REW_CONV2 can_thl) 
       cnet,
     rev_itlist enter_form
       (mapfilter (IMP_REW_FCONV2 o FCONV_CANON) can_thl) 
       fcnet);;


% map_ap x [f1;...;fn]   --->   [f1 x;...;fn x] %
let map_ap x = map (\f. f x);;



%Rather ad-hoc functions for applying conversions stored in nets%
let FIRST_NET_CONV cnet tac tm =
    FIRST_CONV (map_ap tac (lookup_term cnet tm)) tm
and FIRST_NET_FCONV fcnet tac fm =
    FIRST_FCONV (map_ap tac (lookup_form fcnet fm)) fm;;


%Main conversion for rewriting formulas.  Calls itself recursively to
solve implicative rewrites and to introduce local assumptions.
%
letrec MAIN_REWRITE_FCONV (cnet,fcnet) =
  letrec tac g = FCONV_TAC fconv g
  and fconv fm =
    LOCAL_BASIC_FCONV 
       (FIRST_NET_CONV cnet tac)
       (FIRST_NET_FCONV fcnet tac)
       (\th. MAIN_REWRITE_FCONV (use_rewrite_lemma th (cnet,fcnet)))
       fm
  in fconv;;



%Build discrimination nets containing the rewriting theorems%
let build_nets thms =
   rev_itlist use_rewrite_lemma thms 
      (enter_term BETA_CONV2 nil_term_net,
       nil_form_net);;



%rewrite a formula using a list of theorems%
let rewrite_form = MAIN_REWRITE_FCONV o build_nets;;


%rewrite a term using a list of theorems%
let rewrite_term thms =
    let cnet,fcnet = build_nets thms in
    let tac = FCONV_TAC (MAIN_REWRITE_FCONV (cnet,fcnet)) in
    TOP_DEPTH_CONV (FIRST_NET_CONV cnet tac);;

%Added for HOL: "t=t"   -->   |- (t=t) = T %

let REFL_CONV t =
 (let t1,t2 = dest_eq t
  in
  if t1=t2 then EQT_INTRO(REFL t1) else fail
 ) ? REFL t;;

let hol_rewrite_term ths = rewrite_term ths THENC REFL_CONV;;

%Added for HOL%
let CONV_TAC conv :tactic (asl,w) =
 let th = conv w
 in
 let left,right = dest_eq(concl th)
 in
 if right="T" 
 then ([], \[]. EQ_MP (SYM th) TRUTH)
 else ([asl,right], \[th']. EQ_MP (SYM th) th');;

%Rewrite a goal%
let REWRITE_TAC = CONV_TAC o hol_rewrite_term;;  %Changed for HOL%


%Rewrite a goal with the help of its assumptions%
let ASM_REWRITE_TAC thl =
    ASSUM_LIST (\asl. REWRITE_TAC (asl @ thl));;

%Added for HOL%
let CONV_RULE conv th = EQ_MP (conv(concl th)) th;;

%Rewrite a theorem%
let REWRITE_RULE = CONV_RULE o hol_rewrite_term;; %Changed for HOL%


%Rewrite a theorem with the help of its assumptions%
let ASM_REWRITE_RULE thl th =
    REWRITE_RULE ((map ASSUME (hyp th)) @thl) th;;



%Reverse the direction of a term/formula rewrite%
let REV_REWRITE th0 =
    (let [th] = IMP_CANON th0 in
     let (),conseq = strip_imp (concl th) in
     if is_equiv conseq then ONCE_DEPTH_CHAIN SYM th
     else if is_iff conseq then ONCE_DEPTH_CHAIN FSYM th
     else fail)
    ? failwith `REV_REWRITE`;;


%return the arg if f accepts it, else pass on f's failure%
let good_arg f x = (f x; x);;


%return a pair of lists: all clauses used as term/formula rewrites.
This should give the user some idea of what REWRITE_TAC is doing.
%
let used_rewrites thl =
    let can_thl = flat (map IMP_CANON thl) in    
     (mapfilter (good_arg IMP_REW_CONV2) can_thl,
      mapfilter (good_arg IMP_REW_FCONV2) (mapfilter FCONV_CANON can_thl));;


%include the assumptions in the list of potential rewrites%
let asm_used_rewrites thl =
    ASSUM_LIST (\asl. K (used_rewrites (asl @ thl)));;

