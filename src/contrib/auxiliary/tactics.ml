
letrec sublist numl l =
    if null numl then []
    else (el (hd numl) l).(sublist (tl numl) l);;

let SUB_ASSUM_TAC filter:tactic (asl,g) =
    let goal = (sublist filter asl,g) in
    let prf = \[thm].TAC_PROOF((asl,g),ACCEPT_TAC thm) in
    [goal],prf;;  

let FILTER_ASSUM_TAC filter termtactic (asl,g) =
    let tmlist = sublist filter asl in
    (MAP_EVERY termtactic tmlist) (asl,g);;

let FILTER_RULE_ASSUM_TAC filter rule (asl,g) =
    letrec mklist n =(if n=0 then []
                      else (mklist (n-1))@[n]) in
    let intlist = mklist (length asl) in
    let tasl = map ASSUME asl in
    let fasl = (map (\n. if (mem n filter) then rule (el n tasl)
                        else (el n tasl)) intlist) in
    MAP_EVERY ASSUME_TAC (rev fasl) ([],g);;

let REWRITE_RULE_ASSUM_TAC filter1 filter2 =
    ASSUM_LIST(\asl.FILTER_RULE_ASSUM_TAC filter1 (REWRITE_RULE (sublist filter2 asl)));;


let EXP_UNIQUE_TAC = 
     REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV);;

let FILTER_FILTER_RULE_ASSUM_TAC filter1 filter2 rule =
    ASSUM_LIST(\asl.FILTER_RULE_ASSUM_TAC filter1 
                      (rule (sublist filter2 asl)));;

let DEFINE deftm  =
       let y,fx = dest_eq deftm in 
       let name,ty = dest_var y in 
       let thm  = EXISTS("? ^y.^deftm",fx) (REFL fx) in 
       let prf = \[th].(CHOOSE(y,thm) th) in    
          \(asl,g).
          ([deftm.asl,g],prf)
        ;;

ml_curried_infix `TIMES`;;

letrec n TIMES tac = 
       if n=0 then ALL_TAC
       if n =1 then tac
       else tac THEN ((n-1) TIMES tac);;

let FILTER_STRIP_ASSUM_TAC nl =
       let l = length nl in 
       FILTER_ASSUM_TAC (rev nl) UNDISCH_TAC THEN
       (l TIMES STRIP_TAC) ;; 

 
let GENVAR th =
    let vl = fst(strip_forall (concl th)) in
    let vln = map (genvar o type_of) vl in
    GEN_ALL (SPECL vln th);; 

% --------------------------------------------------------------------- %
% HOL_PART_MATCH and HOL_MATCH_MP now deleted from system.		%
% But added here in order to make this library file compile.		%
% Library needs to be rewritten (and documented!)	[TFM 90.04.27]	%
% --------------------------------------------------------------------- %

let HOL_PART_MATCH partfn th =
    let pth = SPEC_ALL (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth;;

let HOL_MATCH_MP impth =
     let match = HOL_PART_MATCH (fst o dest_imp) impth 
                 ? failwith `HOL_MATCH_MP` 
     in
     \th. MP (match (concl th)) th;;

% --------------------------------------------------------------------- %
% HOL_STRIP_ASSUME_TAC added too, for the same reason.			%
% Library needs to be rewritten (and documented!)	[TFM 90.04.27]	%
% --------------------------------------------------------------------- %

let HOL_STRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN];;

let HOL_STRIP_ASSUME_TAC =
    (REPEAT_TCL HOL_STRIP_THM_THEN) CHECK_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% QUESTION: 								%
%   what does the following stuff do that the new (version 1.12) 	%
%   resolution tools can't handle?  			[TFM 90.04.27]	%
% --------------------------------------------------------------------- %

letrec NEW_HOL_RESOLVE_THEN antel ttac impth : tactic =
    let answers = map GEN_ALL (mapfilter (HOL_MATCH_MP impth) antel) in
    EVERY (mapfilter ttac answers)
    THEN
    (EVERY (mapfilter (NEW_HOL_RESOLVE_THEN antel ttac) answers));;

let NEW_IMP_RES_THEN ttac impth =
 ASSUM_LIST
    (\asl. EVERY (mapfilter (NEW_HOL_RESOLVE_THEN asl ttac) (RES_CANON (GENVAR impth))));;

let NEW_RES_THEN ttac = 
    ASSUM_LIST (EVERY o (mapfilter (NEW_IMP_RES_THEN ttac)));;

let NEW_IMP_RES_TAC = NEW_IMP_RES_THEN HOL_STRIP_ASSUME_TAC
and NEW_RES_TAC     = NEW_RES_THEN     HOL_STRIP_ASSUME_TAC;;  

let FILTER_ASSUM_LIST filter asltac  =
          ASSUM_LIST  (asltac o (sublist filter));;
