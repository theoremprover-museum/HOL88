%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        tacticals.ml                                          %
%                                                                             %
%     DESCRIPTION:      Monomorphic tacticals                                 %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml  %
%                       hol-rule.ml, hol-drule.ml, drul.ml                    %
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

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% Also load hol-rule.ml, hol-drule.ml, drul.ml				%
% --------------------------------------------------------------------- %

if compiling then  
   (loadf `ml/hol-in-out`; 
    loadf `ml/hol-rule`; 
    loadf `ml/hol-drule`;
    loadf `ml/drul`);;

% --------------------------------------------------------------------- %
% ML type abbreviations.						%
% --------------------------------------------------------------------- %

lettype proof = thm list -> thm  ;;

lettype goal = term list # term;;

lettype tactic = goal -> ((goal list) # proof);;

% --------------------------------------------------------------------- %
% TAC_PROOF (g,tac) uses tac to prove the goal g			%
% --------------------------------------------------------------------- %

let TAC_PROOF : (goal # tactic) -> thm =
    set_fail_prefix `TAC_PROOF`
       (\(g,tac). 
	   let gl,p = tac g in
	   if null gl then p[]
	   else failwith `unsolved goals`);;

% --------------------------------------------------------------------- %
% prove (t,tac) : prove the boolean term t using the tactic tac.	%
% [MJCG 17/1/89 for HOL88]						%
% --------------------------------------------------------------------- %

let prove(t,tac) = TAC_PROOF(([],t), tac);;

% --------------------------------------------------------------------- %
% Provide a function (tactic) with the current assumption list		%
% --------------------------------------------------------------------- %

let (ASSUM_LIST: (thm list -> tactic) -> tactic) 
  	aslfun (asl,w) =
    aslfun (map ASSUME asl) (asl,w);;

% --------------------------------------------------------------------- %
% Pop the first assumption and give it to a function (tactic) 		%
% --------------------------------------------------------------------- %

let POP_ASSUM (thfun:thm->tactic) ((as.asl),w) = thfun (ASSUME as) (asl,w);;

% --------------------------------------------------------------------- %
% Pop off the entire assumption list and give it to a function (tactic) %
% --------------------------------------------------------------------- %

let POP_ASSUM_LIST (asltac : thm list -> tactic) (asl,w) =
    asltac (map ASSUME asl) ([],w);;

% --------------------------------------------------------------------- %
% The tacticals THEN and THENL.						%
% --------------------------------------------------------------------- %

ml_curried_infix `THEN` ;;
ml_curried_infix `THENL` ;;

begin_section THEN_THENL;;

letrec mapshape nl fl l =  
    if null nl then []
    else 
       (let m,l = chop_list (hd nl) l in 
        (hd fl)m . mapshape(tl nl)(tl fl)l) ;;

let ((tac1 : tactic) THEN (tac2 : tactic)) g =
   let gl,p = tac1 g in
   let gll,pl = split(map tac2 gl) in
   flat gll ,  (p o mapshape(map length gll)pl) ;;

let ((tac1:tactic) THENL (tac2l : tactic list)) g =
   let gl,p = tac1 g  in
   let gll,pl = split(map (\(tac2,g). tac2 g) tac2gl)
		where tac2gl = combine(tac2l,gl) ? failwith `THENL`
   in
   flat gll  ,  (p o mapshape(map length gll)pl);;

(THEN,THENL);;

end_section THEN_THENL;;

let (THEN,THENL) = it;;

ml_curried_infix `ORELSE` ;;

let ((tac1:tactic) ORELSE tac2) (g:goal) =  tac1 g ? tac2 g ;;

%
Fail with the given token.  Useful in tactic programs to check that a tactic 
produces no subgoals.  Write
	TAC  THEN  FAIL_TAC `TAC did not solve the goal`
%

let FAIL_TAC tok : tactic = \g. failwith tok;;

%Tactic that succeeds on no goals;  identity for ORELSE%
let NO_TAC : tactic = FAIL_TAC `NO_TAC`;;

%Tactic that succeeds on all goals;  identity for THEN%

let ALL_TAC : tactic = \g. [g],hd;;

let TRY tac = tac ORELSE ALL_TAC;;

%
The abstraction around g is essential to avoid looping, due to applicative
order semantics
%

letrec REPEAT tac g = ((tac THEN REPEAT tac) ORELSE ALL_TAC) g ;;

% Check whether a theorem achieves a goal, using no extra assumptions %

let achieves th : goal -> bool =
    \(asl,w).
    aconv (concl th) w & 
    forall (\h. (exists (aconv h)) asl) (hyp th);;

% MJCG 17/1/89 for HOL88. mk_fthm not used. 

let fakethms gl = map mk_fthm gl;;
%

%
Check the goal list and proof returned by a tactic.
At top-level, it is convenient to type "chktac it;;"

MJCG 17/1/89 for HOL88: mk_thm used instead of mk_fthm. This
introduces slight insecurity into the system, but since chktak
is assignable this insecurity can be removed by doing:

   chktak := \(gl,prf). fail

%
letref chktac((gl:goal list),(prf:proof)) = prf(map mk_thm gl);;

%Check whether a prospective (goal list, proof) pair is valid.
 MJCG 17/1/89 for HOL88: "falsity.asl" changed to "asl".
%

let check_valid : goal -> (goal list # proof) -> bool =
   \(asl,w).
    set_fail_prefix `check_valid`
       (\glp. achieves (chktac glp) (asl, w));;

%
Tactical to make any tactic valid.
"VALID tac" is the same as "tac", except it will fail in the cases where
"tac" returns an invalid proof. 

VALID uses mk_thm; the proof could assign its arguments to 
global theorem variables, making them accessible outside.

This kind of insecurity is very unlikely to lead to accidental proof of false
theorems; see comment preceding check_valid for how to remove insecurity.

Previously mk_fthm was used by check_valid instead of mk_thm (see
hol-drule.ml), but this lead to problems with tactics (like resolution) that
checked for "F".  A possible solution would be to use another constant that
was defined equal to F.  %

let (VALID: tactic -> tactic) tac g =
     let gl,prf = tac g in
     if check_valid g (gl,prf) then gl,prf
     else failwith `Invalid tactic`;;

%Tactical quantifiers -- Apply a list of tactics in succession%

%
Uses every tactic.
EVERY [TAC1;...;TACn] =  TAC1  THEN  ...  THEN  TACn
%

let EVERY tacl = itlist $THEN tacl ALL_TAC;;

%
Uses first tactic that succeeds.
FIRST [TAC1;...;TACn] =  TAC1  ORELSE  ...  ORELSE  TACn
%

let FIRST tacl g = tryfind (\tac:tactic. tac g) tacl  ? failwith `FIRST`;;

let MAP_EVERY tacf lst  =  EVERY (map tacf lst);;

let MAP_FIRST tacf lst =  FIRST (map tacf lst);;

%Call a thm-tactic for every assumption%

% --------------------------------------------------------------------- %
% Optimized 13.5.93 by JVT to remove the function composition to        %
% enhance speed.                                                        %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
%    let EVERY_ASSUM : (thm -> tactic) -> tactic =                      %
%        ASSUM_LIST o MAP_EVERY;;                                       %
% --------------------------------------------------------------------- %

let EVERY_ASSUM : (thm -> tactic) -> tactic = \x. (ASSUM_LIST (MAP_EVERY x));;

% --------------------------------------------------------------------- %
% Call a thm-tactic for the first assumption at which it succeeds	%
%									%
% Revised: TFM 91.04.20 : failures of ttac to produce a tactic are now  %
% filtered out.								%
%									%
% Old implementation:							%
%									%
% let FIRST_ASSUM : (thm->tactic)->tactic = ASSUM_LIST o MAP_FIRST;;    %
%									%
% Revised: TFM 91.05.24 : optimized; no longer constructs extra tactics.%
%									%
% OLD CODE:								%
% let FIRST_ASSUM (ttac:thm->tactic) (A,g) =				%
%  FIRST (mapfilter (ttac o ASSUME) A) (A,g) ? failwith `FIRST_ASSUM`;; %
% --------------------------------------------------------------------- %

let FIRST_ASSUM =
    letrec find ttac as g =
       if (null as) then failwith `FIRST_ASSUM` else
          (ttac (ASSUME(hd as)) g ? find ttac (tl as) g) in
    \(ttac:thm->tactic). \(A,g). find ttac A (A,g);;


%
Split off a new subgoal and provide it as a theorem to a tactic
	SUBGOAL_THEN wa (\tha. tac)
makes a subgoal of wa, and also assumes wa for proving the original goal.
Most convenient when the tactic solves the original goal, leaving only the
new subgoal wa.
%

let SUBGOAL_THEN wa ttac :tactic (asl,w) =
    let gl,p = ttac (ASSUME wa) (asl,w) in
    (asl,wa) . gl,
    \(tha.thl). PROVE_HYP tha (p thl);;

% A tactical that makes a tactic fail if it has no effect %

%<
 (Comment corrected by MJCG on 17.10.90 and "letrec" changed to "let")
>%

let CHANGED_TAC (tac:tactic) g =
 let gl,p = tac g
 in
 if set_equal gl [g] then fail else (gl,p);;
