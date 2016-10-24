%****************************************************************************%
%									     %
% File:         tools.ml						     %
%									     %
% Editor:       Paul Curzon			     			     %
%									     %
% Date:         May 1991						     %
%									     %
% Description:  General Purpose Stuff that can be loaded without	     %
% 	        having to load any other library/file			     %
%									     %
%****************************************************************************%



%*********************************  HISTORY  ********************************%
%									     %
%	This file is the amalgamation of general purpose tool files from     %
%	  Mike Benjamin							     %
%	  Paul Curzon							     %
%	  Wim Ploegaerts						     %
%	The files have been trimmed to include only those tools used by the  %
%	more_arithmetic and more_lists libraries			     %
%									     %
%*****************************  END OF HISTORY  *****************************%





%****************************************************************************%
%									     %
% File:         general_purp.ml						     %
%									     %
% Author:       Wim Ploegaerts  (ploegaer@imec.be)			     %
%									     %
% Date:         Mon Feb 11 1991						     %
%									     %
% Organization: Imec vzw.						     %
%               Kapeldreef 75						     %
%               3001 Leuven - Belgium					     %
%									     %
% Description:  General Purpose Stuff that can be loaded without	     %
% 	      having to load any other library/file			     %
%									     %
%****************************************************************************%





%----------------------------------------------------------------------------%
%									     %
% 				 CONVERSIONS				     %
%									     %
%----------------------------------------------------------------------------%


let LHS_CONV = RATOR_CONV o RAND_CONV;;

let CONJ1 = fst o CONJ_PAIR;;

let CONJ2 = snd o CONJ_PAIR;;

let SPEC_SYM = SYM o SPEC_ALL;;






%----------------------------------------------------------------------------%
%									     %
% 				    RULES				     %
%									     %
%----------------------------------------------------------------------------%


let SYM_RULE = 
    CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) 
    ? failwith `SYM_RULE`;;


%----------------------------------------------------------------------------%
%									     %
% 				   TACTICS				     %
%									     %
%----------------------------------------------------------------------------%


%============================================================================%
%									     %
%                        PROTECT_REWRITE_CONV:				     %
%									     %
%        Conversion for rewrite rules of the form |- !x1 ... xn. t == u	     %
%              Matches x1 ... xn : 	 t'  ---->  |- t' == u'		     %
%   Matches all types in conclusion except those mentioned in hypotheses     %
%									     %
%============================================================================%



%									     %
%      `REWRITE_CONV` behandelt alle vrije variabelen met vervanging door    %
%      generieke variabelen  (`genvars`). De volgende protected functies     %
%      leggen hieraan restricties op.					     %
%									     %




letrec PROTECT_GSPEC tml th =
    let wl,w = dest_thm th in
    if is_forall w then
	let tm = fst(dest_forall w) in
	let tm' = (mem tm tml) => (genvar (type_of tm)) | tm in
	PROTECT_GSPEC tml (SPEC tm' th)
    else th;;

%									     %
% Match a given part of "th" to a term, instantiating "th".		     %
% The part should be free in the theorem, except for outer bound variables   %
%									     %

let PROTECT_PART_MATCH tml  partfn th =
    let pth = PROTECT_GSPEC tml (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth;;



let PROTECT_REWRITE_CONV tml =
  set_fail_prefix `PROTECT_REWRITE_CONV`
     (PROTECT_PART_MATCH tml (fst o dest_eq));;  

%									     %
%    Example of the use:						     %
%    ------------------							     %
%									     %
%    TRANSLATION_LEQ_EQ:						     %
%      " !z x y . (x leq y) = (x plus z) leq (y plus z)"		     %
%									     %
%    let thm = SPEC "n:zet" TRANSLATION_LEQ_EQ;;			     %
%    thm = |- !x y. x leq y = (x plus n) leq (y plus n) : thm		     %
%									     %
%    (PROTECT_REWRITE_CONV ["x:zet";"y:zet"] thm) "a leq b";;		     %
%    |- a leq b = (a plus n) leq (b plus n)				     %
%									     %
%    (REWR_CONV thm) "a leq b";;					     %
%    |- a leq b = (a plus GEN_VAR_871) leq (b plus GEN_VAR_871)		     %
%									     %

%<-------------------------------------------------------------------------->%

%****************************************************************************%
%									     %
% File:         tactics.ml						     %
%									     %
% Author:       Paul Curzon			     			     %
%									     %
% Date:         May 1991						     %
%									     %
%									     %
%****************************************************************************%

%****************************************************************************%
%									     %
%   Tactic to rewrite using the last added assumption and general rewrites   %
%									     %
%****************************************************************************%

let POP_REWRITE_TAC = POP_ASSUM (\th.REWRITE_TAC[th]);;

%****************************************************************************%
%									     %
%   Tactic to remove the last added assumption from the assumption list      %
%									     %
%****************************************************************************%

let POP_JUNK_TAC = POP_ASSUM (\th. ALL_TAC);;

%****************************************************************************%
%									     %
%   Tactics to apply rules to the last added assumption from the             %
%   assumption list      						     %
%									     %
%****************************************************************************%

let POP_TAC rule = POP_ASSUM (\th . ASSUME_TAC (rule th));;


let PEEK_ASSUM (thm_tac:thm_tactic) ((asl,g):goal) =
     thm_tac (ASSUME (hd asl))
             (asl, g);;


let PEEK_TAC rule = PEEK_ASSUM (\th . ASSUME_TAC (rule th));;

%****************************************************************************%
%									     %
%   Specialize a single named variable t1 to t2				     %
%									     %
%****************************************************************************%

let SPEC1 t1 t2 th =
     (GEN_ALL (SPEC t2 (GEN t1 (SPEC_ALL th))));;

%****************************************************************************%
%									     %
%   Rewrite the last assumption with the second last			     %
%									     %
%****************************************************************************%

let REWRITE_A1_WITH_A2_THEN (tac:thm_tactic)  =
      (POP_ASSUM (\th1 . (POP_ASSUM (\th2. tac
         (REWRITE_RULE[th2] th1)))));;

%****************************************************************************%
%									     %
%   Rewrite the second last assumption with the  last			     %
%									     %
%****************************************************************************%


let REWRITE_A2_WITH_A1_THEN (tac:thm_tactic)  =
      (POP_ASSUM (\th1 . (POP_ASSUM (\th2. tac
         (REWRITE_RULE[th1] th2)))));;
%****************************************************************************%
%									     %
%   Versions of RES_TAC and IMP_RES_TAC which only add a single new	     %
%   assumption	to the assumption list. It must be identical to the term     %
%   given orelse no new assumption is added		    	     	     %
%									     %
%****************************************************************************%


let FILTER_THM f target th =
         if (snd (dest_thm th)) = target
         then f th
         else ALL_TAC;;

letrec filter_assume_tac th (asl,c) g =
   if (asl = []) then ASSUME_TAC th g
   else if ((snd (dest_thm th)) = (hd asl)) then ALL_TAC g
   else filter_assume_tac th ((tl asl),c) g ;;

let FILTER_ASSUME_TAC th1 g =
      filter_assume_tac th1 g g;;

let FILTER_IMP_RES_TAC t  =
   REPEAT_GTCL IMP_RES_THEN (FILTER_THM FILTER_ASSUME_TAC t);;

let FILTER_RES_TAC t  =
    let FILTER_THM f target th =
         if (snd (dest_thm th)) = target
         then f th
         else FILTER_IMP_RES_TAC target th
     in
       RES_THEN (FILTER_THM FILTER_ASSUME_TAC t);;
%****************************************************************************%
%									     %
%   STRIP_TAC except do not split CONJUNCTS apart.			     %
%									     %
%****************************************************************************%
let NC_STRIP_TAC (asl,t) =
     if is_conj t
     then NO_TAC (asl,t)
     else (STRIP_TAC (asl,t)) ;; 




%   ***************************************************************************
    *                                                                         *
    *    Mike Benjamin                                                        *
    *    FPC 267                                                              *
    *    British Aerospace Sowerby Research Centre                            *
    *    PO BOX 5                                                             *
    *    Filton                                                               *
    *    Bristol  BS12 7QW                                                    *
    *                                                                         *
    *    Tel: (0272) 366198                                                   *
    *    EMAIL: benjamin@src.bae.co.uk                                        *
    *                                                                         *
    **************************************************************************%



%   **************************************************************************
    *                                                                         *
    *    GENERAL PURPOSE TACTICS.                                             *
    *                                                                         *
    *    These are based on existing tactics in Cambrideg-LCF that don't seem
          to have been implemented                                            *
    *    in HOL.                                                              *
    *                                                                         *
    *         !!! WARNING !!!                                                 *
    *    No provision has been made in these routines for exception handling. *
    *                                                                         *
    **************************************************************************%




%   ***************************************************************************
    *                                                                         *
    *    CUT : thm -> thm -> thm                                              *
    *                                                                         *
    *    X |- A    Y, A |- B                                                  *
    *    -------------------                                                  *
    *        X, Y |- B                                                        *
    *                                                                         *
    **************************************************************************%

let CUT ath bth = MP (DISCH (concl ath) bth) ath;;

%   ***************************************************************************
    *                                                                         *
    *    Introduce a lemma.                                                   *
    *                                                                         *
    *    CUT_TAC : form -> tactic                                             *
    *               A                                                         *
    *                                                                         *
    *    X |- A    X, A |- B                                                  *
    *    -------------------                                                  *
    *        X |- B                                                           *
    *                                                                         *
    **************************************************************************%

let CUT_TAC A :tactic (asl,B) = 
    ([(asl,A);(A.asl,B)], (\ [thA;thB]. CUT thA thB));;

%   ***************************************************************************
    *                                                                         *
    *    Add a theorem to the assumption list.                                *
    *                                                                         *
    *    CUT_TAC : thm -> tactic                                              *
    *               A                                                         *
    *                                                                         *
    *    Y, A |- B                                                            *
    *    ---------                                                            *
    *     Y |- B                                                              *
    *                                                                         *
    **************************************************************************%
 
let CUT_THM_TAC bth :tactic (asl,w) =
    ([(((concl bth).asl),w)],(\ [th]. CUT bth th));;


%   ***************************************************************************
    *                                                                         *
    * Disjunction elimination in the assumption list, generating two subgoals.*
    *                                                                         *
    *    DISJ_LEFT_TAC : tactic                                               *
    *                                                                         *
    *      X, A |- C   X ,B |- C                                              *
    *     ----------------------                                              *
    *         X, A \/ B |- C                                                  *
    *                                                                         *
    **************************************************************************%


letrec take  p (rxs, xxs) = if
                             (length xxs = 0)
                           then 
                              ([], rev rxs)
                           else
                             (if 
                                p (hd xxs)
                              then
                                ([hd xxs], rev rxs @ (tl xxs))
                              else
                                take p ((hd xxs).rxs, (tl xxs)));;

let take_first p xs = take p ([],xs);;

let DISJ_LEFT_TAC :tactic (asl,C) =
       let 
         ([asm], asl') = (take_first is_disj asl)
       in
           let 
              (A,B) = (dest_disj asm)
           in  
    ([(A.asl',C); (B.asl',C)], \[thA;thB]. DISJ_CASES (ASSUME asm) thA thB);;


%   ***************************************************************************
    *                                                                         *
    *    Specialise forall.                                                   *
    *                                                                         *
    *    FORALL_LEFT_TAC : term X term -> tactic                              *
    *                                                                         *
    *     Y, !x.A, A[t/x] |- B                                                *
    *     --------------------                                                *
    *         Y, !x.A |- B                                                    *
    *                                                                         *
    **************************************************************************%

let isvar_forall x C =
    is_forall C &
	let (y,_) = dest_forall C in x=y;;

let FORALL_LEFT_TAC (t:term,x:term) :tactic ((asl,C):goal) =
       let ([asm], z) = take_first (isvar_forall x) asl in
           let specth = SPEC t (ASSUME asm)
           in  ([(concl specth . asl, C)], 
                \ [th]. CUT specth th);;

%   ***************************************************************************
    *                                                                         *
    *    Specialise exists.                                                   *
    *                                                                         *
    *    EXISTS_LEFT_TAC : tactic                                             *
    *                                                                         *
    *     Y, A[x'/x] |- B                                                     *
    *     ---------------  (provided x' is not free in ?x.A, Y, or B)         *
    *       Y, ?x.A |- B                                                      *
    *                                                                         *
    **************************************************************************%

let terml_frees wl = itlist (\ w . union (frees w)) wl [];;

let EXISTS_LEFT_TAC :tactic (asl,C) =
       let ([asm], asl') = take_first is_exists asl in
           let (x,A) = dest_exists asm in
           let x' = variant (terml_frees(C.asl)) x in
           let A' = subst [(x',x)] A
           in  ([(A'.asl',C)], 
                \ [th]. CHOOSE (x', ASSUME asm) th);;

%   ***************************************************************************
    *                                                                         *
    * Solve a goal provided the result to be proven is in the assumption list.*
    *                                                                         *
    *    ACCEPT_ASM_TAC : tactic                                              *
    *                                                                         *
    **************************************************************************%


let ACCEPT_ASM_TAC : tactic ((asl,a):goal) = ([], \[]. ASSUME a);;

%   ***************************************************************************
    *                                                                         *
    *    A set of tactics that rewrite the goal using                         *
    *    assumptions identified by index numbers.                             *
    *                                                                         *
    *    N_REWRITE_TAC : integer -> tactic                                    *
    *    S_REWRITE_TAC : integer list -> tactic                               *
    *    ONCE_N_REWRITE_TAC :integer -> tactic                                *
    *                                                                         *
    **************************************************************************%

letrec index i (x.xs) = if (i = 1) then x else (index (i-1)  xs);;

letrec indexes is xs = if (is = []) then [] else ((index (hd is) xs).(indexes (tl is) xs));;

let N_REWRITE_TAC n  = ASSUM_LIST (\ (x:thm list). REWRITE_TAC [index n x]);;

let S_REWRITE_TAC n  = ASSUM_LIST (\ (x:thm list). REWRITE_TAC (indexes n x));;

let ONCE_N_REWRITE_TAC n  = ASSUM_LIST (\ (x:thm list). ONCE_REWRITE_TAC [index n x]);;
 
%   ***************************************************************************
    *                                                                         *
    * A tactic that adds the inverse of an assumption to the assumption list. *
    *    It is based on the law that equality is symmetric.                   *
    *                                                                         *
    *    N_REVERSE_TAC : integer -> tactic                                    *
    *                                                                         *
    **************************************************************************%

let N_REVERSE_TAC n = ASSUM_LIST (\ (x:thm list). CUT_THM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] (index n x)));;


let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));;

let LEMMA_PROOF term tacticl (asl,g) =
(MP_TAC (TAC_PROOF ((asl,term), (EVERY tacticl))) THEN STRIP_TAC)  (asl,g);;


let MATCH_EQ_MP eqth = 
     let match = PART_MATCH (fst o dest_eq) eqth ? failwith `MATCH_MP` 
     in
     \th. EQ_MP (match (concl th)) th;;
