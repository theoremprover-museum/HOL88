%
 Quasi resolution on assumptions with just one match_mp
%

let ONE_IMP_RES_TAC th = FIRST_ASSUM (ASSUME_TAC o (MATCH_MP th));; 

% Applies thm_tactic to the first assumption it succeeds on,
  then pops that assumption
%
 
let REPLACE_FIRST_ASSUM thm_tac = POP_ASSUM_LIST 
	\thl.
	 (FIRST	(mapfilter
	  	 (\th.	(thm_tac th) 
			THEN (MAP_EVERY ASSUME_TAC (subtract thl [th]))
		 ) thl
		)
	 );;   


% Allows a detour, throwing away any changes made to the assumptions
  useful for rewriting without keeping the equations, doing intermediate 
  resolution the results of which aren't permanent
%

let DETOUR tac = ASSUM_LIST 
	(\thl. tac THEN (POP_ASSUM_LIST (\nthl.MAP_EVERY ASSUME_TAC thl)));; 


% Converts assumptions using a supplied conversion 
  The converted assumptions are added to the assumption list
%

let MAPFILTER_ASSUM tac  = 
	ASSUM_LIST (EVERY o (mapfilter tac));; 

let CONV_ASM conv = MAPFILTER_ASSUM (ASSUME_TAC o (CONV_RULE conv));;


% Rewrites each assumption, using only
  the theorem_list provided and the other assumptions 
  Won't rewrite an assumption using itself, 
  and the original assumption
  list is replaced by the rewritten one
%

letrec REWRITE_ASM_fn thl asl =
	if null asl then ALL_TAC
	else ASSUME_TAC (REWRITE_RULE (thl@(tl asl)) (hd asl))
		THEN REWRITE_ASM_fn ((hd asl).thl) (tl asl);;
                                       
let REWRITE_ASM thl = POP_ASSUM_LIST \asl.REWRITE_ASM_fn (thl) asl;;

letrec ONCE_REWRITE_ASM_fn thl asl =
	if null asl then ALL_TAC
	else ASSUME_TAC (ONCE_REWRITE_RULE (thl@(tl asl)) (hd asl))
		THEN ONCE_REWRITE_ASM_fn ((hd asl).thl) (tl asl);;
                                       
let ONCE_REWRITE_ASM thl = POP_ASSUM_LIST \asl.ONCE_REWRITE_ASM_fn (thl) asl;;

letrec UNDISCH_ALL_fn thl = 
	if null thl then ALL_TAC
	else UNDISCH_TAC (snd (dest_thm (hd thl))) THEN UNDISCH_ALL_fn (tl thl);; 

let UNDISCH_ALL_TAC = ASSUM_LIST UNDISCH_ALL_fn;;

let DISJ_CASES_SPLIT t  = DISJ_CASES_TAC (SPEC t EXCLUDED_MIDDLE);;

% Strengthen a goal by adding a conjunct on the left 

[A] ?- glt
================ (CONJ1_INTRO_TAC t)
[A] ?- t /\ glt
 
%

let (CONJ1_INTRO_TAC:term->tactic) (t:term) (asl, glt) =
	(
	 [(asl,mk_conj(t,glt))],
	 \[th].	CONJUNCT2 th
	);;


% Eliminate unique part of ?!x.Px, ie. return ?x.Px %

let UNIQUE_ELIM = 
	CONJUNCT1
	o (CONV_RULE (DEPTH_CONV BETA_CONV)) 
	o (REWRITE_RULE [EXISTS_UNIQUE_DEF]);;

% Fork thm_tactics on the same th %

let FORK (f:*->tactic) (g:*->tactic) = \t. f t THEN g t;;


% Pop a named assumption %

let POP_IT = \t. UNDISCH_TAC t THEN DISCH_THEN \th.ALL_TAC;;

% Give a thm_tactic a named assumption and apply it % 

let APPLY_TO t tac = UNDISCH_TAC t THEN 
	(DISCH_THEN \th. ASSUME_TAC th THEN tac th);; 
 
% Replace a named assumption with the result of
  applying a rule to it
% 

let REPLACE_ASSUM t rule = 
	UNDISCH_TAC t 
	THEN DISCH_THEN \th.ASSUME_TAC (rule th);; 

let REWRITE_ASSUM thl t =
	UNDISCH_TAC t 
	THEN (DISCH_THEN \th.ASSUME_TAC (REWRITE_RULE thl th));;


% Restricted Resolution: just MATCH_MP on the assumptions 
  and a theorem, enriching the assumptions with the results, if any
%

letrec match_fn th thl = 
	if null thl then failwith `NO MATCH`
	else MATCH_MP th (hd thl) ? 
		(match_fn th (tl thl)) ;;
 
let MATCH_MP_TAC th = ASSUM_LIST \thl.ASSUME_TAC (match_fn th thl);; 


% ASSUM_REDUCE_TAC : tactic

Reduces a goal by removing subterms that appear in the assumption list.
Strangely enough, ASM_REWRITE_TAC [] doesn't always do this.

%

let ASSUM_REDUCE_TAC = 
	ASSUM_LIST (\thl.SUBST_TAC (map EQT_INTRO thl))
	THEN REWRITE_TAC[];; 
	


 
% SELECT_TAC : term -> tactic   ( term = @x.P(x) )

    [A] P[@x.P(x)]
======================
     [A] ?x.P(x)
%

let SELECT_TAC (thisterm:term) (thisgoal:goal) =
(let t1,t2=dest_select thisterm in
 if (snd thisgoal)= subst[(thisterm,t1)]t2
 then [((fst thisgoal),(mk_exists (t1,t2)))], (\[thm].(SELECT_RULE thm))
 else fail
)?failwith `SELECT_TAC`;;

% PAIR_EQ_TAC : tactic

     [A] (p,q) = (r,s) 
==============================
   [A] p=r            [A] q=s
%
 
let (PAIR_EQ_TAC:tactic) (asl, gl) =
 (let (p, q) = dest_eq gl in
  let (a, b) = dest_pair p in
  let (c, d) = dest_pair q in
	(
	 [(asl,mk_eq(a,c)); (asl,mk_eq(b,d))],
	 \[th1;th2].
		let a = type_of (fst (dest_eq (snd (dest_thm th1)))) in
		let c = type_of (fst (dest_eq (snd (dest_thm th2)))) in
		MK_COMB (AP_TERM "$,:^a->^c->(^a#^c)" th1, th2)
	)		
 )?failwith `PAIR_EQ_TAC`;;

% CONTRAPOS_TAC : tactic

    [A] p ==> q
  ================
    [A] ~q ==> ~p
%

let (CONTRAPOS_TAC:tactic) (asl, gl) = 
 let (p,q) = dest_imp gl in
 (
  [(asl, mk_imp(mk_neg q, mk_neg p))],
  \[th]. REWRITE_RULE [NOT_CLAUSES] (CONTRAPOS th)
 );;
 

% STRENGTHEN_TAC : thm_tactic
        
     [A] p
  ============ STRENGTHEN_TAC (|- p ==> q)
     [A] q

%

let (STRENGTHEN_TAC:thm_tactic) mp_th (asl, gl) = 
 let (p,_) = dest_imp (snd (dest_thm mp_th)) in
 (
  [(asl, p)],
  \[mp_ass]. MP mp_th mp_ass    
 );;
 
 
% Depth convert a theorem (list) once using SYM 
  Extremely useful for reverse rewriting
%
                  
let SYM_th = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV);;

let SYML_th = map (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV));;

% Substitute on right side of an equation %

let RIGHT_SUBSTL = \thl. GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [] thl;;

let RIGHT_SUBST = 
	\th. GEN_REWRITE_RULE 
		(RAND_CONV o DEPTH_CONV) [] [th];; 
 
let ONCE_RIGHT_SUBST = 
	\th. GEN_REWRITE_RULE 
		(RAND_CONV o ONCE_DEPTH_CONV) [] [th];; 

let RIGHT_SUBST_TAC =
        \th. GEN_REWRITE_TAC 
		(RAND_CONV o DEPTH_CONV) [] [th];; 

let ONCE_RIGHT_SUBST_TAC = 
	\th. GEN_REWRITE_TAC 
		(RAND_CONV o ONCE_DEPTH_CONV) [] [th];; 


% Substitute once on left side of an equation %

let ONCE_LEFT_SUBSTL = 
	\thl. GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) [] thl;;

let ONCE_LEFT_SUBST = 
	\th. GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) [] [th];; 

let ONCE_LEFT_SUBST_TAC = 
	\th. GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [] [th];; 
 
let LEFT_SUBST_TAC = 
	\th. GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [] [th];; 

let REWRITE_TERM t th =
	REWRITE_TAC [RIGHT_SUBST th (REFL t)] ;;

let ONCE_REWRITE_TERM t th =
	ONCE_REWRITE_TAC [ONCE_RIGHT_SUBST th (REFL t)] ;;

let REWRITE_TERML t thl = 
	REWRITE_TAC
	 [GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) [] thl (REFL t)];;

let ONCE_REWRITE_TERML t thl = 
	REWRITE_TAC
	 [GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [] thl (REFL t)];;

% SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A;t] t1    [A] t
%

let SUPPOSE_TAC thisterm thisgoal =
(if type_of thisterm = ":bool"
 then [((thisterm.(fst thisgoal)),(snd thisgoal));((fst thisgoal),thisterm)],
      (\[goalthm;termthm].MP (DISCH thisterm goalthm) termthm)
 else fail)?failwith `SUPPOSE_TAC`;;


%REV_SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A] t    [A;t] t1
%

let REV_SUPPOSE_TAC thisterm thisgoal =
(if type_of thisterm = ":bool"
 then [((fst thisgoal),thisterm);((thisterm.(fst thisgoal)),(snd thisgoal))],
      (\[termthm;goalthm].MP (DISCH thisterm goalthm) termthm)
 else fail)?failwith `REV_SUPPOSE_TAC`;;


% ADD_ASSUMS_THEN : term list -> tactic -> tactic                       %
%                                                                       %
% For adding assumptions to the goal to be used by the given tactic.    %
% Returns the result of applying the tactic to the augmented goal,      %
% together with a new subgoal for each new assumption added.            %

letrec ADD_ASSUMS_THEN asmlist tactic (asms,goal) =
 if null asmlist then tactic  (asms,goal) else
 if (exists (aconv (hd asmlist)) asms)
 then (ADD_ASSUMS_THEN (tl asmlist) tactic (asms,goal))
 else
  ((SUPPOSE_TAC (hd asmlist)) THENL
   [(ADD_ASSUMS_THEN (tl asmlist) tactic);ALL_TAC])
  (asms,goal);;

% ADD_STRIP_ASSUMS_THEN : term list -> tactic -> tactic                 %
%                                                                       %
% Like ADD_ASSUMS_THEN except it srtips the new assumptions before      %
% adding them to the assumptions.                                       %

letrec ADD_STRIP_ASSUMS_THEN asmlist tactic (asms,goal) =
 if null asmlist then tactic  (asms,goal) else
 if (exists (aconv (hd asmlist)) asms)
 then (ADD_STRIP_ASSUMS_THEN (tl asmlist) tactic (asms,goal))
 else
  ((SUPPOSE_TAC (hd asmlist)) THENL
   [((POP_ASSUM STRIP_ASSUME_TAC) THEN
     (ADD_STRIP_ASSUMS_THEN (tl asmlist) tactic));
    ALL_TAC])
  (asms,goal);;

let ANTE_IMP_THM = PROVE
(	"! a b c. a ==> b ==> c = a /\ b ==> c",
	CONV_TAC(DEPTH_CONV ANTE_CONJ_CONV)
	THEN REWRITE_TAC[]
);;

let de_imp = REWRITE_RULE[ANTE_IMP_THM];;

let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;

% ASM_REWRITE with a rule for transforming the assumptions used
  before they are applied
%

let ASM_RULE_REWRITE_TAC rule thl = 
	ASSUM_LIST \asml. REWRITE_TAC ((map rule asml) @ thl);; 

let ONCE_ASM_RULE_REWRITE_TAC rule thl = 
	ASSUM_LIST \asml. ONCE_REWRITE_TAC ((map rule asml) @ thl);;


