%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        resolve.ml                                            %
%                                                                             %
%     DESCRIPTION:      Resolution inference rules and tactics                %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml  %
%                       hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml,     %
%                       tacont.ml, tactics.ml, conv.ml                        %
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
%     REVISION HISTORY: new resolve.ml for HOL Version 1.12 [TFM 91.01.26]    %
%=============================================================================%

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml, etc	%
% --------------------------------------------------------------------- %
if compiling then
   (loadf `ml/hol-in-out`;
    loadf `ml/hol-rule`;
    loadf `ml/hol-drule`;
    loadf `ml/drul`;
    loadf `ml/tacticals`;
    loadf `ml/tacont`;
    loadf `ml/tactics`;
    loadf `ml/conv`);;

% --------------------------------------------------------------------- %
% Search among a list of implications to perform Modus Ponens		%
% Used nowhere --- deleted until found useful [TFM 90.04.24]		%
% let MULTI_MP impl ante =						%
%     tryfind (\imp. MATCH_MP imp ante) impl  ?  failwith `MULTI_MP`;;  %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Forwards chaining by Modus Ponens					%
% Used nowhere --- deleted until found useful [TFM 90.04.24]		%
% let MP_CHAIN = REDEPTH_CHAIN o MULTI_MP;;				%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Accept a theorem that, properly instantiated, satisfies the goal      %
% --------------------------------------------------------------------- %
let MATCH_ACCEPT_TAC thm : tactic =
    let fmatch = PART_MATCH I thm in
    let atac (asl,w) = [], K (fmatch w) in
    set_fail_prefix `MATCH_ACCEPT_TAC` ((REPEAT GEN_TAC) THEN atac);;

% --------------------------------------------------------------------- %
% Basic unit for resolution tactics					%
% DELETED: TFM 88.03.31 (not used anywhere)				%
%									%
% let MATCH_MP_TAC impth = STRIP_ASSUME_TAC o (MATCH_MP impth);;	%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Resolve implicative assumptions with an antecedent			%
% --------------------------------------------------------------------- %
let ANTE_RES_THEN ttac ante : tactic =
    ASSUM_LIST (EVERY o (mapfilter (\imp. ttac (MATCH_MP imp ante))));;

% --------------------------------------------------------------------- %
% Old versions of RESOLVE_THEN etc.			[TFM 90.04.24]  %
% 									%
% letrec RESOLVE_THEN antel ttac impth : tactic =			%
%     let answers = mapfilter (MATCH_MP impth) antel in			%
%     EVERY (mapfilter ttac answers)					%
%     THEN								%
%     (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));;		%
% 									%
% let OLD_IMP_RES_THEN ttac impth =					%
%  ASSUM_LIST								%
%     (\asl. EVERY (mapfilter (RESOLVE_THEN asl ttac) 			%
%		  	      (IMP_CANON impth)));;			%
% 									%
% let OLD_RES_THEN ttac = 						%
%     ASSUM_LIST (EVERY o (mapfilter (OLD_IMP_RES_THEN ttac)));;	%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% A trick tactic for solving existential/disjunctive goals		%
% Too tricky, and depends on obsolete version of IMP_RES_THEN		%
% Deleted: TFM 90.04.24							%
% let SELF_RES_TAC (asl,w) = 						%
%    OLD_IMP_RES_THEN ACCEPT_TAC					%
%       (DISCH w (itlist ADD_ASSUM asl (ASSUME w))) (asl,w);;		%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Resolution tactics from LCF - uses IMP_CANON and GSPEC 		%
% 									%
% Deleted: TFM 90.04.24							%
%									%
% let OLD_IMP_RES_TAC = OLD_IMP_RES_THEN STRIP_ASSUME_TAC;;		%
% let OLD_RES_TAC = OLD_RES_THEN STRIP_ASSUME_TAC;;			%
% --------------------------------------------------------------------- %

% ===================================================================== %
% Resolution tactics for HOL - uses RES_CANON and SPEC_ALL 		%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put a theorem 							%
%									%
%	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			%
%									%
% into canonical form for resolution by splitting conjunctions apart    %
% (like IMP_CANON but without the stripping out of quantifiers and only %
% outermost negations being converted to implications).			%
%									%
%   ~t            --->          t ==> F        (at outermost level)	%
%   t1 /\ t2	  --->		t1,   t2				%
%   (t1/\t2)==>t  --->		t1==> (t2==>t)				%
%   (t1\/t2)==>t  --->		t1==>t, t2==>t				%
%									%
%									%
% Modification provided by David Shepherd of Inmos to make resolution   %
% work with equalities as well as implications. HOL88.1.08,23 jun 1989. %
%									%
%   t1 = t2      --->          t1=t2, t1==>t2, t2==>t1			%
%									%
% Modification provided by T Melham to deal with the scope of 		%
% universal quantifiers. [TFM 90.04.24]					%
%									%
%   !x. t1 ==> t2  --->  t1 ==> !x.t2   (x not free in t1)		% 
%									%
% The old code is given below:						%
% 									%
%    letrec RES_CANON_FUN th =						%
%     let w = concl th in						%
%     if is_conj w 							%
%     then RES_CANON_FUN(CONJUNCT1 th)@RES_CANON_FUN(CONJUNCT2 th)	%
%     else if is_imp w & not(is_neg w) then				%
% 	let ante,conc = dest_imp w in					%
% 	if is_conj ante then						%
% 	    let a,b = dest_conj ante in					%
% 	    RES_CANON_FUN 						%
% 	    (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))	%
% 	else if is_disj ante then					%
% 	    let a,b = dest_disj ante in					%
% 	    RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @	%
% 	    RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))	%
% 	else								%
% 	map (DISCH ante) (RES_CANON_FUN (UNDISCH th))			%
%     else [th];;							%
% 									%
% This version deleted for HOL 1.12 (see below)		 [TFM 91.01.17] %
%									%
% let RES_CANON = 							%
%     letrec FN th = 							%
%       let w = concl th in						%
%       if (is_conj w) then FN(CONJUNCT1 th) @ FN(CONJUNCT2 th) else	%
%       if ((is_imp w) & not(is_neg w)) then				%
%       let ante,conc = dest_imp w in					%
%       if (is_conj ante) then						%
%          let a,b = dest_conj ante in					%
% 	   let ath = ASSUME a and bth = ASSUME b in			%
%                   FN (DISCH a (DISCH b (MP th (CONJ ath bth)))) else  %
%          if is_disj ante then						%
%         let a,b = dest_disj ante in					%
%        let ath = ASSUME a and bth = ASSUME b in			%
% 	          FN (DISCH a (MP th (DISJ1 ath b))) @			%
%                 FN (DISCH b (MP th (DISJ2 a bth))) else		%
%            map (GEN_ALL o (DISCH ante)) (FN (UNDISCH th)) else	%
%        if is_eq w then						%
%        let l,r = dest_eq w in						%
%            if (type_of l = ":bool") then				%
%            let (th1,th2) = EQ_IMP_RULE th in				%
%                (GEN_ALL th) . ((FN  th1) @ (FN  th2)) 		%
%                else [GEN_ALL th]					%
%            else [GEN_ALL th] in					%
%     \th. (let vars,w = strip_forall(concl th) in			%
%           let th1 = if (is_neg w)	 				%
% 	  		then NOT_ELIM(SPEC_ALL th) 			%
% 			else (SPEC_ALL th) in				%
%               map GEN_ALL (FN th1) ? failwith `RES_CANON`);;		%
% --------------------------------------------------------------------- %


% --------------------------------------------------------------------- %
% New RES_CANON for version 1.12.			 [TFM 90.12.07] %
% 									%
% The complete list of transformations is now:				%
%									%
%   ~t              --->        t ==> F        (at outermost level)	%
%   t1 /\ t2	    --->	t1, t2	       (at outermost level)	%
%   (t1/\t2)==>t    --->	t1==>(t2==>t), t2==>(t1==>t)		%
%   (t1\/t2)==>t    --->	t1==>t, t2==>t				%
%   t1 = t2         --->        t1==>t2, t2==>t1			%
%   !x. t1 ==> t2   --->        t1 ==> !x.t2   (x not free in t1)	% 
%   (?x.t1) ==> t2  --->	!x'. t1[x'/x] ==> t2			%
%									%
% The function now fails if no implications can be derived from the 	%
% input theorem.							%
%									%
% Bugfix: |- (?x. P[x]) ==> !x. Q[x] now transforms to the theorem	%
% |- !x. P[x] ==> !x'. Q[x'].			         [TFM 91.10.19] %
%									%
% Bugfix: check thm_frees not just frees for previous bugfix (above).	%
% [TFM 92.05.11]							%
% --------------------------------------------------------------------- %

let RES_CANON =
    let not_elim th = (is_neg (concl th) => true,(NOT_ELIM th) | (false,th)) in
    letrec canon fl th = 
       let w = concl th in
       if (is_conj w) then 
          let (th1,th2) = CONJ_PAIR th in (canon fl th1) @ (canon fl th2) else
       if ((is_imp w) & not(is_neg w)) then
          let ante,conc = dest_neg_imp w in
          if (is_conj ante) then
             let a,b = dest_conj ante in
	     let cth = NOT_MP th (CONJ (ASSUME a) (ASSUME b)) in
	     let th1 = DISCH b cth and th2 = DISCH a cth in
                 (canon true (DISCH a th1)) @ (canon true (DISCH b th2)) else
          if (is_disj ante) then
             let a,b = dest_disj ante in
	     let ath = DISJ1 (ASSUME a) b and bth = DISJ2 a (ASSUME b) in
             let th1 = DISCH a (NOT_MP th ath) and
                 th2 = DISCH b (NOT_MP th bth) in
                 (canon true th1) @ (canon true th2) else
          if (is_exists ante) then
             let v,body = dest_exists ante in
	     let newv = variant (thm_frees th) v in
	     let newa = subst [newv,v] body in
	     let th1 = NOT_MP th (EXISTS (ante, newv) (ASSUME newa)) in
	         canon true (DISCH newa th1) else
             map (GEN_ALL o (DISCH ante)) (canon true (UNDISCH th)) else
       if (is_eq w & (type_of (rand w) = ":bool")) then
          let (th1,th2) = EQ_IMP_RULE th in
          (fl => [GEN_ALL th] | []) @ (canon true th1) @ (canon true th2) else
       if (is_forall w) then
           let vs,body = strip_forall w in
           let fvs = thm_frees th in
           let vfn = \l. variant (l @ fvs) in
           let nvs = itlist (\v nv. let v' = vfn nv v in (v'.nv)) vs [] in
               canon fl (SPECL nvs th) else
       if fl then [GEN_ALL th] else [] in
    \th. (let args = map (not_elim o SPEC_ALL) (CONJUNCTS (SPEC_ALL th)) in
          let imps = flat (map (map GEN_ALL o (uncurry canon)) args) in
              assert ($not o null) imps)
         ? failwith `RES_CANON: no implication is derivable from input thm.`;;



% --------------------------------------------------------------------- %
% Definitions of the primitive:						%
%									%
% IMP_RES_THEN: Resolve all assumptions against an implication.		%
%									%
% The definition uses two auxiliary (local)  functions:			%
%									%
%     MATCH_MP     : like the built-in version, but doesn't use GSPEC.	%
%     RESOLVE_THEN : repeatedly resolve an implication			%
% 									%
% This version deleted for HOL version 1.12   		 [TFM 91.01.17]	%
%									%
% begin_section IMP_RES_THEN;;						%
%									%
% let MATCH_MP impth =							%
%     let sth = SPEC_ALL impth in					%
%     let pat = fst(dest_imp(concl sth)) in				%
%     let matchfn = match pat in					%
%        (\th. MP (INST_TY_TERM (matchfn (concl th)) sth) th);;		%
% 									%
% letrec RESOLVE_THEN antel ttac impth : tactic =			%
%        let answers = mapfilter (MATCH_MP impth) antel in		%
%            EVERY (mapfilter ttac answers) THEN			%
%           (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));;	%
% 									%
% let IMP_RES_THEN ttac impth =						%
%     ASSUM_LIST (\asl. 						%
%      EVERY (mapfilter (RESOLVE_THEN asl ttac) (RES_CANON impth))) ? 	%
%     failwith `IMP_RES_THEN`;;						%
%									%
% IMP_RES_THEN;;							%
% 									%
% end_section IMP_RES_THEN;;						%
% 									%
% let IMP_RES_THEN = it;;						%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Definition of the primitive:						%
%									%
% IMP_RES_THEN: Resolve all assumptions against an implication.		%
%									%
% The definition uses an auxiliary (local) function, MATCH_MP, which is %
% just like the built-in version, but doesn't use GSPEC.		%
% 									%
% New implementation for version 1.12: fails if no MP-consequences can  %
% be drawn, and does only one-step resolution.		[TFM 90.12.07]  %
% --------------------------------------------------------------------- %

begin_section resolution_ttcls;;

let MATCH_MP impth =
    let sth = SPEC_ALL impth in
    let matchfn = match (fst(dest_neg_imp(concl sth))) in
       \th. NOT_MP (INST_TY_TERM (matchfn (concl th)) sth) th;;

% --------------------------------------------------------------------- %
% check st l : Fail with st if l is empty, otherwise return l.		%
% --------------------------------------------------------------------- %

let check st l = (null l => failwith st | l);;

% --------------------------------------------------------------------- %
% IMP_RES_THEN  : Resolve an implication against the assumptions.	%
% --------------------------------------------------------------------- %


let IMP_RES_THEN ttac impth =
    let ths = RES_CANON impth ? failwith `IMP_RES_THEN: no implication` in
    ASSUM_LIST 
     \asl. let l = itlist (\th.append (mapfilter (MATCH_MP th) asl)) ths [] in
           let res = check `IMP_RES_THEN: no resolvents ` l in
           let tacs = check `IMP_RES_THEN: no tactics` (mapfilter ttac res) in
               EVERY tacs;;

% --------------------------------------------------------------------- %
% RES_THEN    : Resolve all implicative assumptions against the rest.	%
% --------------------------------------------------------------------- %

let RES_THEN ttac (asl,g) =
    let as = map ASSUME asl in
    let ths = itlist append (mapfilter RES_CANON as) [] in
    let imps = check `RES_THEN: no implication` ths in
    let l = itlist (\th.append (mapfilter (MATCH_MP th) as)) imps [] in
    let res = check `RES_THEN: no resolvents ` l in
    let tacs = check `RES_THEN: no tactics` (mapfilter ttac res) in
        EVERY tacs (asl,g);;

% --------------------------------------------------------------------- %
% Export IMP_RES_THEN and RES_THEN outside of the section.		%
% --------------------------------------------------------------------- %
(IMP_RES_THEN,RES_THEN);;
end_section resolution_ttcls;;
let (IMP_RES_THEN,RES_THEN) = it;;

% --------------------------------------------------------------------- %
% Definition of the standard resolution tactics IMP_RES_TAC and RES_TAC %
%									%
% The function SA is like STRIP_ASSUME_TAC, except that it does not     %
% strip off existential quantifiers. And ST is like STRIP_THM_THEN, 	%
% except that it also does not strip existential quantifiers.		%
%									%
% Old version: deleted for HOL version 1.12 		 [TFM 91.01.17]	%
%									%
% let (IMP_RES_TAC,RES_TAC) = 						%
%    let ST = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in		%
%    let SA = (REPEAT_TCL ST) CHECK_ASSUME_TAC in			%
%        (IMP_RES_THEN SA, RES_THEN SA);;				%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% New versions of IMP_RES_TAC and RES_TAC: repeatedly resolve, and then %
% add FULLY stripped, final, result(s) to the assumption list.		%
% --------------------------------------------------------------------- %

let IMP_RES_TAC th g =
    IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g ? ALL_TAC g;;

let RES_TAC g =
    RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g ? ALL_TAC g;;

% --------------------------------------------------------------------- %
% Used to be for compatibility with the old system. 			%
% Deleted: TFM 90.04.24							%
% let HOL_IMP_RES_THEN = IMP_RES_THEN					%
% and HOL_RES_THEN     = RES_THEN;;					%
% --------------------------------------------------------------------- %


% --------------------------------------------------------------------- %
% MATCH_MP_TAC: Takes a theorem of the form 				%
%									%
%       |- !x1..xn. A ==> !y1 ... ym. B 				%
% 									%
% and matches B to the goal, reducing it to the subgoal consisting of 	%
% some existentially-quantified instance of A:				%
%									%
%      !v1...vi. B							%
% ======================= MATCH_MP_TAC |- !x1...1n. A ==> !y1...ym. B   %
%      ?z1...zp. A							%
% 									%
% where {z1,...,zn} is the subset of {x1,...,xn} whose elements to not  %
% appear free in B.							%
%									%
% Added: TFM 88.03.31							%
% Revised: TFM 91.04.20							%
%									%
% Old version:								%
%									%
% let MATCH_MP_TAC thm:tactic (gl,g) =					%
%     let imp = ((PART_MATCH (snd o dest_imp) thm) g) ? 		%
% 	       failwith `MATCH_MP_TAC` in				%
%     ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl));;	%
% --------------------------------------------------------------------- %

let MATCH_MP_TAC : thm_tactic =
    let efn v (tm,th) =
        let ntm = mk_exists(v,tm) in ntm,CHOOSE (v, ASSUME ntm) th in
    \thm. let gvs,imp = strip_forall (concl thm) in
          let ant,cnc = dest_neg_imp imp ?
                        failwith `MATCH_MP_TAC: not an implication` in
          let cvs,con = strip_forall cnc in
          let th1 = SPECL cvs (UNDISCH (SPECL gvs thm)) in
          let vs,evs = partition (C free_in con) gvs in
          let th2 = uncurry DISCH (itlist efn evs (ant,th1)) in
          \A,g. let vs,gl = strip_forall g in
	        let ins = match con gl ? failwith `MATCH_MP_TAC: no match` in
                let ith = INST_TY_TERM ins th2 in
                let ant = fst(dest_neg_imp(concl ith)) in
                let gth = GENL vs (UNDISCH ith) ?
                               failwith `MATCH_MP_TAC: generalized var(s)` in
                    ([A,ant], \thl. NOT_MP (DISCH ant gth) (hd thl));;
