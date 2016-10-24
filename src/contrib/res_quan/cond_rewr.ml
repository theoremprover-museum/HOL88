% ===================================================================== %
% FILE: cond_rewrite.ml	    	    					%
% AUTHOR: Wai Wong  	DATE: 10 Feb 1993				%
% CONDITIONAL REWRITING    	    					%
% --------------------------------------------------------------------- %

begin_section `COND_REWR_TAC`;;

let match_aa tm1 tm2 = [match tm1 tm2] ? [] ;;

let match_ok vs l =
    (((length l) = 1) & (null (snd(hd l))) &
     (let vlist = (map snd (fst(hd l))) in
     ((set_equal vs vlist) or (null vlist)))) ;;

letrec match_aal fvars ante =
    fun [] . []
    | (asm.asml) .
      let ml = match_aa ante asm in
      (if (match_ok (intersect fvars (frees ante)) ml)
       then [(fst(hd ml), asm)]
       else (match_aal fvars ante asml)) ;;

let subset s1 s2 = % s1 is a subset of s2 %
    set_equal s2 (union s1 s2);;

letrec match_asm fvars asm (ml,pl) =
    fun [] . (ml,pl)
    | (ante. antes) .
      let mlist = match_aal fvars ante asm in
      if null mlist then % no match %
        (match_asm fvars asm (ml,pl) antes)
      else (let ml' = fst (hd mlist) in
        if (subset ml ml')
        then % found consistant match %
          (match_asm fvars asm (ml', (ante.pl)) antes)
    	else if (subset ml' ml)
    	then % found consistant match %
    	  (match_asm fvars asm (ml, (ante.pl)) antes)
    	else %  inconsistant match %
    	  (match_asm fvars asm (ml, pl) antes)) ;;

% --------------------------------------------------------------------- %
% MATCH_SUBS1 = -   	    	    					%
% : thm ->  ((term # term) list # (type # type) list) list -> term list %
%  -> term list -> (term list # thm)	    	    			%
% MATCH_SUBS1 th m1 asm fvs = [tm1;...], th'   				%
% INPUTS:   	    	    	    					%
%  th is the theorem whose instances are required.			%
%  m1 is a list indicating an instantiation of th.			%
%  asm is a list of terms from which instances of the antecedents of th %
%   are found.	    	    	    					%
%  fvs is a set fo variables which do not appear in the lhs of the 	%
%   conclusion of th.	    	    					%
% RETURNS:  	    	    	    					%
%  tmi's are instances of the antecedents of th which do not appear in	%
%   the assumptions asm	    	    					%
%  th' is an instance of th resulting from substituting the matches in	%
%   m1 and the matches newly found in the assumption asm.		%
% --------------------------------------------------------------------- %

letrec var_cap th fv sv newvs =
    if not(is_forall (concl th)) then (newvs,th)
    else
    	(let v, b = dest_forall (concl th) in
    	 let nv,th' = (I # (GEN v)) (var_cap (SPEC v th) fv sv newvs) in
         if  (mem v fv) then
           (if (mem v sv) 
    	    then (let v' =  (variant (fv @ sv) v) in
    	      ((v' . nv), (CONV_RULE (GEN_ALPHA_CONV v') th')))
    	    else ((v . nv),th'))
    	 else (nv,th'));;

let MATCH_SUBS1 th fvs asm m1 =
    let afilter l fvs =
    	   mapfilter (\(a,a'). if null(intersect fvs (frees a)) 
    	         then fail else a') l in
    let subfrees = flat (map (frees o fst) (fst m1)) in
    let thm1 = INST_TYPE (snd m1) th in
%    let vars = fst(strip_forall (concl thm1)) in%
    let nv, thm1' = var_cap thm1 fvs subfrees [] in
    let thm2 = INST (fst m1) (SPEC_ALL thm1') in
    let antes = fst(strip_imp (snd (strip_forall(concl thm1')))) in
    let antes' = fst(strip_imp(concl thm2)) in
    if (null fvs)
    then %not free vars %
    	((subtract antes' (intersect antes' asm)), (UNDISCH_ALL thm2))
    else
       (let rlist = match_asm nv asm ([],[]) 
    	    (afilter (combine(antes, antes')) nv) in
    	let thm3 = UNDISCH_ALL (INST (fst rlist) thm2) in
    	let new_antes = hyp thm3 in
    	let sgl =  subtract new_antes (intersect new_antes asm) in
    	(sgl,thm3));;

let MATCH_SUBS th fvs asm mlist =
    let mll = map (MATCH_SUBS1 th fvs asm) mlist in
    let tms,thms = (flat # I) (split mll) in
    (((null tms) => [] | [(list_mk_conj (setify tms))]), thms);;

% --------------------------------------------------------------------- %
% COND_REWR_TAC = -	    	    					%
% : ((term -> term -> ((term # term) list # (type # type) list) list) ->%
%   thm_tactic)	    	    	    					%
% COND_REWR_TAC fn th	    	    					%
% fn is a search function which returns a list of matches in the format %
% of the list returned by the system function match.			%
% th is the theorem used for rewriting which should be in the following %
% form: |- !x1...xn y1..ym. P1[xi yj] ==> ...==> Pl[xi,yj] ==>		%
%   (Q[x1...xn] = R[xi yj])	    	    				%
% The variables x's appears in the lefthand side of the conclusion, and %
% the variables y's do not appear in the lefthand side of the conclusion%
% This tactic uses the search function fn to find any matches of Q in 	%
% the goal. It fails of no match is found, otherwise, it does:		%
% 1) instantiating the input theorem (using both the type and the	%
%    matched terms);	    	    					%
% 2) searching the assumptions to find any matches of the antecedents;	%
% 3) if there is any antecedents which does not has match in the 	%
%    assumptions, it is put up as a subgoal and also added to the 	%
%    assumption list of the original goal;				%
% 4) substitutes these instances into the goal. 			%
% Complications: if {yi} is not empty, step 2 will try to find instance %
% of Pk and instantiate the y's using these matches.			%
% --------------------------------------------------------------------- %

let COND_REWR_TAC fn th =
    \(asm,gl).
    	let vars,body = strip_forall (concl th) in
    	let antes,eqn = strip_imp body in
    	let tml,tmr = dest_eq eqn in
        let freevars = subtract vars (frees tml) in
    	let mlist = fn tml gl in
    	let sgl,thms = (MATCH_SUBS th freevars asm mlist) in
     if null mlist then failwith `no match`
     else if (null sgl)
     then ((SUBST_TAC thms) (asm,gl))
     else
       ((SUBGOAL_THEN (hd sgl) STRIP_ASSUME_TAC THENL[
         REPEAT CONJ_TAC; SUBST_TAC thms]) (asm,gl))
    ?\s failwith (`COND_REWR_TAC: `^s);;

COND_REWR_TAC;;
end_section `COND_REWR_TAC`;;

let COND_REWR_TAC = it;;

% --------------------------------------------------------------------- %
% search_top_down carries out a top-down left-to-right search for 	%
% matches of the term tm1 in the term tm2. 				%
% --------------------------------------------------------------------- %

letrec search_top_down tm1 tm2 =
    [(match tm1 tm2)] ?
     (if (is_comb tm2)
      then (let (rator,rand) = dest_comb tm2 in
    	    ((search_top_down tm1 rator) @ (search_top_down tm1 rand)))
      else if (is_abs tm2)
      then (let v,body = dest_abs tm2 in
    	    (search_top_down tm1 body))
      else []);;

%---------------------------------------------------------------%
% COND_REWR_CANON: thm -> thm	    				%
% converts a theorem to a canonical form for conditional	%
% rewriting. The input theorem should be in the following form:	%
% !x1 ... xn. P1[xi] ==> ... ==> !y1 ... ym. Pr[xi,yi] ==>	%
% (!z1 ... zk. u[xi,yi,zi] = v[xi,yi,zi])			%
% The output theorem is in the form accepted by COND_REWR_THEN.	%
% It first moves all universal quantifications to the outermost %
% level (possibly doing alpha conversion to avoid making free	%
% variables become bound, then converts any Pj which is itself 	%
% a conjunction using ANTE_CONJ_CONV repeatedly.			%
%---------------------------------------------------------------%

let COND_REWR_CANON th =
    letrec X_CONV conv tm =
        (conv ORELSEC
        (if is_imp tm then RAND_CONV (X_CONV conv) else NO_CONV)) tm in
    let rule = CONV_RULE(REPEATC(X_CONV ANTE_CONJ_CONV)) in
    let th' = CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV) th in
    let vars = fst(strip_forall (concl th')) in
    (GENL vars (rule(SPEC_ALL th')));;

%---------------------------------------------------------------%
% COND_REWRITE1_TAC : thm_tactic	    				%
%---------------------------------------------------------------%

let COND_REWRITE1_TAC th =
    COND_REWR_TAC search_top_down (COND_REWR_CANON th);;

% --------------------------------------------------------------------- %
% COND_REWR_CONV = 	    	    					%
% : ((term -> term -> ((term # term) list # (type # type) list) list) ->%
%   thm -> conv)    	    	    					%
% COND_REWR_CONV fn th tm  	    					%
% th is a theorem in the usual format for conditional rewriting.	%
% tm is a term on which conditinal rewriting is performed. 		%
% fn is a function attempting to match the lhs of the conclusion of th  %
% to the input term tm or any subterm(s) of it. The list returned by 	%
% this function is used to instantiate the input theorem. the resulting %
% instance(s) are used in a REWRITE_CONV to produce the final theorem.  %
% --------------------------------------------------------------------- %

let COND_REWR_CONV fn th tm =
    let vars,b = (strip_forall (concl th)) in
    let tm1 = lhs(snd(strip_imp b)) in
    let ilist = fn tm1 tm in
    if (null ilist) then failwith `no match`
    else (let thm1 = SPEC_ALL th in
    	let rlist = map (\l. UNDISCH_ALL(INST_TY_TERM l thm1)) ilist in
    	(REWRITE_CONV rlist tm))
     ?\s failwith (`COND_REWR_CONV: `^ s);;

% --------------------------------------------------------------------- %
% COND_REWRITE1_CONV : thm list -> thm -> conv				%
% COND_REWRITE1_CONV thms thm tm	    				%
% --------------------------------------------------------------------- %
let COND_REWRITE1_CONV thms th tm =
    let thm1 = COND_REWR_CONV search_top_down (COND_REWR_CANON th) tm in
    (itlist PROVE_HYP thms thm1);;
