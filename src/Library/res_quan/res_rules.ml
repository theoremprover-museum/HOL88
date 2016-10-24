% ===================================================================== %
% FILE: res_rules.ml	    DATE: 1 Aug 92	BY: Wai Wong		%
% This file contains rules, conversions and tactics supporting		%
% restricted quantifiers.   	    					%
% ===================================================================== %

let rtheory = `res_quan`;;

% ===================================================================== %
% Syntactic operations on restricted quantifications.                   %
% These ought to be generalised to all kinds of restrictions,           %
% but one thing at a time.                                              %
% --------------------------------------------------------------------- %

let (mk_resq_forall,mk_resq_exists,mk_resq_select,mk_resq_abstract) =
    let mk_resq_quan cons s =
      \(x,t1,t2) .
        let ty = type_of x in
    	let predty = mk_type(`fun`,[ty;bool_ty]) in
        let resty = mk_type(`fun`,[predty; mk_type(`fun`,[predty;bool_ty])]) in
    	    mk_comb(mk_comb(mk_const(cons,resty),t1),mk_abs(x,t2))
            ? failwith s  in
    ((mk_resq_quan `RES_FORALL` `mk_resq_forall`),
     (mk_resq_quan `RES_EXISTS` `mk_resq_exists`),
     (mk_resq_quan `RES_SELECT` `mk_resq_select`),
     (mk_resq_quan `RES_ABSTRACT` `mk_resq_abstract`));;

let list_mk_resq_forall (ress,body) =
   (itlist (\(v,p) b.mk_resq_forall(v,p,b)) ress body) 
   ? failwith `list_mk_resq_forall`;;

let list_mk_resq_exists (ress,body) =
   (itlist (\(v,p) b.mk_resq_exists(v,p,b)) ress body) 
   ? failwith `list_mk_resq_exists`;;

let (dest_resq_forall,dest_resq_exists,dest_resq_select,dest_resq_abstract) =
    let dest_resq_quan cons s =
    let check = assert (\c. fst(dest_const c) = cons) in
    \tm. (let ((_,c1),(c2,c3)) = (((check # I) o dest_comb) # dest_abs) 
                                 (dest_comb tm) in
               (c2,c1,c3)) ? failwith s in
    ((dest_resq_quan `RES_FORALL` `dest_resq_forall`),
     (dest_resq_quan `RES_EXISTS` `dest_resq_exists`),
     (dest_resq_quan `RES_SELECT` `dest_resq_select`),
     (dest_resq_quan `RES_ABSTRACT` `dest_resq_abstract`)) ;;

letrec strip_resq_forall fm =
    (let bv,pred,body = dest_resq_forall fm in
     let prs, core = strip_resq_forall body in
     (bv, pred).prs, core)
    ? [],fm;;

letrec strip_resq_exists fm =
    (let bv,pred,body = dest_resq_exists fm in
     let prs, core = strip_resq_exists body in
     (bv, pred).prs, core)
    ? [],fm;;

let is_resq_forall = can dest_resq_forall;;
let is_resq_exists = can dest_resq_exists;;
let is_resq_select = can dest_resq_select;;
let is_resq_abstract = can dest_resq_abstract;;


% ===================================================================== %
% Derived rules    	    	    					%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Rule to strip off a restricted universal quantification.              %
%                                                                       %
%    A |- !x :: P. t                                                    %
%   -------------------  RESQ_SPEC "x'"                                  %
%    A, P x' |- t                                                       %
%                                                                       %
% --------------------------------------------------------------------- %

let RESQ_SPEC =
    let dthm = definition `bool` `RES_FORALL` in
  \v' th.
    (let v,P,tm = dest_resq_forall (concl th) in
     BETA_RULE (UNDISCH_ALL (ISPEC v'
     (EQ_MP (ISPECL[P;mk_abs(v,tm)] dthm) th))))
    ?\s failwith (`RESQ_SPEC `^s);;

% --------------------------------------------------------------------- %
% RESQ_SPECL : term list -> thm -> thm					%
% An analogy to SPECL as RESQ_SEPC to SPEC.				%
% Instatiate a list of restricted universal quantifiers.		%
% --------------------------------------------------------------------- %
let RESQ_SPECL vs th = rev_itlist RESQ_SPEC vs th;;

% --------------------------------------------------------------------- %
% RESQ_SPEC_ALL : thm -> thm						%
% An analogy to SPEC_ALL as RESQ_SEPC to SPEC.				%
% Strip a list of restricted universal quantifiers.			%
% --------------------------------------------------------------------- %
let RESQ_SPEC_ALL th =
    let vs = map fst (fst (strip_resq_forall (concl th))) in
 rev_itlist RESQ_SPEC vs th;;

% --------------------------------------------------------------------- %
% GQSPEC : tm -> thm -> thm						%
% Instantiate a universal quantifier which may be either an ordinary	%
% or restricted.							%
% --------------------------------------------------------------------- %
let GQSPEC = \tm th.
    if (is_resq_forall (concl th)) then RESQ_SPEC tm th
    else ISPEC tm th;;

% --------------------------------------------------------------------- %
% GQSPECL : term list -> thm -> thm					%
% Instantiate a list of universal quantifiers which may be a mixture	%
% of ordinary or restricted in any order.				%
% --------------------------------------------------------------------- %
let GQSPECL tms th = rev_itlist GQSPEC tms th;;

% --------------------------------------------------------------------- %
% GQSPEC_ALL : thm -> thm						%
% Strip a list of universal quantifiers which may be a mixture		%
% of ordinary or restricted in any order.				%
% --------------------------------------------------------------------- %
letrec GQSPEC_ALL th =
    if (is_resq_forall (concl th))
    then (let v = fst (dest_resq_forall (concl th)) in
    	  GQSPEC_ALL (RESQ_SPEC v th))
    else if (is_forall (concl th))
    then (let v = fst (dest_forall (concl th)) in
    	  GQSPEC_ALL (SPEC v th))
    else th ;;

% --------------------------------------------------------------------- %
% Rule to strip off a restricted universal quantification.              %
% but keeping the implication.	    					%
%                                                                       %
%    A |- !x :: P. t                                                    %
%   -------------------  RESQ_HALF_SPEC                                  %
%    A |- !x. P x ==> t                                                 %
%                                                                       %
% --------------------------------------------------------------------- %
let RESQ_HALF_SPEC =
    let dthm = definition `bool` `RES_FORALL` in
  \th.
    (let v,P,tm = dest_resq_forall (concl th) in
     CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
     (EQ_MP (ISPECL[P;mk_abs(v,tm)] dthm) th))
    ?\s failwith (`RESQ_HALF_SPEC `^s);;

% --------------------------------------------------------------------- %
% Rule to strip off a restricted existential quantification.            %
%                                                                       %
%    A |- ?x :: P. t                                                    %
%   --------------------- RESQ_HALF_EXISTS                               %
%    A |- ?x. P x /\ t[x]                                               %
%                                                                       %
% --------------------------------------------------------------------- %
let RESQ_HALF_EXISTS =
    let dthm = definition `bool` `RES_EXISTS` in
  \th.
    (let v,P,tm = dest_resq_exists (concl th) in
     CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
     (EQ_MP (ISPECL[P;mk_abs(v,tm)] dthm) th))
    ?\s failwith (`RESQ_HALF_EXISTS `^s);;

% --------------------------------------------------------------------- %
% Rule to introduce a restricted universal quantification.              %
%                                                                       %
%    A |- t [x]                                                         %
%   ------------------  RESQ_GEN ("x", "P")                                %
%    A |- !x :: P. t                                                    %
%                                                                       %
% --------------------------------------------------------------------- %

let RESQ_GEN =
    let dthm = definition `bool` `RES_FORALL` in
    let REV_MATCH_EQ_MP = \th1 th2. MATCH_MP (snd (EQ_IMP_RULE th1)) th2 in
  \(v,P) th.
    (let P' = mk_comb(P,v) in
 %    if not(mem P' (hyp th)) then failwith `predicate not in hypotheses`
     else%
      let B' = mk_abs(v,(concl th)) in
      let th1 = CONV_RULE (DEPTH_CONV BETA_CONV)(ISPECL[P;B']dthm) in
      REV_MATCH_EQ_MP th1 (GEN v
    	(CONV_RULE(DEPTH_CONV BETA_CONV)(DISCH P' th))))
    ?\s failwith (`RESQ_GEN `^s);;

let RESQ_GENL vps th = itlist RESQ_GEN vps th;;

let RESQ_GEN_ALL =
    let dest_p tm = 
    	let p,v = dest_comb tm in
    	if not(is_var v) then fail else (v,p) in
    \th. itlist RESQ_GEN (mapfilter dest_p (hyp th)) th;;

% --------------------------------------------------------------------- %
% RESQ_MATCH_MP : thm -> thm -> thm  					%
% RESQ_MATCH_MP (|- !x :: P. Q[x]) (|- P x') returns |- Q[x']  	    	%
% --------------------------------------------------------------------- %

let RESQ_MATCH_MP th1 th2 =
    MATCH_MP (RESQ_HALF_SPEC th1) th2;;

% ===================================================================== %
% Tactics   	    	    	    					%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Tactic to strip off a restricted universal quantification.            %
%                                                                       %
%    A ?- !x :: P. t                                                    %
%   ===================  RESQ_HALF_GEN_TAC                              %
%    A ?- !x. P x ==> t                                                 %
%                                                                       %
%    A ?- !x :: P. t                                                    %
%   ===================  RESQ_GEN_TAC                                   %
%    A, P x ?- ==> t                                                    %
%                                                                       %
% --------------------------------------------------------------------- %

let RESQ_HALF_GEN_TAC, RESQ_GEN_TAC =
    let RESQ_FORALL = definition `bool` `RES_FORALL` in
    let gtac tac =
  \(asl, w).
    let var,cond,body = dest_resq_forall w in
    let thm = RIGHT_CONV_RULE (GEN_ALPHA_CONV var)
        (ISPECL [cond; mk_abs(var,body)] RESQ_FORALL) in
     (SUBST1_TAC thm THEN tac) (asl, w) in
    (gtac BETA_TAC), (gtac (GEN_TAC THEN BETA_TAC THEN DISCH_TAC));;

% --------------------------------------------------------------------- %
% Tactic to strip off a universal quantification which may be either	%
% ordinary ore restricted, i.e. a generic version of GEN_TAC and 	%
% RESQ_GEN_TAC.            						%
% --------------------------------------------------------------------- %
let GGEN_TAC (asl,gl) =
    if (is_forall gl) then GEN_TAC (asl, gl)
    else if (is_resq_forall gl) then (RESQ_GEN_TAC) (asl,gl)
    else failwith `GGEN_TAC: goal is not (restricted) universally quantified`;;

% --------------------------------------------------------------------- %
% Tactic to strip off a restricted existential quantification.          %
%                                                                       %
%    A ?- ?x :: P. t                                                    %
%   ===================  RESQ_EXISTS_TAC "x'"                             %
%    A ?-  P x' /\ t                                                    %
%                                                                       %
% --------------------------------------------------------------------- %

let RESQ_EXISTS_TAC tm =
    let RESQ_EXISTS = definition `bool` `RES_EXISTS` in
  \(asl, w).
    let var,cond,body = dest_resq_exists w in
    let thm = RIGHT_CONV_RULE (GEN_ALPHA_CONV var)
        (ISPECL [cond; mk_abs(var,body)] RESQ_EXISTS) in
     (SUBST1_TAC thm THEN EXISTS_TAC tm THEN BETA_TAC) (asl, w);;

% --------------------------------------------------------------------- %
% Resolution using the supplied theorem which contains restricted 	%
% quantifier. This is first converted to an implication then the normal %
% resolution tactic is applied.	    					%
% --------------------------------------------------------------------- %

begin_section resolution_ttcls;;

let MATCH_MP impth =
    let sth = SPEC_ALL impth in
    let matchfn = match (fst(dest_imp(concl sth))) in
       \th. MP (INST_TY_TERM (matchfn (concl th)) sth) th;;

% --------------------------------------------------------------------- %
% check st l : Fail with st if l is empty, otherwise return l.		%
% --------------------------------------------------------------------- %

let check st l = (null l => failwith st | l);;

% --------------------------------------------------------------------- %
% check_res th : Fail if th is not in the form:				%
% !x0 ... xn. !y :: P. t   otherwise, it returns the following theorem	%
% !x0 ... xn y. P ==> t.    	    					%
% --------------------------------------------------------------------- %

let check_res th = 
    if is_forall (concl th) then 
    	GEN_ALL(RESQ_HALF_SPEC(SPEC_ALL th))
    else (RESQ_HALF_SPEC th)
    ?failwith `not restricted forall`;;

% --------------------------------------------------------------------- %
% RESQ_IMP_RES_THEN  : Resolve a restricted quantified theorem against	%
% the assumptions.	    	    					%
% --------------------------------------------------------------------- %

let RESQ_IMP_RES_THEN ttac resth =
    (let th = check_res resth in
     IMP_RES_THEN ttac th) ?\s failwith(`RESQ_IMP_RES_THEN `^s);;

% --------------------------------------------------------------------- %
% RESQ_RES_THEN : Resolve all restricted universally quantified 	%
% assumptions against the rest.	    					%
% --------------------------------------------------------------------- %

let RESQ_RES_THEN ttac (asl,g) =
    let as = map ASSUME asl in
    let ths = mapfilter check_res as in
    let imps = check `RESQ_RES_THEN: no restricted quantification ` ths in
    let l = itlist (\th.append (mapfilter (MATCH_MP th) as)) imps [] in
    let res = check `RESQ_RES_THEN: no resolvents ` l in
    let tacs = check `RESQ_RES_THEN: no tactics` (mapfilter ttac res) in
        EVERY tacs (asl,g);;

% --------------------------------------------------------------------- %
% Export RESQ_IMP_RES_THEN and RESQ_RES_THEN outside of the section.	%
% --------------------------------------------------------------------- %
(RESQ_IMP_RES_THEN,RESQ_RES_THEN);;
end_section resolution_ttcls;;
let (RESQ_IMP_RES_THEN,RESQ_RES_THEN) = it;;

let RESQ_IMP_RES_TAC th g =
    RESQ_IMP_RES_THEN (REPEAT_GTCL RESQ_IMP_RES_THEN STRIP_ASSUME_TAC) th g
    ? ALL_TAC g;;

let RESQ_RES_TAC g =
    RESQ_RES_THEN (REPEAT_GTCL RESQ_IMP_RES_THEN STRIP_ASSUME_TAC) g ? ALL_TAC g;;

% ===================================================================== %
% Conversions		    	    					%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% If conversion c maps term "\i.t1" to theorem |- (\i.t1) = (\i'.t1'),  %
% then RF_BODY_CONV c "!i :: P. t1" returns the theorem                 %
%     |- (!i :: P. t1) = (!i' :: P. t1')                                %
%                                                                       %
% If conversion c maps term "t1" to the theorem |- t1 = t1',            %
% then RF_CONV c "!i :: P. t1" returns the theorem                      %
%     |- (!i :: P. t1) = (!i :: P. t1')                                 %
% --------------------------------------------------------------------- %

let LHS_CONV = RATOR_CONV o RAND_CONV;;
let RHS_CONV = RAND_CONV;;
let BOTH_CONV c = (LHS_CONV c THENC RHS_CONV c);;
let LEFT_THENC_RIGHT c1 c2 = (LHS_CONV c1 THENC RHS_CONV c2);;

let RF_BODY_CONV = RAND_CONV;;
let RF_PRED_CONV = (RATOR_CONV o RAND_CONV);;
let RF_CONV = (RAND_CONV o ABS_CONV);;
let PRED_THENC_BODY c1 c2 = 
   (((RATOR_CONV o RAND_CONV) c1) THENC ((RAND_CONV o ABS_CONV) c2));;

% --------------------------------------------------------------------- %
% RESQ_FORALL_CONV "!x :: P. t[x]"   					%
%     |- !x :: P. t[x] = !x. P x ==> t[x]   	    			%
% --------------------------------------------------------------------- %

let RESQ_FORALL_CONV =
    let dthm = definition `bool` `RES_FORALL` in
  \tm.
    (let (var,pred,t) = dest_resq_forall tm in
    RIGHT_CONV_RULE ((GEN_ALPHA_CONV var) THENC
      (ONCE_DEPTH_CONV BETA_CONV))(ISPECL [pred;mk_abs(var,t)] dthm))
    ? failwith `RESQ_FORALL_CONV`;;

% --------------------------------------------------------------------- %
% LIST_RESQ_FORALL_CONV "!x1 :: P1. ... !xn::Pn. t[x1...xn]"		%
% |- !x1 :: P1. ... !xn::Pn. t[x1...xn] = 				%
%    !x1...xn. P1 x1 ==> ... ==> Pn xn ==> t[x1...xn]  			%
% --------------------------------------------------------------------- %

let LIST_RESQ_FORALL_CONV tm =
    RIGHT_CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    (TOP_DEPTH_CONV RESQ_FORALL_CONV tm);;

% --------------------------------------------------------------------- %
% IMP_RESQ_FORALL_CONV "!x. P x ==> t[x]"				%
%     |- !x. P x ==> t[x] = !x :: P. t[x]    	    			%
% --------------------------------------------------------------------- %

let IMP_RESQ_FORALL_CONV =
    let dthm = definition `bool` `RES_FORALL` in
  \tm.
    (let var,(ante,t) = (I # dest_imp) (dest_forall tm) in
     let pred,v = dest_comb ante in
     if not(var = v) then failwith `term not in the correct form`
     else 
    SYM (RIGHT_CONV_RULE ((GEN_ALPHA_CONV var) THENC
      (ONCE_DEPTH_CONV BETA_CONV))(ISPECL [pred;mk_abs(var,t)] dthm)))
    ? failwith `IMP_RESQ_FORALL_CONV`;;

% --------------------------------------------------------------------- %
% RESQ_FORALL_AND_CONV "!i :: P. t1 /\ t2"  =                            %
%     |- (!i :: P. t1 /\ t2) = (!i :: P. t1) /\ (!i :: P. t2)           %
% --------------------------------------------------------------------- %

let RESQ_FORALL_AND_CONV =
    let rthm = theorem rtheory `RESQ_FORALL_CONJ_DIST` in
  \tm.
   (let (var,pred,conj) = dest_resq_forall tm in
    let (left,right) = dest_conj conj in
    let (left_pred,right_pred) = mk_abs(var,left), mk_abs(var,right) in
    let thm = ISPECL [pred; left_pred; right_pred] rthm in
    let c = LEFT_THENC_RIGHT
        (RF_CONV(BOTH_CONV BETA_CONV)) (BOTH_CONV(RF_CONV BETA_CONV)) in
    CONV_RULE c thm) ? failwith `RESQ_FORALL_AND_CONV`;;

% --------------------------------------------------------------------- %
% AND_RESQ_FORALL_CONV "(!i :: P. t1) /\ (!i :: P. t2)" =               %
%     |- (!i :: P. t1) /\ (!i :: P. t2) = (!i :: P. t1 /\ t2)           %
% --------------------------------------------------------------------- %

let AND_RESQ_FORALL_CONV =
    let rthm = theorem rtheory `RESQ_FORALL_CONJ_DIST` in
  \tm.
   (let conj1 = rand(rator tm) and conj2 = rand tm in
    let (var1,pred1,body1) = dest_resq_forall conj1 in
    let (var2,pred2,body2) = dest_resq_forall conj2 in
    let thm = SYM(
        ISPECL[pred1;mk_abs(var1,body1);mk_abs(var2,body2)] rthm) in
    let c = LEFT_THENC_RIGHT
        (BOTH_CONV(RF_CONV BETA_CONV)) (RF_CONV(BOTH_CONV BETA_CONV)) in
    CONV_RULE c thm) ? failwith `AND_RESQ_FORALL_CONV`;;

% --------------------------------------------------------------------- %
% RESQ_FORALL_SWAP_CONV "!i :: P. !j :: Q. R" =                         %
%     |- (!i :: P. !j :: Q. R) = (!j :: Q. !i :: P. R)                  %
% --------------------------------------------------------------------- %

let RESQ_FORALL_SWAP_CONV =
    let rthm = theorem rtheory `RESQ_FORALL_REORDER` in
  \tm.
   (let (i,P,body) = dest_resq_forall tm in
    let (j,Q,R) = dest_resq_forall body in
    let thm1 = ISPECL [P;Q;mk_abs(i, mk_abs(j, R))] rthm in
    % Reduce the two beta-redexes on either side of the equation. %
    let c1 = RF_CONV(RF_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV)) in
    let thm2 = CONV_RULE (LHS_CONV c1 THENC RHS_CONV c1) thm1 in
    % Rename the bound variables in the quantifications. %
    let c2 =
        LHS_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV j)) THENC
            RF_BODY_CONV(ALPHA_CONV i)) THENC
        RHS_CONV(RF_CONV(RF_BODY_CONV(ALPHA_CONV i)) THENC
            RF_BODY_CONV(ALPHA_CONV j)) in
    if i=j or free_in i Q or free_in j P then fail
    else CONV_RULE c2 thm2) ? failwith `RESQ_FORALL_SWAP`;;

% --------------------------------------------------------------------- %
% RESQ_EXISTS_CONV "?x::P. t" --> |- ?x::P. t = ?x. P x /\ t[x]         %
%                                                                       %
% --------------------------------------------------------------------- %
let RESQ_EXISTS_CONV =
    let dthm = definition `bool` `RES_EXISTS` in
  \tm'.
    (let v,P,tm = dest_resq_exists tm' in
     RIGHT_CONV_RULE ((ONCE_DEPTH_CONV BETA_CONV)THENC (GEN_ALPHA_CONV v))
     (ISPECL[P;mk_abs(v,tm)] dthm))
    ?\s failwith (`RESQ_EXISTS_CONV `^s);;


% --------------------------------------------------------------------- %
% RESQ_REWR_CANON : thm -> thm	    					%
% convert a theorem into a canonical form for COND_REWR_TAC		%
% --------------------------------------------------------------------- %

let RESQ_REWR_CANON = 
    COND_REWR_CANON o (CONV_RULE ((TOP_DEPTH_CONV RESQ_FORALL_CONV)));;


% --------------------------------------------------------------------- %
% RESQ_REWRITE1_TAC : thm_tactic					%
% RESQ_REWRITE1_TAC |- !x::P. u[x] = v[x]				%
% transforms the input restricted quantified theorem to implicative     %
% form then do conditional rewriting.					%
% --------------------------------------------------------------------- %

let RESQ_REWRITE1_TAC th' =
    let th = RESQ_REWR_CANON th' in
    COND_REWR_TAC search_top_down th;;

% --------------------------------------------------------------------- %
% RESQ_REWRITE1_CONV : thm list -> thm -> conv				%
% RESQ_REWRITE1_CONV thms thm tm	    				%
% The input theorem thm should be restricted quantified equational 	%
% theorem ie. the form suitable for RESQ_REWRITE_TAC. The input term tm %
% should be an instance of the left-hand side of the conclusion of thm.	%
% The theorem list thms should contains theorems matching the conditions%
% in the input thm. They are used to discharge the conditions. The 	%
% conditions which cannot be discharged by matching theorems will be 	%
% left in the assumption.   	    					%
% --------------------------------------------------------------------- %
let RESQ_REWRITE1_CONV thms th tm =
    let th' = CONV_RULE ((TOP_DEPTH_CONV RESQ_FORALL_CONV)
        THENC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) th in
    COND_REWRITE1_CONV thms th' tm;;

% ===================================================================== %
% Functions for making definition with restrict universal quantified	%
% variables.	    	    	    					%
% The auxiliary functions used here are taken from the system directly.	%
% --------------------------------------------------------------------- %

begin_section new_resq_def;;

% check that tm is a <varstruct> where:

   <varstruct> ::= <var> | (<varstruct>,...,<varstruct>)

  and that there are no repeated variables. Return list of variables.
 %

letrec check_varstruct tm =
 if is_var tm
  then [tm]
  else
  (let t1,t2 = (dest_pair tm ? failwith `bad varstruct`)
   in
   let l1 = check_varstruct t1
   and l2 = check_varstruct t2
   in
   if intersect l1 l2 = []
    then l1@l2
    else failwith `repeated variable in varstruct`);;


% check that tm is a <lhs> where:

   <lhs> ::= <var> | <lhs> <varstruct>

 and that no variables are repeated. Return list of variables.
%

letrec check_lhs tm =
 if is_var tm
 then [tm]
 if is_const tm
 then failwith(`attempt to redefine the constant ` ^
               (fst(dest_const tm)))
 if not(is_comb tm)
 then failwith`lhs not of form "x = ..." or "f x = ... "`
 else
 (let t1,t2 = dest_comb tm
  in
  let l1 = check_lhs t1
  and l2 = check_varstruct t2
  in
  if intersect l1 l2 = [] then l1@l2 else failwith `var used twice`);;

%  if "C ... = (...:ty)" then  (get_type "C ..." ty) gives the
   type of C.
%


letrec get_type left rightty =
 (if is_var left
  then rightty
  else get_type (rator left) ":^(type_of(rand left))->^rightty"
 ) ? failwith `bad lhs`;;

% --------------------------------------------------------------------- %
% RESQ_DEF_EXISTS_RULE "!x1::P1. ... !xn::Pn. 				%
%   C y x1 ... xn z = t[y,x1,...,xn,z]"	returns a theorem which is 	%
% suitable to be used in new_specification				%
% If there are free variables in Pi, then Skolem conversion will be 	%
% done, so the constant C will become C' m where m is free in Pi.	%
% --------------------------------------------------------------------- %

let RESQ_DEF_EXISTS_RULE tm =
    let gvars,tm' = strip_forall tm in
    let ress,(lh,rh) = ((I # dest_eq) o strip_resq_forall) tm'
    	    	       ? failwith `definition not an equation` in
    let leftvars = check_lhs lh and
        cty = get_type lh (type_of rh) and
    	rightvars = frees rh and
        resvars = map fst ress in
    let finpred = setify (flat (map (frees o snd) ress)) in
    let Const = hd leftvars in let cname = fst(dest_var Const) in
    if not(allowed_constant cname) then 
    	failwith (cname^` is not allowed as a constant name`)
    else if (mem Const resvars) then
    	failwith (cname^` is restrict bound`)
    else if not(forall (\x. mem x leftvars) resvars) then
    	failwith `restrict bound var not in lhs`
    else if not(set_equal(intersect
    	(union finpred leftvars) rightvars)rightvars) then
    	failwith`unbound var in rhs`
    else if mem(hd leftvars)rightvars then
    	failwith `recursive definitions not allowed`
    else if not(null(subtract (tyvars rh) (tyvars Const))) then
    	failwith (dest_vartype(hd(subtract (tyvars rh) (tyvars Const)))^
                  `an unbound type variable in definition`)
    else
     (let gl = list_mk_forall(finpred,mk_exists(Const,list_mk_resq_forall(ress,
    	list_mk_forall((subtract(tl leftvars) resvars), mk_eq(lh,rh))))) in
      let ex = list_mk_abs((tl leftvars), rh) in
      let defthm = PROVE(gl,
    	REPEAT GEN_TAC THEN EXISTS_TAC ex THEN BETA_TAC 
    	THEN REPEAT RESQ_GEN_TAC THEN REPEAT GEN_TAC THEN REFL_TAC) in
      if is_forall(concl defthm) then
    	CONV_RULE SKOLEM_CONV defthm
      else defthm )
    ?\s failwith(`RESQ_DEF_EXISTS_RULE:`^s);;

% --------------------------------------------------------------------- %
% new_gen_resq_definition flag (name, "!x1::P1. ... !xn::Pn. 		%
%   C y x1 ... xn z = t[y,x1,...,xn,z]")				%
% This makes a new constant definition via new_specification.		%
%  The definition is stored in the current theory under the give name.	%
%  flag specifies the syntactic status of the new constant. It should	%
%    be either `constant`, or `infix` or `binder`.			%
% --------------------------------------------------------------------- %

let new_gen_resq_definition flag (name, tm) =
 let def_thm = RESQ_DEF_EXISTS_RULE tm
 in
 let cname = (fst o dest_var o fst o dest_exists o concl) def_thm
 in
 new_specification name [flag,cname] def_thm;;

let new_resq_definition =  new_gen_resq_definition `constant`;;

let new_infix_resq_definition =  new_gen_resq_definition `infix`;;

let new_binder_resq_definition =  new_gen_resq_definition `binder`;;

(new_resq_definition, new_infix_resq_definition, new_binder_resq_definition);;
end_section new_resq_def;;

let (new_resq_definition,
     new_infix_resq_definition,
     new_binder_resq_definition) = it;;

