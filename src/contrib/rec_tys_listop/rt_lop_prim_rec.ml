%=============================================================================%
%                               HOL 88 Version 2.1                            %
%                                                                             %
%     FILE NAME:        rt_lop_prim_rec.ml                                    %
%                       (altered prim_rec.ml)                                 %
%                                                                             %
%     DESCRIPTION:      Primitive recursive definitions on arbitrary recursive%
%                       types.  Assumes the type is defined by an axiom of    %
%                       the form proved by the recursive types package.       %
%                                                                             %
%                       See my Ph.D. thesis for details                       %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.08.23)                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987                                     %
%                                                                             %
% 23.03.93 - BtG - MODIFIED FOR USE IN DEFINING EXTENDED RECURSIVE TYPES      %
%=============================================================================%

% remove x satisfying p from l.... giving x and the thing and rest of l	%
letrec remove p l = 
       if (p(hd l)) then ((hd l), (tl l)) else
       (I # (\r. ((hd l) . r))) (remove p (tl l));;

begin_section prove_rec_fn_exists;;

% derive_existence_thm th tm						%
%									%
% If th is a rec type axiom and tm is a term giving a prim rec 		%
% definition, derive an existence theorem for doing the definition.	%
% The existence theorem has cases corresponding to those in tm and	%
% is suitably type-instantiated.					%
%									%
% E.g. Input								%
%									%
% |- !f0 f1 f2 e. ?! fn.						%
%    (!x0 x1 t t'. fn(C1 t x0 t' x1) = f0(fn t)(fn t')x0 x1 t t') /\	%
%    (!t. fn(C2 t) = f1(fn t)t) /\             				%
%    (!x. fn(C3 x) = f2 x) /\     					%
%     (fn C4 = e)							%
%									%
%  "(!n b. Fn n C4 b = ...) /\						%
%   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\			%
%   (!m x q. Fn m (C3 x) q = ...)"					%
%									%
% Output:								%
%									%
% |- !e f0 f2. ?fn.							%
%    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\					%
%    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 = 			%
%		       f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\	        %
%    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)			%
%									%
% Note: the g's are genvars	(so are e ... f2)			%

let derive_existence_thm th tm = 
    (let vars = map(genvar o type_of) (fst(strip_forall(concl th))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPECL vars th)) in
     let e_fn = fst(dest_exists (concl exists)) in
     let conjs = conjuncts tm in
     letrec splt l = 
	    if (is_var (hd l)) then 
	       (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	    if (is_const (hd l) or (is_comb (hd l))) then
	       [],(hd l),(tl l) else fail in
     let bv,Con,av =splt(snd(strip_comb(lhs(snd(strip_forall(hd conjs)))))) in
     let rhsfn = let cv = genvar(type_of Con) in
                 let r = rhs(snd(strip_forall(hd conjs))) in
                 list_mk_abs(cv. (bv @ av),r) in
     let th_inst = INST_TYPE (snd(match e_fn rhsfn)) exists in
     let get_c t = 
         let args = snd(strip_comb(lhs(snd(strip_forall t)))) in
	 let c = fst(strip_comb(find (\t.is_const t or is_comb t) args)) in
	 (if (is_const c) then c else fail) in
     let cs = map get_c conjs in
     let exl = CONJUNCTS (SELECT_RULE th_inst) in
     let fn = fst(dest_exists(concl th_inst)) in
     let same_c c cl = 
	 (c = fst(strip_comb(rand(lhs(snd(strip_forall(concl cl))))))) in
     letrec get_ths cs exl = 
            if (null cs) then [] else
	       (let (c,ex) = remove (same_c(hd cs)) exl in
	         (c.(get_ths (tl cs) ex))) in
     let ths = (get_ths cs exl) in
     let argvars = map (genvar o type_of) (bv @ av) in
     let ap_ths th = 
         let v = map (genvar o type_of) (fst(strip_forall(concl th))) in
	 let th1 = rev_itlist (C AP_THM) argvars (SPECL v th) in
	     (GENL (v @ argvars) th1) in
     let th1 = LIST_CONJ (map ap_ths ths) in
     let sel = mk_select(dest_exists (concl th_inst)) in
     GEN_ALL(EXISTS(mk_exists(fn,subst [fn,sel](concl th1)),sel)th1))?
     failwith `Can't derive existence theorem`;;


% mk_fn: make the function for the rhs of a clause in the existence thm	%
% 									%
% returns:  1) the function						%
%	    2) a list of variables that the clause should be SPECl	%
%	    3) a pre-done beta-conversion of the rhs.			%
%                                                                       %
% 05.04.93 - BtG - the internal function find has been altered to admit %
%                  the MAP of the function over a list argument.        %
%                                                                       %
%   cl - the generic, genvar'ed clause from the theorem characterizing  %
%        the datatype on which the function is being defined.           %
%   Fn - the function name that is being defined (or instantiated)      %
%   bv - before variables - arguments to Fn ?                           %
%   C  - the constructor term argument to Fn                            %
%   av - after variables - arguments to Fn ?                            %
%   r  - right hand side of definition                                  %
%                                                                       %
%   lcl - the recursive data type argument from cl                      %
%   lclvars - other arguments to the function from cl                   %
%   m - matches of C and lcl (match genvars with args to constructor)   %
%   cl' - body of cl with m substituted                                 %
%   nonrec - nonrecursive args (variables) in body of function rhs      %
%   rec - recursive arguments (applics.) in body of function rhs        %
%   recvars - genvars of rec (result of applying rec func.)             %
%   basepat - Fn applied to (genvar'd) before variables                 %
%                                                                       %
%   find t tm - returns a list of subterms of tm which match either     %
%               "^basepat ^t" or "MAP ^basepat ^t"                      %
%                                                                       %
%   do_subst (new,old) tm -                                             %
%                                                                       %
%   mk_substs (rc,rcv) t -                                              %
%     rc - rec term                                                     %
%     rcv - matching variable to rc                                     %
%     t - term in which to substitute (originally r above)              %
%                                                                       %
%     occs - find (type or type list arg) t                             %
%     args "Fn rec_inst v1 v2 ..." =                                    %
%                                                                       %
% The significant change here involves treating the recursive           %
% instances with a MAP of the recursive function differently            %
% from the simple application instances.  This shows up in mk_substs,   %
% which now retrieves the additional args to the recursive function     %
% being defined properly in this case.                                  %
% --------------------------------------------------------------------- %
let mk_fn (cl,(Fn,bv,C,av,r)) = 
    let lcl = hd(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let lclvars = tl(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let m = (fst(match lcl C)) @ combine((bv @ av),lclvars) in
    let cl' = subst m (snd(strip_forall cl)) in
    let nonrec = filter(is_var)(snd(strip_comb(rhs cl'))) in
    let rec = filter(is_comb)(snd(strip_comb(rhs cl'))) in
    let recvars = map (genvar o type_of) rec in
    let basepat = list_mk_comb(Fn,(map (genvar o type_of) bv)) in
    let find t =
        find_terms 
	(\tm. can (match "^basepat ^t") tm & 
	      (fst(strip_comb tm) = Fn) & (rand tm = t)) 
    and findm t =
        find_terms 
	(\tm. (can (match "MAP ^basepat ^t") tm &
               (fst(strip_comb(hd(snd(strip_comb tm)))) = Fn) &
               (rand tm = t))) in
   letrec do_subst (new,old) tm = 
    	   if (tm = old) then new else
	   if (is_abs tm) then 
	      mk_abs((I # do_subst(new,old))(dest_abs tm)) else
	   if (is_comb tm) then
	      let fn = do_subst(new,old) # do_subst(new,old) in
	      mk_comb((fn(dest_comb tm))) else tm in
    let mk_substs (rc,rcv) t = 
       if (is_const(fst(strip_comb rc))) then            % test for "MAP fn tm" %
       (let occs = findm (rand rc) t in
	let args tm = snd(strip_comb(rand(rator tm))) in

	let news = map (\tm. list_mk_comb(rcv,args tm)) occs in
	itlist do_subst (combine(news,occs)) t) else
       (let occs = find (rand rc) t in
	let args tm = snd(strip_comb (rator tm)) in

	let news = map (\tm. list_mk_comb(rcv,args tm)) occs in
	itlist do_subst (combine(news,occs)) t)  in
    let r' = itlist mk_substs (combine(rec,recvars)) r in
    let varsub = map (\v. (genvar (type_of v)),v) (recvars @ nonrec) in
    let fn = list_mk_abs(fst(split varsub),subst varsub r') in
    let specl =  map (\v.(fst(rev_assoc v m))? v) (fst(strip_forall cl)) in
    let beta = LIST_BETA_CONV(list_mk_comb(fn,snd(strip_comb(rhs cl')))) in
        (fn,specl,beta);;


% instantiate_existence_thm eth tm : instantiate eth to match tm 	%
%									%
% E.g. INPUT:								%
%									%
% |- !e f0 f2. ?fn.							%
%    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\					%
%    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 = 			%
%		       f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\	        %
%    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)			%
%									%
%									%
%  "(!n b. Fn n C4 b = ...) /\						%
%   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\			%
%   (!m x q. Fn m (C3 x) q = ...)"					%
%									%
% OUTPUT:								%
%  |- ?fn. (!n b. fn C4 n b = ...) /\					%
%          (!b n m t x t'. fn (C1 t' b t m) n x = ...) /\		%
% 	   (!m x q. fn (C3 x) m q = ...)				%

let instantiate_existence_thm eth tm = 
   (let cls = map (snd o strip_forall) (conjuncts tm) in
    letrec splt l = 
	   if (is_var (hd l)) then 
	      (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	   if (is_const (hd l) or (is_comb (hd l))) then
	      [],(hd l),(tl l) else fail in
    let dest tm = 
	let ((Fn,(bv,C,av)),r)=(((I # splt) o strip_comb) # I)(dest_eq tm) in
	    (Fn,bv,C,av,r) in
    let destcl = (map dest cls) in
    let ecls = conjuncts(snd(dest_exists(snd(strip_forall(concl eth))))) in
    let fns,spec,beta = (I # split)
			(split(map mk_fn (combine(ecls,destcl)))) in
    let ethsp = SPECL fns eth in
    let conjs = map (uncurry SPECL)
    		    (combine(spec,CONJUNCTS(SELECT_RULE ethsp))) in
    let rule (th1,th2) = CONV_RULE (RAND_CONV (REWR_CONV th1)) th2 in
    let th = LIST_CONJ (map (GEN_ALL o rule) (combine(beta,conjs))) in
    let fn = fst(dest_exists (concl ethsp)) and
        fsel = mk_select(dest_exists(concl ethsp)) in
        (EXISTS (mk_exists(fn,subst [fn,fsel] (concl th)),fsel) th))?
    failwith `Can't instantiate existence theorem`;;


% --------------------------------------------------------------------- %
% ETA_THM = |- !fn lst. MAP(\x. fn x)lst = MAP fn lst                   %
% --------------------------------------------------------------------- %
let ETA_THM =
  GEN_ALL (ONCE_DEPTH_CONV ETA_CONV "MAP(\x. (fn:*->**) x) lst");;


% prove_rec_fn_exists th tm						%
%									%
% Given 1) th, a recursion theorem (type axiom)				%
%	2) tm, the specification of a recursive function		%
%									%
% proves that such a function exists.					%

% Quantify the equations of the function spec.				%
let closeup tm = 
    let lvars t = subtract
		    (freesl(snd(strip_comb(lhs(snd (strip_forall t))))))
    		    (fst(strip_forall t)) in
    list_mk_conj(map (\tm.list_mk_forall(lvars tm,tm)) (conjuncts tm));;

% MJCG 17/1/89: added test for attempted redefinition of a constant and	%
% code to propagate failure message					%

let prove_rec_fn_exists th tm = 
   (let eth = derive_existence_thm th tm in
    let ith = instantiate_existence_thm eth tm in
    letrec get_avars tm  = 
	   if (is_var (rand tm)) then (get_avars (rator tm)) else
	      (snd(strip_comb (rator tm)),rand tm) in
    let cl = snd(strip_forall(hd(conjuncts tm))) in
    let fn = fst(strip_comb(lhs cl)) and
        av,tv = (map (genvar o type_of) # (genvar o type_of))
	        (get_avars (lhs cl)) in
    if is_const fn
     then failwith(fst(dest_const fn)^` previously defined`)
     else
      let goal = ([],mk_exists(fn,closeup tm)) in 
      let etac th = 
	  let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
          EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
      let fn_beta th (A,gl) = 
 	   let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
           let eabs = (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
	   let epat = list_mk_comb(eabs, map (genvar o type_of) (av @ [tv])) in
	   let tms = find_terms (\tm. can (match epat) tm) gl in
	   PURE_ONCE_REWRITE_TAC (map LIST_BETA_CONV tms) (A,gl) in
      GEN_ALL(TAC_PROOF(goal,
              STRIP_ASSUME_TAC ith THEN FIRST_ASSUM etac THEN
              REPEAT STRIP_TAC THEN FIRST_ASSUM fn_beta THEN
              PURE_ONCE_REWRITE_TAC [ ETA_THM ] THEN
              FIRST_ASSUM MATCH_ACCEPT_TAC)))?\tok
    failwith(`Can't solve recursion equation: `^tok);;

prove_rec_fn_exists;;

end_section prove_rec_fn_exists;;

let prove_rec_fn_exists = it;;

% Make a new recursive function definition.				%

%
Old code:

let new_recursive_definition infix_flag th name tm = 
    let thm = prove_rec_fn_exists th tm in
    if (is_forall (concl thm)) then 
	failwith `definition contains free vars` else
    let def = mk_eq(fst(dest_exists (concl thm)),
    		    mk_select(dest_exists (concl thm))) in
    let defn = if (infix_flag) then
	           new_infix_definition (name ^ `_DEF`,def) else
	           new_definition (name ^ `_DEF`,def) in 
        save_thm (name,SUBS [SYM defn] (SELECT_RULE thm));;

New code for HOL88:
%

let new_recursive_definition infix_flag th name tm = 
 let thm = prove_rec_fn_exists th tm 
 in
 new_specification
  name
  [(infix_flag=>`infix`|`constant`),
  ((fst o dest_var o fst o dest_exists o concl) thm)]
  thm;;



