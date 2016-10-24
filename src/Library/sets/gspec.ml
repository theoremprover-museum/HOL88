% ===================================================================== %
% FILE		: gspec.ml						%
% DESCRIPTION   : Generalized set specification : {tm[xi...xn] | P}	%
%								        %
% REWRITTEN     : T Melham						%
% DATE		: 90.07.30						%
% ===================================================================== %

begin_section SET_SPEC_CONV;; 

% --------------------------------------------------------------------- %
% Local function: dest_tuple "t1,t2,...,tn" = [t1;t2;...;tnm]		%
% --------------------------------------------------------------------- %

letrec dest_tuple tm = 
       (let (x,y) = dest_pair tm in x.dest_tuple y) ? [tm];;

% --------------------------------------------------------------------- %
% Local function: MK_PAIR						%
%									%
% A call to:								%
% 									%
%     MK_PAIR "[x1;x2;...;xn]" "v:(ty1 # ty2 # ... # tyn)"		%
%									%
% returns:								%
%									%
%     |- v = FST v, FST(SND v), ..., SND(SND...(SND v))			%
% --------------------------------------------------------------------- %

letrec MK_PAIR vs v = 
       if (null (tl vs)) then (REFL v) else
       let vty = type_of v in
       let _,[ty1;ty2] = dest_type vty in
       let inst = SYM(SPEC v (INST_TYPE [ty1,":*";ty2,":**"] PAIR)) in 
       let FST,SND = dest_pair(rhs(concl inst)) in
       let thm = MK_PAIR (tl vs) SND and gv = genvar ty2 in
           SUBST [thm,gv] (mk_eq(v,mk_pair(FST,gv))) inst;;

% --------------------------------------------------------------------- %
% Local function: EXISTS_TUPLE_CONV					%
%									%
% A call to:								%
% 									%
%  EXISTS_TUPLE_CONV ["x1";...;"xn"] "?v. tm' = (\(x1,...,xn). tm) v	%  
%									%
% returns:								%
%									%
%  |- (?v. tm' = (\(x1,...,xn). tm) v ) = ?x1...xn. tm' = tm		%
% --------------------------------------------------------------------- %

let EXISTS_TUPLE_CONV =
    let EX (v,tm) th = EXISTS (mk_exists(v,subst [v,tm] (concl th)),tm) th and
        CH tm th = CHOOSE (tm,ASSUME (mk_exists(tm,hd(hyp th)))) th in
    let conv = RAND_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV) in
    \vs tm. let tup = end_itlist (curry mk_pair) vs in
            let v,body = dest_exists tm in
            let tupeq = MK_PAIR vs v in
            let asm1 = SUBST [tupeq,v] body (ASSUME body) in
            let comp = dest_tuple (rand(concl tupeq)) in
            let thm1 = itlist2 EX (vs,comp) asm1 in
            let imp1 = DISCH tm (CHOOSE (v,ASSUME tm) thm1) in
            let asm2 = ASSUME (subst [tup,v] body) in
            let thm2 = itlist CH vs (EXISTS (tm,tup) asm2) in
            let imp2 = DISCH (hd(hyp thm2)) thm2 in 
            let eq = IMP_ANTISYM_RULE imp1 imp2 in
	    let beta = conv (snd(strip_exists(rhs(concl eq)))) in
	        TRANS eq (itlist EXISTS_EQ vs beta);;

% --------------------------------------------------------------------- %
% Local function: PAIR_EQ_CONV.						%
%									%
% A call to PAIR_EQ_CONV "?x1...xn. a,b = c,T" returns:			%
%									%
%    |- (?x1...xn. a,T = b,c) = (?x1...xn. (a = b) /\ c)		%
% --------------------------------------------------------------------- %

let PAIR_EQ_CONV = 
    let EQT = el 1 (CONJUNCTS (SPEC "c:bool" EQ_CLAUSES)) in
    let PEQ = let inst = INST_TYPE [":bool",":**"] PAIR_EQ in
              let spec = SPECL ["a:*";"T";"b:*";"c:bool"] inst in
	          GENL ["a:*";"b:*";"c:bool"] (SUBS [EQT] spec) in
    \tm. let vs,body = strip_exists tm in
         let (a,T),(b,c) = (dest_pair # dest_pair) (dest_eq body) in
         let th = SPEC c (SPEC b (SPEC a (INST_TYPE [type_of a,":*"] PEQ))) in
	     itlist EXISTS_EQ vs th;;

% --------------------------------------------------------------------- %
% Local function: ELIM_EXISTS_CONV.					%
%									%
% ELIM_EXISTS_CONV "?x. (x = tm) /\ P[x]" returns:			%
%									%
%   |- (?x. x = tm /\ P[x]) = P[tm/x]					%
% --------------------------------------------------------------------- %

let ELIM_EXISTS_CONV tm = 
    let x,eq,body = (I # dest_conj)(dest_exists tm) in
    let asm1,asm2 = (SYM # I) (CONJ_PAIR (ASSUME (mk_conj(eq,body)))) in
    let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (SUBST [asm1,x] body asm2)) in
    let r = lhs eq in 
    let asm = subst [r,x] body in
    let imp2 = DISCH asm (EXISTS (tm,r) (CONJ (REFL r) (ASSUME asm))) in
        IMP_ANTISYM_RULE imp1 imp2;;


% --------------------------------------------------------------------- %
% Local function: PROVE_EXISTS.						%
%									%
% PROVE_EXISTS "?x. tm" (x not free in tm) returns:			%
%									%
%   |- ?x.tm = tm							%
% --------------------------------------------------------------------- %

let PROVE_EXISTS tm = 
    let x,body = dest_exists tm in
    let v = genvar (type_of x) in
    let imp1 = DISCH tm (CHOOSE (v,ASSUME tm) (ASSUME body)) in
    let imp2 = DISCH body (EXISTS (tm,v) (ASSUME body)) in
        IMP_ANTISYM_RULE imp1 imp2;;

% --------------------------------------------------------------------- %
% Internal function: list_variant					%
%									%
% makes variants of the variables in l2 such that they are all not in	%
% l1 and are all different.						%
% --------------------------------------------------------------------- %
letrec list_variant l1 l2 = 
       if (null l2) then [] else
           (let v = variant l1 (hd l2) in
	     (v.list_variant (v.l1) (tl l2)));;

% --------------------------------------------------------------------- %
% SET_SPEC_CONV: implements the axiom of specification for generalized	%
% set specifications.							%
%									%
% There are two cases:							%
%									%
%   1) SET_SPEC_CONV "t IN {v | p[v]}"    (v a variable, t a term)	%
% 									%
%      returns:								%
%									%
%      |- t IN {v | p[v]} = p[t/v]					%
%									%
%									%
%   2) SET_SPEC_CONV "t IN {tm[x1;...;xn] | p[x1;...xn]}"		%
%									%
%      returns:								%
%									%
%      |- t IN {tm[x1;...;xn] | p[x1;...xn]} 				%
%	     =								%
%         ?x1...xn. t = tm[x1;...;xn] /\ p[x1;...xn]			%
%									%
% Note that {t[x1,...,xm] | p[x1,...,xn]} means:			%
%									%
%   GGSPEC (\(x1,...,xn). (t[x1,...,xn], p[x1,...,xn]))			%
% --------------------------------------------------------------------- %


let SET_SPEC_CONV = 
    let check name = assert \tm.fst(dest_const tm) = name in
    let GSPEC = let th = theorem `sets` `GSPECIFICATION` in
    		let vs = fst(strip_forall(concl th)) in
		     GENL (rev vs) (SPECL vs th) in
    let RAconv = RAND_CONV o ABS_CONV in
    let conv = RAND_CONV(RAconv(RAND_CONV BETA_CONV)) in
    let conv2 = RAND_CONV (PAIR_EQ_CONV THENC PROVE_EXISTS) in
    letrec mktup tm = 
       (let x,(xs,res) = (I # mktup) (dest_abs(rand tm)) in ((x.xs),res)) ? 
       (let x,res =  (I # (fst o dest_pair)) (dest_abs tm) in [x],res) in
    \tm. (let _,[v;set] = (check `IN` # I) (strip_comb tm) in
          let _,f = (check `GSPEC` # I ) (dest_comb set) in
          let vty = type_of v and _,[uty;_] = dest_type(type_of f) in
	  let inst = SPEC v (INST_TYPE [vty,":*";uty,":**"] GSPEC) in
	  let vs,res = mktup f in 
	  if (forall ($not o (C free_in res)) vs) then
     	     let spec = CONV_RULE conv (SPEC f inst) in
     	     let thm1 = CONV_RULE conv2 spec in thm1 else
	  if (is_var res) then
	     let spec = CONV_RULE conv (SPEC f inst) in
	     let thm1 = CONV_RULE (RAND_CONV PAIR_EQ_CONV) spec in
	         TRANS thm1 (ELIM_EXISTS_CONV (rhs(concl thm1))) else
	  let spec = SPEC f inst in
	  let nvs = list_variant (frees v) vs in
	  let thm = EXISTS_TUPLE_CONV nvs (rhs(concl spec)) in
              TRANS spec (CONV_RULE (RAND_CONV PAIR_EQ_CONV) thm)) ? 
	  failwith `SET_SPEC_CONV`;;

% --------------------------------------------------------------------- %
% Bind SET_SPEC_CONV to "it".						%
% --------------------------------------------------------------------- %
SET_SPEC_CONV;;

end_section SET_SPEC_CONV;; 

% --------------------------------------------------------------------- %
% Save exported value of SET_SPEC_CONV.					%
% --------------------------------------------------------------------- %

let SET_SPEC_CONV = it;;
