%============================================================================%
% Various useful tactics, conversions etc.                                   %
%============================================================================%

timer true;;

%----------------------------------------------------------------------------%
% Applies a conversion to the left-hand operand of a binary operator         %
%----------------------------------------------------------------------------%

let LAND_CONV = RATOR_CONV o RAND_CONV;;

%----------------------------------------------------------------------------%
% Proves tautologies: handy for propositional lemmas                         %
%----------------------------------------------------------------------------%

let TAUT_CONV =
  let val w t = type_of t = ":bool" & can (find_term is_var) t & free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C $THEN (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o sort (uncurry free_in) o
    W(find_terms o val) o snd));;

%----------------------------------------------------------------------------%
% More concise way to get an AC rewrite lemma                                %
%----------------------------------------------------------------------------%

let AC thp tm = EQT_ELIM(AC_CONV thp tm);;

%----------------------------------------------------------------------------%
% GEN_PAIR_TAC - Like GEN_TAC but "pairs" the relevant variable              %
%----------------------------------------------------------------------------%

let GEN_PAIR_TAC =
  W($THEN GEN_TAC o SUBST1_TAC o SYM o
    C ISPEC PAIR o fst o dest_forall o snd);;

%----------------------------------------------------------------------------%
% MK_COMB_TAC - reduces ?- f x = g y to ?- f = g and ?- x = y                %
%----------------------------------------------------------------------------%

let MK_COMB_TAC : tactic (asl,w) =
  let l,r = dest_eq w in
  let l1,l2 = dest_comb l and r1,r2 = dest_comb r in
  ([(asl,mk_eq(l1,r1)); (asl,mk_eq(l2,r2))],end_itlist (curry MK_COMB));;

%----------------------------------------------------------------------------%
% BINOP_TAC - reduces "$op x y = $op u v" to "x = u" and "y = v"             %
%----------------------------------------------------------------------------%

let BINOP_TAC =
  MK_COMB_TAC THENL [AP_TERM_TAC; ALL_TAC];;

%----------------------------------------------------------------------------%
% SYM_CANON_CONV - Canonicalizes single application of symmetric operator    %
% Rewrites "so as to make fn true", e.g. fn = $<< or fn = curry$= "1" o fst  %
%----------------------------------------------------------------------------%

let SYM_CANON_CONV sym fn =
  REWR_CONV sym o assert ($not o fn o ((snd o dest_comb) # I) o dest_comb);;

%----------------------------------------------------------------------------%
% IMP_SUBST_TAC - Implicational substitution for deepest matchable term      %
%----------------------------------------------------------------------------%

let IMP_SUBST_TAC th :tactic (asl,w) =
  let tms = find_terms (can (PART_MATCH (lhs o snd o dest_imp) th)) w in
  let tm1 = hd (sort (uncurry free_in) tms) in
  let th1 = PART_MATCH (lhs o snd o dest_imp) th tm1 in
  let (a,(l,r)) = (I # dest_eq) (dest_imp (concl th1)) in
  let gv = genvar (type_of l) in
  let pat = subst[(gv,l)] w in
  ([(asl,a); (asl,subst[(r,gv)] pat)],
   \[t1;t2]. SUBST[(SYM(MP th1 t1),gv)] pat t2);;

%----------------------------------------------------------------------------%
% Tactic to introduce an abbreviation                                        %
%                                                                            %
% N.B. Just "ABBREV_TAC = CHOOSE_TAC o DEF_EXISTS_RULE" doesn't work if RHS  %
% has free variables.                                                        %
%----------------------------------------------------------------------------%

let ABBREV_TAC tm =
  let v,t = dest_eq tm in
  CHOOSE_THEN (\th. SUBST_ALL_TAC th THEN ASSUME_TAC th)
              (EXISTS(mk_exists(v,mk_eq(t,v)),t) (REFL t));;

%---------------------------------------------------------------%
% EXT_CONV "!x. f x = g x" = |- (!x. f x = g x) = (f = g)       %
%---------------------------------------------------------------%

let EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I # (mk_eq o (rator # rator) o dest_eq)) o dest_forall;;

%----------------------------------------------------------------------------%
%   (\x. s[x]) = (\y. t[y])                                                  %
%  ========================= ABS_TAC                                         %
%         s[x] = t[x]                                                        %
%----------------------------------------------------------------------------%

let ABS_TAC (asl,w) =
  (let l,r = dest_eq w in
   let v1,b1 = dest_abs l
   and v2,b2 = dest_abs r in
   let v = variant (freesl (w.asl)) v1 in
   let subg = mk_eq(subst[v,v1] b1,subst[v,v2] b2) in
   ([asl,subg],CONV_RULE(LAND_CONV(ALPHA_CONV v1)) o
               CONV_RULE(RAND_CONV(ALPHA_CONV v2)) o ABS v o hd))
  ? failwith `ABS_TAC`;;

%----------------------------------------------------------------------------%
% EQUAL_TAC - Strip down to unequal core (usually too enthusiastic)          %
%----------------------------------------------------------------------------%

let EQUAL_TAC = REPEAT(FIRST [AP_TERM_TAC; AP_THM_TAC; ABS_TAC]);;

%----------------------------------------------------------------------------%
% X_BETA_CONV "v" "tm[v]" = |- tm[v] = (\v. tm[v]) v                         %
%----------------------------------------------------------------------------%

let X_BETA_CONV v tm =
  SYM(BETA_CONV(mk_comb(mk_abs(v,tm),v)));;

%----------------------------------------------------------------------------%
% EXACT_CONV - Rewrite with theorem matching exactly one in a list           %
%----------------------------------------------------------------------------%

let EXACT_CONV =
  ONCE_DEPTH_CONV o FIRST_CONV o
  map (\t. K t o assert(curry$=(lhs(concl t))));;

%----------------------------------------------------------------------------%
% Rather ad-hoc higher-order fiddling conversion                             %
% |- (\x. f t1[x] ... tn[x]) = (\x. f ((\x. t1[x]) x) ... ((\x. tn[x]) x))   %
%----------------------------------------------------------------------------%

let HABS_CONV tm =
  let v,bod = dest_abs tm in
  let hop,pl = strip_comb bod in
  let eql = rev(map (X_BETA_CONV v) pl) in
  ABS v (itlist (C(curry MK_COMB)) eql (REFL hop));;

%----------------------------------------------------------------------------%
% autoload_definitions - Substitute for load_definitions                     %
%----------------------------------------------------------------------------%

let autoload_definitions thy =
  do map (\s. autoload_theory(`definition`,thy,fst s)) (definitions thy);;

%----------------------------------------------------------------------------%
% autoload_theorems - Substitute for load_theorems                           %
%----------------------------------------------------------------------------%

let autoload_theorems thy =
  do map (\s. autoload_theory(`theorem`,thy,fst s)) (theorems thy);;

%----------------------------------------------------------------------------%
% Expand an abbreviation                                                     %
%----------------------------------------------------------------------------%

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(curry$= s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;
