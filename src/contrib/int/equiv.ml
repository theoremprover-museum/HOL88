%----------------------------------------------------------------------------%
% Defines a type of equivalence classes, and transfers a list of             %
% functions and theorems about the representatives over to the new type.     %
% It returns a list of the transferred theorems.                             %
%                                                                            %
% tyname   - desired name of new type                                        %
%                                                                            %
% equiv    - Theorem that R is an equivalence relation; in the form:         %
%               |- !x y. x R y = (R x = R y)                                 %
%                                                                            %
% fnlist   - list of triples: old function (term),                           %
%            new function name (string), infix flag (true = infix)           %
%                                                                            %
% welldefs - theorems asserting that the old functions are welldefined;      %
%            of the form |- (x1 R y1) /\ .. /\ (xn R yn) ==>                 %
%                             (f x1 .. xn) R (f y1 .. yn)                    %
%            where "R" becomes "=" for types other than the                  %
%            representing type.                                              %
%                                                                            %
% thlist   - List of theorems about the old functions                        %
%                                                                            %
% Restrictions:                                                              %
%                                                                            %
%  * R must be an equivalence relation over the whole type, no subsets.      %
%                                                                            %
%  * All original functions must be curried (as are the new ones).           %
%                                                                            %
%  * The theorems must have all variables bound by existential or            %
%    universal quantifiers.                                                  %
%                                                                            %
%  * The theorems must be obviously `well-defined', i.e. invariant under     %
%    subtitution [t/u] whenever |- t R u. Essentially "R" becomes "=" and    %
%    old functions become the new ones.                                      %
%                                                                            %
%  * All arguments/results of the representing type will be transferred      %
%    to the new type.                                                        %
%----------------------------------------------------------------------------%

let define_equivalence_type tyname equiv
                            fnlist welldefs thlist =
  let absname = `mk_`^tyname and repname = `dest_`^tyname in
  let eqv = (rator o rhs o rhs o snd o strip_forall o concl) equiv in
  let repty = (hd o snd o dest_type o type_of) eqv in
  let tydef =
    let rtm = "\c. ?x. c = ^eqv x" in
    new_type_definition(tyname,rtm,
      PROVE("?c. ^rtm c",
            BETA_TAC THEN MAP_EVERY EXISTS_TAC ["^eqv x"; "x:^repty"]
            THEN REFL_TAC)) in
  let tybij = BETA_RULE
    (define_new_type_bijections (tyname^`_tybij`) absname repname tydef) in
  let absty = mk_type(tyname,[])
  and abs,rep = ((I # rator) o dest_comb o lhs o snd o dest_forall o hd o
                 conjuncts o concl) tybij in

  let refl = PROVE
    ("!h. ^eqv h h",
     GEN_TAC THEN REWRITE_TAC[equiv] THEN REFL_TAC)
  and sym = PROVE
   ("!h i. ^eqv h i = ^eqv i h",
    REWRITE_TAC[equiv] THEN MATCH_ACCEPT_TAC EQ_SYM_EQ)
  and trans = PROVE
   ("!h i j. ^eqv h i /\ ^eqv i j ==> ^eqv h j",
    REPEAT GEN_TAC THEN REWRITE_TAC[equiv] THEN
    MATCH_ACCEPT_TAC EQ_TRANS) in

  let EQ_AP = PROVE
   ("!p q. (p = q) ==> ^eqv p q",
    REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC refl) in

  let EQ_WELLDEF = PROVE
   ("!x1 x2 y1 y2. (^eqv x1 x2) /\ (^eqv y1 y2) ==>
       ((^eqv x1 y1) = (^eqv x2 y2))",
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[sym]); ALL_TAC] THEN
  POP_ASSUM(CONJUNCTS_THEN2 (\th. DISCH_THEN(MP_TAC o CONJ th)) ASSUME_TAC)
  THEN DISCH_THEN(MP_TAC o MATCH_MP trans) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[sym]) THEN
  POP_ASSUM(\th. DISCH_THEN(MP_TAC o C CONJ th)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP trans)) in

  let DEST_MK_EQCLASS = PROVE
   ("!v. ^rep (^abs (^eqv v)) = ^eqv v",
    GEN_TAC THEN REWRITE_TAC[GSYM tybij] THEN
    EXISTS_TAC "v:^repty" THEN REFL_TAC) in

  let SAME_REP = PROVE
   ("!h i. ^eqv h i ==> ^eqv h ($@ (^eqv i))",
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC trans THEN
    EXISTS_TAC "i:^repty" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SELECT_AX THEN
    EXISTS_TAC "i:^repty" THEN MATCH_ACCEPT_TAC refl) in

  let SAME_RCR = PROVE
    ("!h i. (^eqv($@(^rep h)) = ^eqv($@(^rep i))) = (h = i)",
     let th = SYM(REWRITE_RULE[equiv](SPECL ["h:^repty";"h:^repty"] SAME_REP))
     and th2 = REWRITE_RULE[CONJUNCT1 tybij](SPEC "^rep h"(CONJUNCT2 tybij)) in
     let th3 = SPEC "i:^absty" (GEN "h:^absty" th2) in
     REPEAT GEN_TAC THEN MAP_EVERY CHOOSE_TAC [th2; th3] THEN
     ASM_REWRITE_TAC[th] THEN EVERY_ASSUM(SUBST1_TAC o SYM) THEN EQ_TAC THENL
      [DISCH_THEN(MP_TAC o AP_TERM abs); DISCH_THEN SUBST1_TAC] THEN
     REWRITE_TAC[tybij]) in

  let R_MK_COMB_TAC = FIRST
    [W(C $THEN (GEN_TAC THEN CONV_TAC
          (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o
       CONV_TAC o X_FUN_EQ_CONV o fst o dest_abs o lhs o snd);
     FIRST(map MATCH_MP_TAC (EQ_WELLDEF.welldefs)) THEN REPEAT CONJ_TAC;
     MK_COMB_TAC;
     MATCH_MP_TAC SAME_REP;
     MATCH_MP_TAC EQ_AP;
     FIRST (map MATCH_ACCEPT_TAC [refl; EQ_REFL])] in

  let EQC_FORALL_CONV tm =
    let v = fst(dest_forall tm) in
    let v' = (mk_var o (I # (K absty o assert(curry$= repty))) o dest_var) v in
    let th1 = GEN v' (SPEC "$@(^rep ^v')" (ASSUME tm)) in
    let tm' = concl th1 in
    let th2 = ASSUME tm' in
    let th3 = GEN v (SPEC "^abs (^eqv ^v)" th2) in
    let th4 = GEN_REWRITE_RULE (ONCE_DEPTH_CONV) [] [DEST_MK_EQCLASS] th3 in
    let tm'' = concl th4 in
    let peq = mk_eq(tm,tm'') in
    let th5 = PROVE(peq,REPEAT R_MK_COMB_TAC) in
    let th6 = EQ_MP(SYM th5) th4 in
    IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th6) in

  let EQC_EXISTS_CONV =
    let neg2 = TAUT_CONV "~(~x) = x" in
    REWR_CONV(SYM neg2) THENC
    RAND_CONV(NOT_EXISTS_CONV THENC EQC_FORALL_CONV) THENC
    NOT_FORALL_CONV THENC RAND_CONV(ABS_CONV(REWR_CONV neg2)) in

  letrec transconv tm =
    if is_abs tm then (mk_abs o (I # transconv) o dest_abs) tm
    else
      let (op,tms) = (I # map transconv) (strip_comb tm) in
      if mem op (map fst fnlist) & type_of tm = repty then
        "$@(^rep(^abs(^eqv ^(list_mk_comb(op,tms)))))"
      else if tms = [] then op
      else list_mk_comb(transconv op,tms) in

  let TRANSFORM_CONV tm =
    let th1 = DEPTH_CONV(EQC_FORALL_CONV ORELSEC EQC_EXISTS_CONV) tm in
    let tm1 = rhs(concl th1) in
    let th2 = PROVE
     (mk_eq(tm1,transconv tm1),
      REWRITE_TAC[DEST_MK_EQCLASS] THEN
      REPEAT R_MK_COMB_TAC) in
    TRANS th1 th2 in

  let define_fun =
    letrec dest_funtype ty =
      if ty = repty then [ty] else
      (let (_,[l;r]) = (assert(curry$=`fun`) # I) (dest_type ty) in
       [l]@(dest_funtype r)) ? [ty] in
    \(tm,fname,inf).
    let tyl = dest_funtype(type_of tm) in
    let ntyl = map (\ty. ty = repty => absty | ty) tyl in
    let rty = end_itlist (\t1 t2. mk_type(`fun`,[t1;t2])) ntyl in
    let args = map genvar (butlast ntyl) in
    let rargs = map (\tm. (type_of tm = absty) => "$@ (^rep ^tm)" | tm) args in
    let l = list_mk_comb(mk_var(fname,rty),args)
    and r =
      let r0 = list_mk_comb(tm,rargs) in
      (type_of r0 = repty) => "^abs (^eqv ^r0)" | r0 in
    (inf => new_infix_definition | new_definition)
       (fname,mk_eq(l,r)) in

  let newdefs = map define_fun fnlist in

  let newthms = map (REWRITE_RULE(map GSYM newdefs) o
                     REWRITE_RULE[equiv; SAME_RCR] o
                     CONV_RULE TRANSFORM_CONV) thlist in
  newthms;;
