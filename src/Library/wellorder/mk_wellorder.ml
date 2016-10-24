%============================================================================%
% LIBRARY:     wellorder                                                     %
%                                                                            %
% DESCRIPTION: (1) Theorems about wosets, including recursion theorem        %
%              (2) Versions of the Axiom of Choice                           %
%                                                                            %
% AUTHOR:      John Harrison                                                 %
%              University of Cambridge Computer Laboratory                   %
%              New Museums Site                                              %
%              Pembroke Street                                               %
%              Cambridge CB2 3QG                                             %
%              England.                                                      %
%                                                                            %
%              jrh@cl.cam.ac.uk                                              %
%                                                                            %
% DATE:        30th May 1992    [Original version written]                   %
% REVISED:     31st Mar 1993    [Recursion theorem added]                    %
%               2nd Mar 1994    [Improved proofs]                            %
%                                                                            %
% DETAILS: The recursion theorem justifies arbitrary recursive definitions:  %
%                                                                            %
%   ?!f. f a = h f a                                                         %
%                                                                            %
% provided one can prove that for some wellfounded "measure" function, the   %
% value of |h f a| depends only on the values of |f| at values of lower      %
% measure than |a|.                                                          %
%                                                                            %
% The versions of the Axiom of Choice proved are:                            %
%                                                                            %
%     1. Cantor-Zermelo well-ordering theorem:                               %
%        Every set can be wellordered.                                       %
%                                                                            %
%     2. Hausdorff Maximum Principle:                                        %
%        Every poset has a maximal chain.                                    %
%                                                                            %
%     3. Zorn's Lemma:                                                       %
%        A poset where every chain has an upper bound, has a                 %
%        maximal element.                                                    %
%                                                                            %
%     4. Kuratowski's Lemma:                                                 %
%        Every chain is a poset can be extended to a maximal                 %
%        chain.                                                              %
%                                                                            %
% The proofs (the early ones at least) approximately follow those in the     %
% introductory set-theory section of:                                        %
%                                                                            %
%     R. M. Dudley                                                           %
%     Real analysis and probability                                          %
%     Wadsworth & Brooks/Cole 1989                                           %
%                                                                            %
% One or two ideas (e.g. simple characterization of woset) are from:         %
%                                                                            %
%     R. R. Stoll                                                            %
%     Set Theory and Logic                                                   %
%     Dover 1979                                                             %
%============================================================================%

can unlink `WELLORDER.th`;;

new_theory `WELLORDER`;;

timer true;;

let ty = ":*#*->bool";;

let set_wo_map,unset_wo_map =
  let extras =
   [`subset`,`wo_subset`;
    `Union`,`wo_Union`;
    `fl`,`wo_fl`;
    `poset`,`wo_poset`;
    `chain`,`wo_chain`;
    `woset`,`wo_woset`;
    `inseg`,`wo_inseg`;
    `linseg`,`wo_linseg`;
    `ordinal`,`wo_ordinal`;
    `less`,`wo_less`] in
  (\():void. do set_interface_map(union (interface_map()) extras)),
  (\():void. do set_interface_map(subtract (interface_map()) extras));;

%----------------------------------------------------------------------------%
% Some useful tactics etc.                                                   %
%----------------------------------------------------------------------------%

let TAUT_CONV =
  let val w t = type_of t = ":bool" & can (find_term is_var) t & free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C $THEN (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o sort (uncurry free_in) o
    W(find_terms o val) o snd));;

let GEN_PAIR_TAC =
  W($THEN GEN_TAC o SUBST1_TAC o SYM o
    C ISPEC PAIR o fst o dest_forall o snd);;

let PBETA_TAC = CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV);;

let ABBREV_TAC tm =
  let v,t = dest_eq tm in
  CHOOSE_THEN (\th. SUBST_ALL_TAC th THEN ASSUME_TAC th)
              (EXISTS(mk_exists(v,mk_eq(t,v)),t) (REFL t));;

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(curry$= s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

let ANTE_RES_THEN ttac th = FIRST_ASSUM(\t. ttac (MATCH_MP t th));;

let IMP_RES_THEN ttac th = FIRST_ASSUM(\t. ttac (MATCH_MP th t));;

let LAND_CONV = RATOR_CONV o RAND_CONV;;

%============================================================================%
% (0) Definitions and general lemmas.                                        %
%============================================================================%

%----------------------------------------------------------------------------%
% Irreflexive version of an ordering.                                        %
%----------------------------------------------------------------------------%

let less = new_definition(`less`,
  "(wo_less l)(x,y) = (l:*#*->bool)(x,y) /\ ~(x = y)");;

%----------------------------------------------------------------------------%
% Subset                                                                     %
%----------------------------------------------------------------------------%

let subset = new_infix_definition(`subset`,
  "$wo_subset P Q = !x:*. P x ==> Q x");;

%----------------------------------------------------------------------------%
% Union                                                                      %
%----------------------------------------------------------------------------%

let Union = new_definition(`Union`,
  "wo_Union P = \x:*. ?p. P p /\ p x");;

%----------------------------------------------------------------------------%
% Field of an uncurried binary relation                                      %
%----------------------------------------------------------------------------%

let fl = new_definition(`fl`,
  "wo_fl(l:^ty) x = ?y:*. l(x,y) \/ l(y,x)");;

%----------------------------------------------------------------------------%
% Partial order (we infer the domain from the field of the relation)         %
%----------------------------------------------------------------------------%

let poset = new_definition(`poset`,
  "wo_poset (l:^ty) =
       (!x. wo_fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y))");;

%----------------------------------------------------------------------------%
% Chain in a poset (Defined as a subset of the field, not the ordering)      %
%----------------------------------------------------------------------------%

let chain = new_definition(`chain`,
  "wo_chain(l:^ty) P = (!x y. P x /\ P y ==> l(x,y) \/ l(y,x))");;

%----------------------------------------------------------------------------%
% Wellorder                                                                  %
%----------------------------------------------------------------------------%

let woset = new_definition(`woset`,
 "wo_woset (l:^ty) =
       (!x. wo_fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
       (!x y. wo_fl(l) x /\ wo_fl(l) y ==> l(x,y) \/ l(y,x)) /\
       (!P. (!x. P x ==> wo_fl(l) x) /\ (?x. P x) ==>
            (?y. P y /\ (!z. P z ==> l(y,z))))");;

%----------------------------------------------------------------------------%
% General (reflexive) notion of initial segment.                             %
%----------------------------------------------------------------------------%

let inseg = new_infix_definition(`inseg`,
  "wo_inseg (l:^ty) m = !x y. l(x,y) = m(x,y) /\ wo_fl(l) y");;

%----------------------------------------------------------------------------%
% Specific form of initial segment: "all elements in fl(l) less than a".     %
%----------------------------------------------------------------------------%

let linseg = new_definition(`linseg`,
  "wo_linseg (l:^ty) a = \(x,y). l(x,y) /\ (wo_less l)(y,a)");;

%----------------------------------------------------------------------------%
% "Ordinals", i.e. canonical wosets using choice operator.                   %
%----------------------------------------------------------------------------%

let ordinal = new_definition(`ordinal`,
  "wo_ordinal(l:^ty) =
    wo_woset(l) /\ (!x. wo_fl(l) x ==> (x = $@ (\y. ~(wo_less l)(y,x))))");;

%----------------------------------------------------------------------------%
% Set up the interface map now, for convenience                              %
%----------------------------------------------------------------------------%

set_wo_map();;

%----------------------------------------------------------------------------%
% Derive useful properties of subset                                         %
%----------------------------------------------------------------------------%

let SUBSET_REFL = prove_thm(`SUBSET_REFL`,
  "!P:*->bool. P subset P",
  REWRITE_TAC[subset]);;

let SUBSET_ANTISYM = prove_thm(`SUBSET_ANTISYM`,
  "!(P:*->bool) Q. P subset Q /\ Q subset P ==> (P = Q)",
  REPEAT GEN_TAC THEN REWRITE_TAC[subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN
  REWRITE_TAC[TAUT_CONV "(a ==> b) /\ (b ==> a) = (a = b)"]);;

let SUBSET_TRANS = prove_thm(`SUBSET_TRANS`,
  "!(P:*->bool) Q R. P subset Q /\ Q subset R ==> P subset R",
  REPEAT GEN_TAC THEN REWRITE_TAC[subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  DISCH_THEN($THEN (X_GEN_TAC "x:*") o MP_TAC o SPEC "x:*") THEN
  MATCH_ACCEPT_TAC(TAUT_CONV "(a ==> b) /\ (b ==> c) ==> (a ==> c)"));;

%----------------------------------------------------------------------------%
% Now useful things about the orderings                                      %
%----------------------------------------------------------------------------%

let [POSET_REFL; POSET_TRANS; POSET_ANTISYM] = map (GEN "l:^ty" o DISCH_ALL)
  (CONJUNCTS(PURE_ONCE_REWRITE_RULE[poset] (ASSUME "poset (l:^ty)")));;

let POSET_FLEQ = prove_thm(`POSET_FLEQ`,
  "!l:^ty. poset l ==> (!x. fl(l) x = l(x,x))",
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP POSET_REFL);
    DISCH_TAC THEN REWRITE_TAC[fl] THEN EXISTS_TAC "x:*" THEN
    ASM_REWRITE_TAC[]]);;

let CHAIN_SUBSET = prove_thm(`CHAIN_SUBSET`,
  "!(l:^ty) P Q. chain(l) P /\ Q subset P ==> chain(l) Q",
  REPEAT GEN_TAC THEN REWRITE_TAC[chain; subset] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

let [WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; WOSET_TOTAL; WOSET_WELL] =
  map (GEN "l:^ty" o DISCH_ALL)
    (CONJUNCTS(PURE_ONCE_REWRITE_RULE[woset] (ASSUME "woset (l:^ty)")));;

let WOSET_POSET = prove_thm(`WOSET_POSET`,
  "!l:^ty. woset l ==> poset l",
  GEN_TAC THEN REWRITE_TAC[woset; poset] THEN
  DISCH_THEN(\th. REWRITE_TAC[th]));;

let WOSET_FLEQ = prove_thm(`WOSET_FLEQ`,
  "!l:^ty. woset l ==> (!x. fl(l) x = l(x,x))",
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP WOSET_POSET) THEN
  MATCH_ACCEPT_TAC POSET_FLEQ);;

let WOSET_TRANS_LESS = prove_thm(`WOSET_TRANS_LESS`,
  "!l:*#*->bool. woset l ==>
       !x y z. (less l)(x,y) /\ l(y,z) ==> (less l)(x,z)",
  REWRITE_TAC[less] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC "x:* = z" THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC "~(z:* = y)" THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Antisymmetry and wellfoundedness are sufficient for a wellorder            %
%----------------------------------------------------------------------------%

let WOSET = prove_thm(`WOSET`,
  "!l:^ty. woset l =
        (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
        (!P. (!x. P x ==> fl(l) x) /\ (?x. P x) ==>
             (?y. P y /\ (!z. P z ==> l(y,z))))",
  GEN_TAC THEN REWRITE_TAC[woset] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN "!x y. fl(l:^ty) x /\ fl(l) y ==> l(x,y) \/ l(y,x)" MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC "\z:*. (z = x) \/ (z = y)") THEN BETA_TAC THEN
    W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
        FIRST_ASSUM ACCEPT_TAC;
        EXISTS_TAC "x:*" THEN REWRITE_TAC[]]; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN "z:*" (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THENL
     [DISCH_THEN(MP_TAC o SPEC "y:*"); DISCH_THEN(MP_TAC o SPEC "x:*")] THEN
    REWRITE_TAC[] THEN DISCH_THEN(\th. REWRITE_TAC[th]);
    DISCH_THEN(\th. ASSUME_TAC th THEN REWRITE_TAC[th] THEN
      MP_TAC(GEN "x:*" (SPECL ["x:*"; "x:*"] th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN(\th. REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[TAUT_CONV "a = ~~a"] THEN
    CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN "fl(l:^ty) x /\ fl(l) y /\ fl(l) z" STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[fl] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC "y:*"; EXISTS_TAC "x:*"; EXISTS_TAC "y:*"] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC "!x y. fl(l:^ty) x /\ fl(l) y ==> l(x,y) \/ l(y,x)" THEN
    DISCH_THEN(MP_TAC o SPECL ["z:*"; "x:*"]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC "\w:*. (w = x) \/ (w = y) \/ (w = z)") THEN
    BETA_TAC THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
        FIRST_ASSUM ACCEPT_TAC;
        EXISTS_TAC "x:*" THEN REWRITE_TAC[]];
      DISCH_THEN(\th. REWRITE_TAC[th])] THEN
    DISCH_THEN(X_CHOOSE_THEN "w:*" (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(DISJ_CASES_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THENL
     map (\t. DISCH_THEN(MP_TAC o SPEC t)) ["z:*"; "x:*"; "y:*"] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC "!x y. l(x,y) /\ l(y,x) ==> (x:* = y)" THENL
     [DISCH_THEN(MP_TAC o SPECL ["x:*"; "y:*"]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC "(l:^ty)(y,z)" THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL ["y:*"; "z:*"]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC "(l:^ty)(x,z)" THEN ASM_REWRITE_TAC[]]]);;

%----------------------------------------------------------------------------%
% Misc lemmas.                                                               %
%----------------------------------------------------------------------------%

let PAIRED_EXT = prove_thm(`PAIRED_EXT`,
  "!(l:*#**->***) m. (!x y. l(x,y) = m(x,y)) = (l = m)",
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "p:*#**" THEN
  SUBST1_TAC(SYM(SPEC "p:*#**" PAIR)) THEN POP_ASSUM MATCH_ACCEPT_TAC);;

let [WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; WOSET_TOTAL; WOSET_WELL] =
  map (GEN "l:^ty" o DISCH_ALL)
    (CONJUNCTS(PURE_ONCE_REWRITE_RULE[woset] (ASSUME "woset (l:^ty)")));;

let WOSET_TRANS_LE = prove_thm(`WOSET_TRANS_LE`,
  "!l:*#*->bool. woset l ==>
       !x y z. l(x,y) /\ (less l)(y,z) ==> (less l)(x,z)",
  REWRITE_TAC[less] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC "x:* = z" THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC "~(y:* = z)" THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[]]);;

let WOSET_WELL_CONTRAPOS = prove_thm(`WOSET_WELL_CONTRAPOS`,
  "!l:^ty. woset l ==>
                (!P. (!x. P x ==> fl(l) x) /\ (?x. P x) ==>
                     (?y. P y /\ (!z. (less l)(z,y) ==> ~P z)))",
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  IMP_RES_THEN(IMP_RES_THEN MP_TAC) WOSET_WELL THEN
  DISCH_THEN(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o C CONJ(ASSUME "(less l)(z:*,y:*)")) THEN
  IMP_RES_THEN(IMP_RES_THEN MP_TAC) WOSET_TRANS_LE THEN
  REWRITE_TAC[less]);;

let WOSET_TOTAL_LE = prove_thm(`WOSET_TOTAL_LE`,
  "!l:^ty. woset l ==> !x y. fl(l) x /\ fl(l) y ==> l(x,y) \/ (less l)(y,x)",
  REPEAT STRIP_TAC THEN REWRITE_TAC[less] THEN
  ASM_CASES_TAC "y:* = x" THEN ASM_REWRITE_TAC[] THENL
   [IMP_RES_THEN MATCH_MP_TAC WOSET_REFL;
    IMP_RES_THEN MATCH_MP_TAC WOSET_TOTAL;] THEN
  ASM_REWRITE_TAC[]);;

let WOSET_TOTAL_LT = prove_thm(`WOSET_TOTAL_LT`,
  "!l:^ty. woset l ==>
     !x y. fl(l) x /\ fl(l) y ==> (x = y) \/ (less l)(x,y) \/ (less l)(y,x)",
  REPEAT STRIP_TAC THEN ASM_CASES_TAC "x:* = y" THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[less] THEN RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_TOTAL THEN ASM_REWRITE_TAC[]);;

%============================================================================%
% (1) Induction and recursion on wellorders.                                 %
%============================================================================%

%----------------------------------------------------------------------------%
% Induction on a wellorder                                                   %
%----------------------------------------------------------------------------%

let WO_INDUCT = prove_thm(`WO_INDUCT`,
  "!P l. woset l /\
         (!x:*. fl(l) x /\ (!y. (less l)(y,x) ==> P(y)) ==> P(x))
        ==> !x. fl(l) x ==> P(x)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
  DISCH_THEN(MP_TAC o SPEC "\x:*. fl(l) x /\ ~P(x)") THEN
  BETA_TAC THEN ASM_REWRITE_TAC[TAUT_CONV "a /\ b ==> a"] THEN
  DISCH_THEN(X_CHOOSE_THEN "x:*" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE
    [TAUT_CONV "(a /\ ~b ==> c) = (a /\ ~c ==> b)"]) THEN
  X_GEN_TAC "y:*" THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[less]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[fl] THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    DISCH_THEN(MP_TAC o SPECL ["y:*"; "x:*"]) THEN
    ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Tactic to apply the above                                                  %
%----------------------------------------------------------------------------%

let WO_INDUCT_TAC =
  let thm = CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) WO_INDUCT in
  \(asl,w).
    let qv,bod = (I # (snd o dest_imp))(dest_forall w) in
    let pred = mk_abs(qv,bod) in
    let thi = ISPEC pred thm in
    let thf = CONV_RULE
      (ONCE_DEPTH_CONV(BETA_CONV o assert (curry$= pred o rator))) thi in
    MATCH_MP_TAC thf (asl,w);;

%----------------------------------------------------------------------------%
% Functions satisfying recursion eqn must agree on their common "domain"     %
%----------------------------------------------------------------------------%

let AGREE_LEMMA = prove_thm(`AGREE_LEMMA`,
  "!l h (ms:*->***) m n f g z.
        woset l /\
        (!x. fl(l)(ms(x))) /\
        (!f f' x. (!y. (less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x)) /\
        (!x. l(ms x,m) ==> (f x = h f x)) /\
        (!x. l(ms x,n) ==> (g x = h g x)) /\
        l(ms z,m) /\
        l(ms z,n) ==> (f z :** = g z)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN "!p (x:*). (l:***#***->bool)(p,m) /\ l(p,n) /\ (ms(x) = p)
                           ==> (f x :**= g x)" MATCH_MP_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC "fl(l:***#***->bool) p" THENL
     [UNDISCH_TAC "fl(l:***#***->bool) p" THEN
      MAP_EVERY (W (curry SPEC_TAC)) ["x:*"; "p:***"];
      STRIP_TAC THEN UNDISCH_TAC "~fl(l:***#***->bool) p" THEN
      REWRITE_TAC[fl] THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
      EXISTS_TAC "n:***" THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC "(ms:*->***) z" THEN ASM_REWRITE_TAC[]] THEN
  CONV_TAC(ONCE_DEPTH_CONV FORALL_IMP_CONV) THEN
  WO_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC "r:***" THEN STRIP_TAC THEN
  X_GEN_TAC "x:*" THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RES_THEN(\th. REWRITE_TAC[th]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC "y:*" THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT_CONV "a ==> b ==> c = a /\ b ==> c"]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "(ms:*->***) y" THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
  EXISTS_TAC "(ms:*->***) x" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[less]) THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Transfinite recursion *below a given value of the domain*                  %
%----------------------------------------------------------------------------%

let WO_RECURSE_LOCAL = prove_thm(`WO_RECURSE_LOCAL`,
  "!l h (ms:*->***).
        woset l /\
        (!x. fl(l)(ms(x))) /\
        (!f f' x. (!y. (less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x))
            ==> !n. ?f:*->**. !x. l(ms x,n) ==> (f x = h f x)",
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC "fl(l:***#***->bool) n" THENL
   [UNDISCH_TAC "fl(l:***#***->bool) n" THEN SPEC_TAC("n:***","n:***");
    EXISTS_TAC "f:*->**" THEN X_GEN_TAC "x:*" THEN
    DISCH_TAC THEN UNDISCH_TAC "~fl(l:***#***->bool) n" THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[fl] THEN EXISTS_TAC "(ms:*->***) x" THEN
    ASM_REWRITE_TAC[]] THEN
  WO_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC "m:***" THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(RATOR_CONV(ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV SKOLEM_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC "Fn:***->*->**") THEN
  EXISTS_TAC "\x:*. h(\y. (Fn:***->*->**)(ms y) y) x :**" THEN
  X_GEN_TAC "x:*" THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC "y:*" THEN
  DISCH_TAC THEN BETA_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT_CONV "a ==> b ==> c = a /\ b ==> c"]) THEN
  SUBGOAL_THEN "(Fn:***->*->**) (ms y) y = h (Fn(ms y)) y" SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
      EXISTS_TAC "(ms:*->***) x" THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN
      ASM_REWRITE_TAC[]];
    FIRST_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC "z:*" THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC AGREE_LEMMA THEN
    MAP_EVERY EXISTS_TAC ["l:***#***->bool"; "h:(*->**)->*->**"; "ms:*->***";
      "(ms:*->***) y"; "(ms:*->***) z"] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN "(l:***#***->bool)(ms(z:*),ms(z))" ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EVERY_ASSUM(\th. REWRITE_TAC[REWRITE_RULE[less] th]) THEN
    SUBGOAL_THEN "(less l)(ms(y:*),m:***)" ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
      EXISTS_TAC "(ms:*->***) x"; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC "w:*" THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS_LESS) THEN
    EXISTS_TAC "(ms:*->***) y" THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_TRANS) THEN
    EXISTS_TAC "(ms:*->***) x" THEN
    EVERY_ASSUM(\th. REWRITE_TAC[REWRITE_RULE[less] th])]);;

%----------------------------------------------------------------------------%
% Finally, an overall function                                               %
%----------------------------------------------------------------------------%

let WO_RECURSE_EXISTS = prove_thm(`WO_RECURSE_EXISTS`,
  "!l h (ms:*->***).
        woset l /\
        (!x. fl(l)(ms(x))) /\
        (!f f' x. (!y. (less l)(ms y,ms x) ==> (f(y) = f'(y))) ==>
                        (h f x = h f' x))
            ==> ?f:*->**. !x. f x = h f x",
  REPEAT GEN_TAC THEN DISCH_THEN(\th.
    STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP WO_RECURSE_LOCAL th)) THEN
  DISCH_THEN(MP_TAC o CONV_RULE SKOLEM_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC "Fn:***->*->**") THEN
  EXISTS_TAC "\x. (Fn:***->*->**) (ms x) x" THEN GEN_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN "(Fn:***->*->**) (ms x) x = h (Fn(ms x)) x" SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC "y:*" THEN
    DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC AGREE_LEMMA THEN
    MAP_EVERY EXISTS_TAC ["l:***#***->bool"; "h:(*->**)->*->**"; "ms:*->***";
      "(ms:*->***) x"; "(ms:*->***) y"] THEN ASM_REWRITE_TAC[] THEN
    EVERY_ASSUM(\th. REWRITE_TAC[REWRITE_RULE[less] th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL) THEN
    ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Now the final version including uniqueness                                 %
%----------------------------------------------------------------------------%

let WO_RECURSE = prove_thm(`WO_RECURSE `,
  "!l h (ms:*->***).
        woset l /\
        (!x. fl(l)(ms(x))) /\
        (!f g x. (!y. (less l)(ms y,ms x) ==> (f(y) = g(y))) ==>
                        (h f x = h g x))
            ==> ?!f:*->**. !x. f x = h f x",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP WO_RECURSE_EXISTS th]) THEN
  MAP_EVERY X_GEN_TAC ["f1:*->**"; "f2:*->**"] THEN STRIP_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "z:*" THEN
  MATCH_MP_TAC AGREE_LEMMA THEN
  MAP_EVERY EXISTS_TAC ["l:***#***->bool"; "h:(*->**)->*->**"; "ms:*->***";
    "(ms:*->***) z"; "(ms:*->***) z"] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_REFL o el 1 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Special case of natural number measure.                                    %
%----------------------------------------------------------------------------%

let FL_NUM = prove_thm(`FL_NUM`,
  "!n. fl(\(m,n). m <= n) n",
  GEN_TAC THEN REWRITE_TAC[fl] THEN
  EXISTS_TAC "n:num" THEN
  PBETA_TAC THEN
  REWRITE_TAC[LESS_EQ_REFL]);;

let WOSET_NUM = prove_thm(`WOSET_NUM`,
  "woset(\(m,n). m <= n)",
  REWRITE_TAC[WOSET] THEN PBETA_TAC THEN
  REWRITE_TAC[LESS_EQUAL_ANTISYM; FL_NUM] THEN
  GEN_TAC THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV CONTRAPOS_CONV)) THEN
  REWRITE_TAC[NOT_LESS_EQUAL; WOP]);;

let WO_RECURSE_NUM = prove_thm(`WO_RECURSE_NUM`,
  "!h ms.
     (!f g x. (!y. ms y < ms x ==> (f(y) = g(y))) ==> (h f x = h g x))
            ==> ?!f:*->**. !x. f x = h f x",
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC "\(m,n). m <= n" WO_RECURSE) THEN
  EXISTS_TAC "ms:*->num" THEN REWRITE_TAC[FL_NUM; WOSET_NUM] THEN
  REWRITE_TAC[less] THEN PBETA_TAC THEN
  REWRITE_TAC[LESS_OR_EQ; TAUT_CONV "(a \/ b) /\ ~b = a /\ ~b"] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_NOT_EQ THEN
  ASM_REWRITE_TAC[]);;

%============================================================================%
% (2) AXIOM OF CHOICE ==> CANTOR-ZERMELO WELLORDERING THEOREM                %
%============================================================================%

%----------------------------------------------------------------------------%
% Union of initial segments is an initial segment.                           %
%----------------------------------------------------------------------------%

let UNION_FL = prove_thm(`UNION_FL`,
  "!P (l:^ty). fl(Union P) x = ?l. P l /\ fl(l) x",
  REPEAT GEN_TAC THEN REWRITE_TAC[Union; fl] THEN
  BETA_TAC THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV OR_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT_CONV "a /\ b \/ a /\ c = a /\ (b \/ c)"] THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_AND_EXISTS_CONV) THEN
  CONV_TAC(RAND_CONV SWAP_EXISTS_CONV) THEN REFL_TAC);;

let UNION_INSEG = prove_thm(`UNION_INSEG`,
  "!P (l:^ty). (!m. P m ==> m inseg l) ==> (Union P) inseg l",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[inseg; UNION_FL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[Union] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(RAND_CONV RIGHT_AND_EXISTS_CONV) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN "m:^ty" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "m:^ty" THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(IMP_RES_THEN (MP_TAC o REWRITE_RULE[inseg])) THENL
   [DISCH_THEN(\th. ASM_REWRITE_TAC[GSYM th]);
    DISCH_THEN(\th. ASM_REWRITE_TAC[th])]);;

%----------------------------------------------------------------------------%
% Initial segment of a woset is a woset.                                     %
%----------------------------------------------------------------------------%

let INSEG_SUBSET = prove_thm(`INSEG_SUBSET`,
  "!(l:^ty) m. m inseg l ==> !x y. m(x,y) ==> l(x,y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[inseg] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[TAUT_CONV "a /\ b ==> a"]);;

let INSEG_SUBSET_FL = prove_thm(`INSEG_SUBSET_FL`,
  "!(l:^ty) m. m inseg l ==> !x. fl(m) x ==> fl(l) x",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[fl] THEN
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN "y:*"
   ($THEN (EXISTS_TAC "y:*") o MP_TAC)) THEN
  MATCH_MP_TAC(TAUT_CONV "(a ==> b) /\ (c ==> d) ==> a \/ c ==> b \/ d") THEN
  CONJ_TAC THEN IMP_RES_THEN MATCH_ACCEPT_TAC INSEG_SUBSET);;

let INSEG_WOSET = prove_thm(`INSEG_WOSET`,
  "!(l:^ty) m. m inseg l /\ woset l ==> woset m",
  REPEAT GEN_TAC THEN REWRITE_TAC[inseg] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[WOSET] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN IMP_RES_THEN MATCH_MP_TAC WOSET_ANTISYM;
    X_GEN_TAC "P:*->bool" THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    IMP_RES_THEN(MP_TAC o SPEC "P:*->bool") WOSET_WELL THEN
    SUBGOAL_THEN "!x:*. P x ==> fl(l) x" (\th. ASM_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INSEG_SUBSET_FL;
      DISCH_THEN(X_CHOOSE_THEN "z:*" STRIP_ASSUME_TAC) THEN
      EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC]] THEN
  ASM_REWRITE_TAC[inseg]);;

%----------------------------------------------------------------------------%
% Properties of segments of the "linseg" form.                               %
%----------------------------------------------------------------------------%

let LINSEG_INSEG = prove_thm(`LINSEG_INSEG`,
  "!(l:^ty) a. woset l ==> (linseg l a) inseg l",
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseg; linseg] THEN
  REPEAT GEN_TAC THEN PBETA_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
    IMP_RES_THEN MATCH_MP_TAC WOSET_TRANS_LE THEN
    FIRST_ASSUM(\th. EXISTS_TAC (rand(rand(concl th))) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC)]);;

let LINSEG_WOSET = prove_thm(`LINSEG_WOSET`,
  "!(l:^ty) a. woset l ==> woset(linseg l a)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INSEG_WOSET THEN
  EXISTS_TAC "l:^ty" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINSEG_INSEG THEN ASM_REWRITE_TAC[]);;

let LINSEG_FL = prove_thm(`LINSEG_FL`,
  "!(l:^ty) a x. woset l ==> (fl (linseg l a) x = (less l)(x,a))",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  IMP_RES_THEN (MP_TAC o SPEC "a:*") LINSEG_WOSET THEN
  DISCH_THEN(\th. REWRITE_TAC[MATCH_MP WOSET_FLEQ th]) THEN
  REWRITE_TAC[linseg] THEN PBETA_TAC THEN
  REWRITE_TAC[less; TAUT_CONV "(a /\ b = b) = b ==> a"] THEN DISCH_TAC THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN REWRITE_TAC[fl] THEN
  EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Key fact: a proper initial segment is of the special form.                 %
%----------------------------------------------------------------------------%

let INSEG_PROPER_SUBSET = prove_thm(`INSEG_PROPER_SUBSET`,
  "!(l:^ty) m. m inseg l /\ ~(l = m) ==>
                   ?x y. l(x,y) /\ ~m(x,y)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM PAIRED_EXT] THEN
  CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN "x:*" (X_CHOOSE_THEN "y:*" MP_TAC)) THEN
  ASM_CASES_TAC "(m:^ty)(x,y)" THEN ASM_REWRITE_TAC[] THENL
   [IMP_RES_THEN(IMP_RES_THEN ASSUME_TAC) INSEG_SUBSET;
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC ["x:*"; "y:*"]] THEN
  ASM_REWRITE_TAC[]);;

let INSEG_PROPER_SUBSET_FL = prove_thm(`INSEG_PROPER_SUBSET_FL`,
  "!(l:^ty) m. m inseg l /\ ~(l = m) ==>
                   ?a. fl(l) a /\ ~fl(m) a",
  REPEAT GEN_TAC THEN DISCH_THEN(\th. MP_TAC th THEN STRIP_ASSUME_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INSEG_PROPER_SUBSET) THEN
  DISCH_THEN(X_CHOOSE_THEN "x:*" (X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC "y:*" THEN CONJ_TAC THENL
   [REWRITE_TAC[fl] THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC "(m:^ty) inseg l" THEN REWRITE_TAC[inseg] THEN
    DISCH_THEN(MP_TAC o SPECL ["x:*"; "y:*"]) THEN ASM_REWRITE_TAC[]]);;

let INSEG_LINSEG = prove_thm(`INSEG_LINSEG`,
  "!(l:^ty) m. woset l ==>
      (m inseg l = (m = l) \/ (?a. fl(l) a /\ (m = linseg l a)))",
  REPEAT STRIP_TAC THEN ASM_CASES_TAC "m:^ty = l" THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[inseg; fl; TAUT_CONV "(a = a /\ b) = a ==> b"] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[fl] THEN
    EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC LINSEG_INSEG THEN FIRST_ASSUM MATCH_ACCEPT_TAC)] THEN
  IMP_RES_THEN (MP_TAC o SPEC "\x:*. fl(l) x /\ ~fl(m) x")
    WOSET_WELL_CONTRAPOS THEN BETA_TAC THEN
  REWRITE_TAC[TAUT_CONV "a /\ b ==> a"] THEN
  MP_TAC(SPECL ["l:^ty"; "m:^ty"] (GSYM INSEG_PROPER_SUBSET_FL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(\th. REWRITE_TAC[th]) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN "a:*" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM PAIRED_EXT] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [IMP_RES_THEN ASSUME_TAC LINSEG_INSEG THEN
    REWRITE_TAC[linseg] THEN PBETA_TAC THEN
    UNDISCH_TAC "m:^ty(x,y)" THEN RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM inseg]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    IMP_RES_THEN(MP_TAC o SPECL ["a:*"; "y:*"]) WOSET_TOTAL_LE THEN
    IMP_RES_THEN(IMP_RES_THEN ASSUME_TAC) INSEG_SUBSET_FL THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC "~fl(m:^ty) a" THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN REWRITE_TAC[fl] THEN
    EXISTS_TAC "y:*" THEN RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC "linseg (l:^ty) a (x,y)" THEN REWRITE_TAC[linseg] THEN
    PBETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ANTE_RES_THEN MP_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[fl] THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% A proper initial segment can be extended by its bounding element.          %
%----------------------------------------------------------------------------%

let EXTEND_FL = prove_thm(`EXTEND_FL`,
  "!(l:^ty) x. woset l ==> (fl (\(x,y). l(x,y) /\ l(y,a)) x = l(x,a))",
  REPEAT STRIP_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
    IMP_RES_THEN MATCH_MP_TAC WOSET_TRANS THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] THEN
    IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN REWRITE_TAC[fl] THEN
    EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[]]);;

let EXTEND_INSEG = prove_thm(`EXTEND_INSEG`,
  "!(l:^ty) a. woset l /\ fl(l) a ==> (\(x,y). l(x,y) /\ l(y,a)) inseg l",
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseg] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) EXTEND_FL);;

let EXTEND_LINSEG = prove_thm(`EXTEND_LINSEG`,
  "!(l:^ty) a. woset l /\ fl(l) a ==>
       (\(x,y). linseg l a (x,y) \/ (y = a) /\ (fl(linseg l a) x \/ (x = a)))
                inseg l",
  REPEAT GEN_TAC THEN DISCH_THEN(\th. STRIP_ASSUME_TAC th THEN
    MP_TAC (MATCH_MP EXTEND_INSEG th)) THEN
  MATCH_MP_TAC(TAUT_CONV "(a = b) ==> a ==> b") THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (\th. REWRITE_TAC[th]) LINSEG_FL THEN
  REWRITE_TAC[linseg; less] THEN PBETA_TAC THEN
  MAP_EVERY ASM_CASES_TAC ["x:* = a"; "y:* = a"] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN "(l:^ty)(a,a)" (\th. REWRITE_TAC[th]) THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Key canonicality property of ordinals.                                     %
%----------------------------------------------------------------------------%

let ORDINAL_CHAINED = prove_thm(`ORDINAL_CHAINED`,
  "!(l:^ty) m. ordinal(l) /\ ordinal(m) ==> m inseg l \/ l inseg m",
  REWRITE_TAC[ordinal] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC "\k:^ty. k inseg l /\ k inseg m" UNION_INSEG) THEN
  DISCH_THEN(\th. MP_TAC(CONJ (SPEC "l:^ty" th) (SPEC "m:^ty" th))) THEN
  BETA_TAC THEN REWRITE_TAC[TAUT_CONV "(a /\ b ==> a) /\ (a /\ b ==> b)"] THEN
  ABBREV_TAC "k:^ty = Union(\k. k inseg l /\ k inseg m)" THEN
  DISCH_THEN(\th. STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  EVERY_ASSUM(\th. GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [] [MATCH_MP INSEG_LINSEG th] ? ALL_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  ASM_CASES_TAC "l:^ty = k" THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC "m:^ty = k" THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN "a:*" STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN "b:*" STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN "a:* = b" SUBST_ALL_TAC THENL
   [MAP_EVERY (ANTE_RES_THEN SUBST1_TAC o ASSUME)
     ["fl(l:^ty) a"; "fl(m:^ty) b"] THEN
    AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
    BETA_TAC THEN AP_TERM_TAC THEN
    EVERY_ASSUM(\th. REWRITE_TAC[GSYM(MATCH_MP LINSEG_FL th)] ? ALL_TAC) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(CONJ(SPECL ["l:^ty"; "b:*"] EXTEND_LINSEG)
               (SPECL ["m:^ty"; "b:*"] EXTEND_LINSEG)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC "Union(\k:^ty. k inseg l /\ k inseg m) = k" THEN
    REWRITE_TAC[Union] THEN CONV_TAC (LAND_CONV FUN_EQ_CONV) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) THEN
    CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    ONCE_REWRITE_TAC[TAUT_CONV "a /\ b ==> c = a ==> b ==> c"] THEN
    DISCH_THEN(IMP_RES_THEN (MP_TAC o SPEC "(b:*,b:*)")) THEN
    PBETA_TAC THEN REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[linseg] THEN PBETA_TAC THEN REWRITE_TAC[less]]);;

%----------------------------------------------------------------------------%
% Proof that any nono-universe ordinal can be extended to its "successor".   %
%----------------------------------------------------------------------------%

let FL_SUC = prove_thm(`FL_SUC`,
  "!(l:^ty) a. fl(\(x,y). l(x,y) \/ (y = a) /\ (fl(l) x \/ (x = a))) x =
              fl(l) x \/ (x = a)",
  REPEAT GEN_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY DISJ1_TAC THEN
  W(MAP_FIRST (\tm. EXISTS_TAC tm THEN ASM_REWRITE_TAC[] THEN NO_TAC) o
    freesl o fst));;

let ORDINAL_SUC = prove_thm(`ORDINAL_SUC`,
  "!l:^ty. ordinal(l) /\ (?x. ~(fl(l) x)) ==>
                ordinal(\(x,y). l(x,y) \/ (y = @y. ~fl(l) y) /\
                                          (fl(l) x \/ (x = @y. ~fl(l) y)))",
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC "a:* = @y. ~fl(l) y" THEN
  SUBGOAL_THEN "~fl(l:^ty) a" ASSUME_TAC THENL
   [EXPAND_TAC `a` THEN CONV_TAC SELECT_CONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PBETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[WOSET] THEN PBETA_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [IMP_RES_THEN MATCH_MP_TAC WOSET_ANTISYM THEN
        ASM_REWRITE_TAC[]; ALL_TAC; ALL_TAC] THEN
      UNDISCH_TAC "~fl(l:^ty) a" THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[fl] THENL
       [EXISTS_TAC "y:*"; EXISTS_TAC "x:*"] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC "P:*->bool" THEN REWRITE_TAC[FL_SUC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC "w:*")) THEN
      IMP_RES_THEN (MP_TAC o SPEC "\x:*. P x /\ fl(l) x") WOSET_WELL THEN
      BETA_TAC THEN REWRITE_TAC[TAUT_CONV "a /\ b ==> b"] THEN
      ASM_CASES_TAC "?x:*. P x /\ fl(l) x" THEN ASM_REWRITE_TAC[] THENL
       [DISCH_THEN(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
        EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
        GEN_TAC THEN DISCH_TAC THEN
        FIRST_ASSUM(IMP_RES_THEN DISJ_CASES_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o SPEC "w:*" o CONV_RULE NOT_EXISTS_CONV) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_ASSUM(IMP_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC "z:*" THEN DISCH_TAC THEN
        FIRST_ASSUM(IMP_RES_THEN MP_TAC) THEN
        FIRST_ASSUM(MP_TAC o SPEC "z:*" o CONV_RULE NOT_EXISTS_CONV) THEN
        REPEAT(ASM_REWRITE_TAC[] THEN DISCH_TAC)]];
    X_GEN_TAC "z:*" THEN REWRITE_TAC[FL_SUC; less] THEN
    PBETA_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
     [FIRST_ASSUM(IMP_RES_THEN (\th. GEN_REWRITE_TAC LAND_CONV [] [th])) THEN
      AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
      BETA_TAC THEN REWRITE_TAC[less] THEN AP_TERM_TAC THEN
      ASM_CASES_TAC "y:* = z" THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC "fl(l:^ty) z" THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC "z:* = a" THEN DISCH_THEN SUBST_ALL_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [] [SYM(ASSUME "(@y:*. ~fl(l) y) = a")] THEN
      AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
      BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC "y:* = a" THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[fl] THEN EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[]]]);;

%----------------------------------------------------------------------------%
% The union of a set of ordinals is an ordinal.                              %
%----------------------------------------------------------------------------%

let ORDINAL_UNION = prove_thm(`ORDINAL_UNION`,
  "!P. (!l:^ty. P l ==> ordinal(l)) ==> ordinal(Union P)",
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ordinal; WOSET] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC ["x:*"; "y:*"] THEN REWRITE_TAC[Union] THEN
    BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN "l:^ty" (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))
     (X_CHOOSE_THEN "m:^ty" (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))) THEN
    MP_TAC(SPECL ["l:^ty"; "m:^ty"] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPEC "l:^ty" WOSET_ANTISYM);
      MP_TAC(SPEC "m:^ty" WOSET_ANTISYM)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ordinal]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC "Q:*->bool" THEN REWRITE_TAC[UNION_FL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC "a:*")) THEN
    FIRST_ASSUM(IMP_RES_THEN (X_CHOOSE_THEN "l:^ty" STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN ASSUME_TAC (ASSUME "!l:^ty. P l ==> ordinal l") THEN
    ASSUME_TAC(CONJUNCT1(REWRITE_RULE[ordinal] (ASSUME "ordinal(l:^ty)"))) THEN
    IMP_RES_THEN(MP_TAC o SPEC "\x:*. fl(l) x /\ Q x") WOSET_WELL THEN
    BETA_TAC THEN REWRITE_TAC[TAUT_CONV "a /\ b ==> a"] THEN
    SUBGOAL_THEN "?x:*. fl(l) x /\ Q x" (\th. REWRITE_TAC[th]) THENL
     [EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN "b:*" STRIP_ASSUME_TAC) THEN
    EXISTS_TAC "b:*" THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC "x:*" THEN DISCH_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME "(Q:*->bool) x") THEN
    DISCH_THEN(X_CHOOSE_THEN "m:^ty" STRIP_ASSUME_TAC) THEN
    ANTE_RES_THEN ASSUME_TAC (ASSUME "(P:^ty->bool) m") THEN
    MP_TAC(SPECL ["l:^ty"; "m:^ty"] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[Union] THEN BETA_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
     [EXISTS_TAC "l:^ty" THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET_FL THEN ASM_REWRITE_TAC[];
      EXISTS_TAC "m:^ty" THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPECL ["x:*"; "b:*"] o REWRITE_RULE[inseg]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      IMP_RES_THEN (MP_TAC o SPEC "b:*") INSEG_SUBSET_FL THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(CONJUNCT1(REWRITE_RULE[ordinal] (ASSUME "ordinal(m:^ty)"))) THEN
      DISCH_THEN(MP_TAC o SPECL ["b:*"; "x:*"] o MATCH_MP WOSET_TOTAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[fl] THEN
      EXISTS_TAC "b:*" THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC "x:*" THEN REWRITE_TAC[UNION_FL] THEN
    DISCH_THEN(X_CHOOSE_THEN "l:^ty" STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[ordinal] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC "x:*")) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT_CONV "(a = b) ==> a ==> b") THEN
    REPEAT AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    X_GEN_TAC "y:*" THEN BETA_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC "y:* = x" THEN ASM_REWRITE_TAC[less; Union] THEN
    BETA_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC "l:^ty" THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(X_CHOOSE_THEN "m:^ty" STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN "ordinal(l:^ty) /\ ordinal(m:^ty)" MP_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_CHAINED)] THENL
       [IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[]]]]);;

%----------------------------------------------------------------------------%
% Consequently, every type can be wellordered (and by an ordinal).           %
%----------------------------------------------------------------------------%

let ORDINAL_UNION_LEMMA = prove_thm(`ORDINAL_UNION_LEMMA`,
  "!(l:^ty) x. ordinal l ==> fl(l) x ==> fl(Union(ordinal)) x",
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_FL] THEN
  EXISTS_TAC "l:^ty" THEN ASM_REWRITE_TAC[]);;

let ORDINAL_UP = prove_thm(`ORDINAL_UP`,
  "!l:^ty. ordinal(l) ==> (!x. fl(l) x) \/
                          (?m x. ordinal(m) /\ fl(m) x /\ ~fl(l) x)",
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT_CONV "a \/ b = ~a ==> b"] THEN
  CONV_TAC(LAND_CONV NOT_FORALL_CONV) THEN DISCH_TAC THEN
  MP_TAC(SPEC "l:^ty" ORDINAL_SUC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   ["\(x,y). l(x,y) \/ (y = @y:*. ~fl l y) /\ (fl(l) x \/ (x = @y. ~fl l y))";
    "@y. ~fl(l:^ty) y"] THEN
  ASM_REWRITE_TAC[FL_SUC] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let WO_LEMMA = prove_thm(`WO_LEMMA`,
  "?l:^ty. ordinal(l) /\ !x. fl(l) x",
  EXISTS_TAC "Union (ordinal:^ty->bool)" THEN
  MATCH_MP_TAC(TAUT_CONV "a /\ (a ==> b) ==> a /\ b") THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORDINAL_UNION THEN REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_UP) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(X_CHOOSE_THEN "m:^ty"
     (X_CHOOSE_THEN "x:*" STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN (IMP_RES_THEN MP_TAC) ORDINAL_UNION_LEMMA THEN
    ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% At least -- every set can be wellordered.                                  %
%----------------------------------------------------------------------------%

let WO_FL_RESTRICT = prove_thm(`WO_FL_RESTRICT`,
  "!l. woset l ==>
       !P. fl(\(x:*,y). P x /\ P y /\ l(x,y)) x = P x /\ fl(l) x",
  REPEAT STRIP_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN
  REWRITE_TAC[fl] THEN EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[]);;

let WO = prove_thm(`WO`,
  "!P. ?l:^ty. woset l /\ (fl(l) = P)",
  GEN_TAC THEN X_CHOOSE_THEN "l:^ty" STRIP_ASSUME_TAC
   (REWRITE_RULE[ordinal] WO_LEMMA) THEN
  EXISTS_TAC "\(x:*,y). P x /\ P y /\ l(x,y)" THEN REWRITE_TAC[WOSET] THEN
  PBETA_TAC THEN CONV_TAC(RAND_CONV(X_FUN_EQ_CONV "x:*")) THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP WO_FL_RESTRICT th]) THEN PBETA_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC "Q:*->bool" THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
    DISCH_THEN(MP_TAC o SPEC "Q:*->bool") THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

%============================================================================%
% (3) CANTOR-ZERMELO WELL-ORDERING THEOREM ==> HAUSDORFF MAXIMAL PRINCIPLE   %
%============================================================================%

let HP = prove_thm(`HP`,
  "!l:^ty. poset l ==>
        ?P. chain(l) P /\ !Q. chain(l) Q  /\ P subset Q ==> (Q = P)",
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN "w:^ty" MP_TAC (SPEC "\x:*. T" WO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(LAND_CONV(X_FUN_EQ_CONV "x:*")) THEN BETA_TAC THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_THEN (MP_TAC o SPEC "\x:*. fl(l) x") WOSET_WELL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC "?x:*. fl(l) x" THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN "b:*" STRIP_ASSUME_TAC);
    FIRST_ASSUM(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    EXISTS_TAC "\x:*. F" THEN REWRITE_TAC[chain; subset] THEN
    GEN_TAC THEN CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN "u:*" MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL ["u:*"; "u:*"]) THEN
    IMP_RES_THEN(ASSUME_TAC o GSYM) POSET_FLEQ THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL["w:^ty"; "\f (x:*).
     (fl(l) x /\ (!y:*. (less w)(y,x) ==> l(x,f y) \/ l(f y,x))) => x | b";
    "\x:*. x"] WO_RECURSE) THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (\t.REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT AP_THM_TAC THEN
    REPEAT AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "z:*" THEN
    BETA_TAC THEN
    REWRITE_TAC[TAUT_CONV "(a ==> b = a ==> c) = a ==> (b = c)"] THEN
    DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN REFL_TAC;
    DISCH_THEN(X_CHOOSE_TAC "f:*->*" o EXISTENCE o GSYM)] THEN
  IMP_RES_THEN(IMP_RES_THEN ASSUME_TAC) POSET_REFL THEN
  SUBGOAL_THEN "(f:*->*) b = b" ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "b:*") THEN
    REWRITE_TAC[COND_ID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "!x:*. fl(l:^ty) (f x)" ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "x:*") THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ANTE_RES_THEN (ASSUME_TAC o GEN_ALL) o SPEC_ALL) THEN
  SUBGOAL_THEN "!x:*. (l:^ty)(b,f x) \/ l(f x,b)" ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC "x:*" (ASSUME "!x:*. (w:^ty)(b,f x)")) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "x:*") THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC "x:* = b" THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN "(less w)(b:*,x)" MP_TAC THENL
     [ASM_REWRITE_TAC[less] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "!x y. l((f:*->*) x,f y) \/ l(f y,f x)" ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    IMP_RES_THEN(MP_TAC o SPECL ["x:*"; "y:*"]) WOSET_TOTAL_LT THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC POSET_REFL;
      ONCE_REWRITE_TAC[DISJ_SYM] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "y:*");
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "x:*")] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(IMP_RES_THEN ACCEPT_TAC o CONJUNCT2); ALL_TAC] THEN
  EXISTS_TAC "\y:*. ?x:*. y = f(x)" THEN
  SUBGOAL_THEN "chain(l:^ty)(\y. ?x:*. y = f x)" ASSUME_TAC THENL
   [REWRITE_TAC[chain] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN(CHOOSE_THEN SUBST1_TAC)); ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC "Q:*->bool" THEN STRIP_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "z:*" THEN EQ_TAC THENL
   [DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC "z:*" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "z:*") THEN
    SUBGOAL_THEN "fl(l:^ty) z /\ !y. (less w)(y,z) ==> l(z,f y) \/ l(f y,z)"
    (\th. REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [UNDISCH_TAC "chain(l:^ty) Q" THEN REWRITE_TAC[chain] THEN
      DISCH_THEN(MP_TAC o SPECL ["z:*"; "z:*"]) THEN ASM_REWRITE_TAC[fl] THEN
      DISCH_TAC THEN EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[];
      X_GEN_TAC "y:*" THEN DISCH_TAC THEN
      UNDISCH_TAC "chain(l:^ty) Q" THEN REWRITE_TAC[chain] THEN
      DISCH_THEN(MP_TAC o SPECL ["z:*"; "(f:*->*) y"]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[subset]) THEN
      BETA_TAC THEN EXISTS_TAC "y:*" THEN REFL_TAC];
    SPEC_TAC("z:*","z:*") THEN ASM_REWRITE_TAC[GSYM subset]]);;

%============================================================================%
% (4) HAUSDORFF MAXIMAL PRINCIPLE ==> ZORN'S LEMMA                           %
%============================================================================%

let ZL = prove_thm(`ZL`,
  "!l:^ty. poset l /\
           (!P. chain(l) P ==> (?y. fl(l) y /\ !x. P x ==> l(x,y))) ==>
        ?y. fl(l) y /\ !x. l(y,x) ==> (y = x)",
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN "M:*->bool" STRIP_ASSUME_TAC o MATCH_MP HP) THEN
  UNDISCH_TAC "!P. chain(l:^ty) P ==> (?y. fl(l) y /\ !x. P x ==> l(x,y))" THEN
  DISCH_THEN(MP_TAC o SPEC "M:*->bool") THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN "m:*" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "m:*" THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC "z:*" THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [] [TAUT_CONV "a = ~~a"] THEN DISCH_TAC THEN
  SUBGOAL_THEN "chain(l) (\x:*. M x \/ (x = z))" MP_TAC THENL
   [REWRITE_TAC[chain] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC "chain(l:^ty) M" THEN REWRITE_TAC[chain] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC "m:*" THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC "m:*" THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
      REWRITE_TAC[fl] THEN EXISTS_TAC "m:*" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN "M subset (\x:*. M x \/ (x = z))" MP_TAC THENL
   [REWRITE_TAC[subset] THEN GEN_TAC THEN BETA_TAC THEN
    DISCH_THEN(\th. REWRITE_TAC[th]); ALL_TAC] THEN
  GEN_REWRITE_TAC I [] [TAUT_CONV "(a ==> b ==> c) = (b /\ a ==> c)"] THEN
  DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[] THEN CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN
  DISCH_THEN(MP_TAC o SPEC "z:*") THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(\th. FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  FIRST_ASSUM(MP_TAC o SPECL ["m:*"; "z:*"] o MATCH_MP POSET_ANTISYM) THEN
  ASM_REWRITE_TAC[]);;

%============================================================================%
% (5) ZORN'S LEMMA ==> KURATOWSKI'S LEMMA                                    %
%============================================================================%

let kl_tm = "\(c1,c2). C subset c1 /\ c1 subset c2 /\ chain(l:^ty) c2";;

let KL_POSET_LEMMA = prove_thm(`KL_POSET_LEMMA`,
  "poset ^kl_tm",
  REWRITE_TAC[poset] THEN PBETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC "P:*->bool" THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN "Q:*->bool" STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THENL
     [MATCH_MP_TAC CHAIN_SUBSET; MATCH_MP_TAC SUBSET_TRANS];
    GEN_TAC THEN X_GEN_TAC "Q:*->bool" THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM] THEN
  TRY(EXISTS_TAC "Q:*->bool") THEN ASM_REWRITE_TAC[]);;

let KL = prove_thm(`KL`,
  "!l:^ty. poset l ==>
        !C. chain(l) C ==>
            ?P. (chain(l) P /\ C subset P) /\
                (!R. chain(l) R /\ P subset R ==> (R = P))",
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC kl_tm ZL) THEN PBETA_TAC THEN
  REWRITE_TAC[KL_POSET_LEMMA; MATCH_MP POSET_FLEQ KL_POSET_LEMMA] THEN
  PBETA_TAC THEN
  W(C SUBGOAL_THEN (\t.REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
   [X_GEN_TAC "P:(*->bool)->bool" THEN GEN_REWRITE_TAC LAND_CONV[] [chain] THEN
    PBETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC "?D:*->bool. P D" THENL
     [EXISTS_TAC "Union(P) :*->bool" THEN REWRITE_TAC[SUBSET_REFL] THEN
      FIRST_ASSUM(X_CHOOSE_TAC "D:*->bool") THEN
      FIRST_ASSUM(MP_TAC o SPECL ["D:*->bool"; "D:*->bool"]) THEN
      REWRITE_TAC[ASSUME "(P:(*->bool)->bool) D"; SUBSET_REFL] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(TAUT_CONV "a /\ b /\ (a /\ b ==> c) ==> (a /\ b) /\ c") THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[Union; subset] THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN EXISTS_TAC "D:*->bool" THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[subset]) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[chain; Union] THEN MAP_EVERY X_GEN_TAC ["x:*"; "y:*"] THEN
        BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
         (X_CHOOSE_TAC "A:*->bool") (X_CHOOSE_TAC "B:*->bool")) THEN
        FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
        DISCH_THEN(MP_TAC o SPECL ["A:*->bool"; "B:*->bool"]) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [UNDISCH_TAC "chain(l:^ty) B"; UNDISCH_TAC "chain(l:^ty) A"] THEN
        REWRITE_TAC[chain] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[subset]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN X_GEN_TAC "X:*->bool" THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPECL ["X:*->bool"; "X:*->bool"]) THEN
        REWRITE_TAC[] THEN DISCH_THEN(IMP_RES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[Union; subset] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN EXISTS_TAC "X:*->bool" THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC "C:*->bool" THEN
      FIRST_ASSUM(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    DISCH_THEN(X_CHOOSE_THEN "D:*->bool" STRIP_ASSUME_TAC) THEN
    EXISTS_TAC "D:*->bool" THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

close_theory();;
