%============================================================================%
% Construct reals from positive reals                                        %
%============================================================================%

can unlink `REALAX.th`;;

new_theory `REALAX`;;

new_parent `HREAL`;;

loadt `useful`;;

autoload_definitions `HREAL`;;

autoload_theorems `HREAL`;;

loadt `equiv`;;

%----------------------------------------------------------------------------%
% Required lemmas about the halfreals - mostly to drive CANCEL_TAC           %
%----------------------------------------------------------------------------%

let HREAL_RDISTRIB = prove_thm(`HREAL_RDISTRIB`,
  "!x y z. (x hreal_add y) hreal_mul z =
              (x hreal_mul z) hreal_add (y hreal_mul z)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HREAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HREAL_LDISTRIB);;

let HREAL_EQ_ADDR = prove_thm(`HREAL_EQ_ADDR`,
  "!x y. ~(x hreal_add y = x)",
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC HREAL_NOZERO);;

let HREAL_EQ_ADDL = prove_thm(`HREAL_EQ_ADDL`,
  "!x y. ~(x = x hreal_add y)",
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDR);;

let HREAL_EQ_LADD = prove_thm(`HREAL_EQ_LADD`,
  "!x y z. (x hreal_add y = x hreal_add z) = (y = z)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL ["y:hreal"; "z:hreal"] HREAL_ADD_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC; ALL_TAC; ALL_TAC] THEN
    POP_ASSUM(X_CHOOSE_THEN "d:hreal" SUBST1_TAC) THEN
    REWRITE_TAC[HREAL_ADD_ASSOC; HREAL_EQ_ADDR; HREAL_EQ_ADDL];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let HREAL_LT_REFL = prove_thm(`HREAL_LT_REFL`,
  "!x. ~(x hreal_lt x)",
  GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[HREAL_EQ_ADDL]);;

let HREAL_LT_ADDL = prove_thm(`HREAL_LT_ADDL`,
  "!x y. x hreal_lt (x hreal_add y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  EXISTS_TAC "y:hreal" THEN REFL_TAC);;

let HREAL_LT_NE = prove_thm(`HREAL_LT_NE`,
  "!x y. x hreal_lt y  ==> ~(x = y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDL);;

let HREAL_LT_ADDR = prove_thm(`HREAL_LT_ADDR`,
  "!x y. ~((x hreal_add y) hreal_lt x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_EQ_ADDL]);;

let HREAL_LT_GT = prove_thm(`HREAL_LT_GT`,
  "!x y. x hreal_lt y  ==> ~(y hreal_lt x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_EQ_ADDL]);;

let HREAL_LT_ADD2 = prove_thm(`HREAL_LT_ADD2`,
  "!x1 x2 y1 y2. x1 hreal_lt y1 /\ x2 hreal_lt y2 ==>
     (x1 hreal_add x2) hreal_lt (y1 hreal_add y2)",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN "d1:hreal" SUBST1_TAC)
    (X_CHOOSE_THEN "d2:hreal" SUBST1_TAC)) THEN
  EXISTS_TAC "d1 hreal_add d2" THEN
  CONV_TAC(AC_CONV(HREAL_ADD_ASSOC,HREAL_ADD_SYM)));;

let HREAL_LT_LADD = prove_thm(`HREAL_LT_LADD`,
  "!x y z. (x hreal_add y) hreal_lt (x hreal_add z) = y hreal_lt z",
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "d:hreal" ($THEN (EXISTS_TAC "d:hreal") o MP_TAC))
  THEN REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_EQ_LADD]);;

%----------------------------------------------------------------------------%
% CANCEL_CONV - Try to cancel, rearranging using AC laws as needed           %
%                                                                            %
% The first two arguments are the associative and commutative laws, as       %
% given to AC_CONV. The remaining list of theorems should be of the form:    %
%                                                                            %
% |- (a & b ~ a & c) = w (e.g. b ~ c)                                        %
% |-    (a & b ~ a)  = x (e.g. F)                                            %
% |-     (a ~ a & c) = y (e.g. T)                                            %
% |-         (a ~ a) = z (e.g. F)                                            %
%                                                                            %
% For some operator (written as infix &) and relation (~).                   %
%                                                                            %
% Theorems may be of the form |- ~ P or |- P, rather that equations; they    %
% will be transformed to |- P = F and |- P = T automatically if needed.      %
%                                                                            %
% Note that terms not cancelled will remain in their original order, but     %
% will be flattened to right-associated form.                                %
%----------------------------------------------------------------------------%

let CANCEL_CONV(assoc,sym,lcancelthms) tm =
  (let lcthms = map ((\th. (assert (is_eq o concl)) th ?
                    EQF_INTRO th ? EQT_INTRO th) o SPEC_ALL) lcancelthms in
   let [eqop; binop] = map
     (rator o rator o lhs o snd o strip_forall o concl) [hd lcthms; sym] in
   letrec strip_binop tm =
     if (rator(rator tm) = binop ? false) then
       (strip_binop (rand(rator tm))) @ (strip_binop(rand tm))
     else [tm] in
   let mk_binop = ((curry mk_comb) o (curry mk_comb binop)) in
   let list_mk_binop = end_itlist mk_binop in
   letrec rmel i l = if (l = []) then [] else
     let h.t = l in (i = h) => t | h.(rmel i t) in
   let (_,[l1;r1]) = (assert (curry$= eqop) # I) (strip_comb tm) in
   let [l; r] = map strip_binop [l1; r1] in
   let i = intersect l r in
   if i = [] then fail else
     let itm = list_mk_binop i in
     let [l'; r'] = map (end_itlist (C (curry $o)) (map rmel i)) [l; r] in
     let [l2; r2] = map (\ts. mk_binop itm (list_mk_binop ts) ? itm) [l';r'] in
     let [le; re] = map (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq)[l1,l2;r1,r2] in
     let eqv = MK_COMB(AP_TERM eqop le,re) in
     CONV_RULE(RAND_CONV(end_itlist $ORELSEC (map REWR_CONV lcthms))) eqv)
  ? failwith `CANCEL_CONV`;;

%----------------------------------------------------------------------------%
% Tactic to do all the obvious simplifications via cancellation etc.         %
%----------------------------------------------------------------------------%

let CANCEL_TAC = (C $THEN (PURE_REWRITE_TAC
      (filter($not o can (find_term is_pair o concl)) basic_rewrites)) o
     CONV_TAC o ONCE_DEPTH_CONV o end_itlist $ORELSEC) (map CANCEL_CONV
 [(HREAL_ADD_ASSOC,HREAL_ADD_SYM,
   [HREAL_EQ_LADD; HREAL_EQ_ADDL; HREAL_EQ_ADDR; EQ_SYM]);
  (HREAL_ADD_ASSOC,HREAL_ADD_SYM,
   [HREAL_LT_LADD; HREAL_LT_ADDL; HREAL_LT_ADDR; HREAL_LT_REFL])]);;

%----------------------------------------------------------------------------%
% Define operations on representatives.                                      %
%----------------------------------------------------------------------------%

let treal_0 = new_definition(`treal_0`,
  "treal_0 = (hreal_1,hreal_1)");;

let treal_1 = new_definition(`treal_1`,
  "treal_1 = (hreal_1 hreal_add hreal_1,hreal_1)");;

let treal_neg = new_definition(`treal_neg`,
  "treal_neg (x:hreal,y:hreal) = (y,x)");;

let treal_add = new_infix_definition(`treal_add`,
  "$treal_add (x1,y1) (x2,y2) = (x1 hreal_add x2, y1 hreal_add y2)");;

let treal_mul = new_infix_definition(`treal_mul`,
  "$treal_mul (x1,y1) (x2,y2) = ((x1 hreal_mul x2) hreal_add (y1 hreal_mul y2),
                          (x1 hreal_mul y2) hreal_add (y1 hreal_mul x2))");;

let treal_lt = new_infix_definition(`treal_lt`,
  "$treal_lt (x1,y1) (x2,y2) = (x1 hreal_add y2) hreal_lt (x2 hreal_add y1)");;

let treal_inv = new_definition(`treal_inv`,
  "treal_inv (x,y) =
         (x  = y) => treal_0 |
     y hreal_lt x => ((hreal_inv (x hreal_sub y)) hreal_add hreal_1,hreal_1)
                   | (hreal_1,(hreal_inv(y hreal_sub x)) hreal_add hreal_1)");;

%----------------------------------------------------------------------------%
% Define the equivalence relation and prove it *is* one                      %
%----------------------------------------------------------------------------%

let treal_eq = new_infix_definition(`treal_eq`,
  "$treal_eq (x1,y1) (x2,y2) = x1 hreal_add y2 = x2 hreal_add y1");;

let TREAL_EQ_REFL = prove_thm(`TREAL_EQ_REFL`,
  "!x. x treal_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN REFL_TAC);;

let TREAL_EQ_SYM = prove_thm(`TREAL_EQ_SYM`,
  "!x y. x treal_eq y = y treal_eq x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC);;

let TREAL_EQ_TRANS = prove_thm(`TREAL_EQ_TRANS`,
  "!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  DISCH_THEN(MP_TAC o MK_COMB o (AP_TERM "$hreal_add" # I) o CONJ_PAIR) THEN
  CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN CANCEL_TAC);;

let TREAL_EQ_EQUIV = prove_thm(`TREAL_EQ_EQUIV`,
  "!p q. p treal_eq q = ($treal_eq p = $treal_eq q)",
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV "r:hreal#hreal")) THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC "q:hreal#hreal") THEN REWRITE_TAC[TREAL_EQ_REFL];
      DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TREAL_EQ_SYM]); ALL_TAC] THEN
      POP_ASSUM(\th. DISCH_THEN(MP_TAC o CONJ th)) THEN
      MATCH_ACCEPT_TAC TREAL_EQ_TRANS]);;

let TREAL_EQ_AP = prove_thm(`TREAL_EQ_AP`,
  "!p q. (p = q) ==> p treal_eq q",
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TREAL_EQ_REFL);;

%----------------------------------------------------------------------------%
% Prove the properties of representatives                                    %
%----------------------------------------------------------------------------%

let TREAL_10 = prove_thm(`TREAL_10`,
  "~(treal_1 treal_eq treal_0)",
  REWRITE_TAC[treal_1; treal_0; treal_eq; HREAL_NOZERO]);;

let TREAL_ADD_SYM = prove_thm(`TREAL_ADD_SYM`,
  "!x y. x treal_add y = y treal_add x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [HREAL_ADD_SYM] THEN
  REFL_TAC);;

let TREAL_MUL_SYM = prove_thm(`TREAL_MUL_SYM`,
  "!x y. x treal_mul y = y treal_mul x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [HREAL_MUL_SYM] THEN
  REWRITE_TAC[PAIR_EQ] THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);;

let TREAL_ADD_ASSOC = prove_thm(`TREAL_ADD_ASSOC`,
  "!x y z. x treal_add (y treal_add z) = (x treal_add y) treal_add z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC]);;

let TREAL_MUL_ASSOC = prove_thm(`TREAL_MUL_ASSOC`,
  "!x y z. x treal_mul (y treal_mul z) = (x treal_mul y) treal_mul z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  REWRITE_TAC[HREAL_LDISTRIB; HREAL_RDISTRIB; PAIR_EQ; GSYM HREAL_MUL_ASSOC]
  THEN CONJ_TAC THEN CANCEL_TAC);;

let TREAL_LDISTRIB = prove_thm(`TREAL_LDISTRIB`,
  "!x y z. x treal_mul (y treal_add z) =
       (x treal_mul y) treal_add (x treal_mul z)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul; treal_add] THEN
  REWRITE_TAC[HREAL_LDISTRIB; PAIR_EQ] THEN
  CONJ_TAC THEN CANCEL_TAC);;

let TREAL_ADD_LID = prove_thm(`TREAL_ADD_LID`,
  "!x. (treal_0 treal_add x) treal_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0; treal_add; treal_eq] THEN
  CANCEL_TAC);;

let TREAL_MUL_LID = prove_thm(`TREAL_MUL_LID`,
  "!x. (treal_1 treal_mul x) treal_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_1; treal_mul; treal_eq] THEN
  REWRITE_TAC[HREAL_MUL_LID; HREAL_LDISTRIB; HREAL_RDISTRIB] THEN
  CANCEL_TAC);;

let TREAL_ADD_LINV = prove_thm(`TREAL_ADD_LINV`,
  "!x. ((treal_neg x) treal_add x) treal_eq treal_0",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg; treal_add; treal_eq; treal_0]
  THEN CANCEL_TAC);;

let TREAL_MUL_LINV = prove_thm(`TREAL_MUL_LINV`,
  "!x. ~(x treal_eq treal_0) ==>
              (((treal_inv x) treal_mul x) treal_eq treal_1)",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0; treal_eq; treal_inv] THEN
  CANCEL_TAC THEN DISCH_TAC THEN DISJ_CASES_THEN2
    (\th. MP_TAC th THEN ASM_REWRITE_TAC[]) (DISJ_CASES_THEN ASSUME_TAC)
    (SPECL ["FST (x:hreal#hreal)"; "SND (x:hreal#hreal)"] HREAL_LT_TOTAL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_LT_GT) THEN
  PURE_ASM_REWRITE_TAC[COND_CLAUSES; treal_mul; treal_eq; treal_1] THEN
  REWRITE_TAC[HREAL_MUL_LID; HREAL_LDISTRIB; HREAL_RDISTRIB] THEN
  CANCEL_TAC THEN W(SUBST1_TAC o SYM o C SPEC HREAL_MUL_LINV o
    find_term(\tm. rator(rator tm) = "$hreal_sub" ? false) o snd) THEN
  REWRITE_TAC[GSYM HREAL_LDISTRIB] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD) THEN REFL_TAC);;

let TREAL_LT_TOTAL = prove_thm(`TREAL_LT_TOTAL`,
  "!x y. x treal_eq y \/ x treal_lt y \/ y treal_lt x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt; treal_eq] THEN
  MATCH_ACCEPT_TAC HREAL_LT_TOTAL);;

let TREAL_LT_REFL = prove_thm(`TREAL_LT_REFL`,
  "!x. ~(x treal_lt x)",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  MATCH_ACCEPT_TAC HREAL_LT_REFL);;

let TREAL_LT_TRANS = prove_thm(`TREAL_LT_TRANS`,
  "!x y z. x treal_lt y /\ y treal_lt z ==> x treal_lt z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HREAL_LT_ADD2) THEN CANCEL_TAC THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [] [HREAL_ADD_SYM] THEN
  POP_ASSUM ACCEPT_TAC);;

let TREAL_LT_ADD = prove_thm(`TREAL_LT_ADD`,
  "!x y z. (y treal_lt z) ==> (x treal_add y) treal_lt (x treal_add z)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt; treal_add] THEN
  CANCEL_TAC);;

let TREAL_LT_MUL = prove_thm(`TREAL_LT_MUL`,
  "!x y. treal_0 treal_lt x /\ treal_0 treal_lt y ==>
           treal_0 treal_lt (x treal_mul y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0; treal_lt; treal_mul] THEN
  CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[HREAL_LT])) THEN
  REWRITE_TAC[HREAL_LDISTRIB; HREAL_RDISTRIB] THEN CANCEL_TAC);;

%----------------------------------------------------------------------------%
% Rather than grub round proving the supremum property for representatives,  %
% we prove the appropriate order-isomorphism {x::R|0 < r} <-> R^+            %
%----------------------------------------------------------------------------%

let treal_of_hreal = new_definition(`treal_of_hreal`,
  "treal_of_hreal x = (x hreal_add hreal_1,hreal_1)");;

let hreal_of_treal = new_definition(`hreal_of_treal`,
  "hreal_of_treal (x,y) = @d. x = y hreal_add d");;

let TREAL_BIJ = prove_thm(`TREAL_BIJ`,
  "(!h. (hreal_of_treal(treal_of_hreal h)) = h) /\
   (!r. treal_0 treal_lt r = (treal_of_hreal(hreal_of_treal r)) treal_eq r)",
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[treal_of_hreal; hreal_of_treal] THEN
    CANCEL_TAC THEN CONV_TAC SYM_CONV THEN
    CONV_TAC(funpow 2 RAND_CONV ETA_CONV) THEN
    MATCH_MP_TAC SELECT_AX THEN EXISTS_TAC "h:hreal" THEN REFL_TAC;
    GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0; treal_lt; treal_eq;
      treal_of_hreal; hreal_of_treal] THEN CANCEL_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP HREAL_SUB_ADD) THEN
      DISCH_THEN(CONV_TAC o RAND_CONV o REWR_CONV o SYM o SELECT_RULE o
      EXISTS("?d. d hreal_add (SND r) = FST r", "(FST r) hreal_sub (SND r)"))
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [HREAL_ADD_SYM] THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN REFL_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN CANCEL_TAC]]);;

let TREAL_ISO = prove_thm(`TREAL_ISO`,
  "!h i. h hreal_lt i ==> (treal_of_hreal h) treal_lt (treal_of_hreal i)",
  REPEAT GEN_TAC THEN REWRITE_TAC[treal_of_hreal; treal_lt] THEN CANCEL_TAC);;

let TREAL_BIJ_WELLDEF = prove_thm(`TREAL_BIJ_WELLDEF`,
  "!h i. h treal_eq i ==> (hreal_of_treal h = hreal_of_treal i)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq; hreal_of_treal] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC(X_FUN_EQ_CONV "d:hreal") THEN
  GEN_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM "SND(i:hreal#hreal)" o AP_TERM "$hreal_add")
    THEN POP_ASSUM SUBST1_TAC;
    DISCH_THEN(MP_TAC o C AP_THM "SND(h:hreal#hreal)" o AP_TERM "$hreal_add")
    THEN POP_ASSUM(SUBST1_TAC o SYM)] THEN
  CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);;

%----------------------------------------------------------------------------%
% Prove that the operations on representatives are well-defined              %
%----------------------------------------------------------------------------%

let TREAL_NEG_WELLDEF = prove_thm(`TREAL_NEG_WELLDEF`,
  "!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg; treal_eq] THEN
  DISCH_THEN($THEN (ONCE_REWRITE_TAC[HREAL_ADD_SYM]) o SUBST1_TAC) THEN
  REFL_TAC);;

let TREAL_ADD_WELLDEFR = prove_thm(`TREAL_ADD_WELLDEFR`,
  "!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add; treal_eq] THEN
  CANCEL_TAC);;

let TREAL_ADD_WELLDEF = prove_thm(`TREAL_ADD_WELLDEF`,
  "!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_add y1) treal_eq (x2 treal_add y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC "x1 treal_add y2" THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_ADD_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC TREAL_ADD_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TREAL_MUL_WELLDEFR = prove_thm(`TREAL_MUL_WELLDEFR`,
  "!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul; treal_eq] THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    "(a hreal_add b) hreal_add (c hreal_add d) =
     (a hreal_add d) hreal_add (b hreal_add c)"] THEN
  REWRITE_TAC[GSYM HREAL_RDISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);;

let TREAL_MUL_WELLDEF = prove_thm(`TREAL_MUL_WELLDEF`,
  "!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC "x1 treal_mul y2" THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_MUL_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC TREAL_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TREAL_LT_WELLDEFR = prove_thm(`TREAL_LT_WELLDEFR`,
  "!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_lt y = x2 treal_lt y)",
  let mkc v tm = SYM(SPECL (v.snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt; treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc "SND (x1:hreal#hreal)")) THEN
  CONV_TAC(LAND_CONV(mkc "SND (x2:hreal#hreal)")) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    "a hreal_add (b hreal_add c) = (b hreal_add a) hreal_add c"] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC);;

let TREAL_LT_WELLDEFL = prove_thm(`TREAL_LT_WELLDEFL`,
  "!x y1 y2. y1 treal_eq y2 ==> (x treal_lt y1 = x treal_lt y2)",
  let mkc v tm = SYM(SPECL (v.snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt; treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc "FST (y1:hreal#hreal)")) THEN
  CONV_TAC(LAND_CONV(mkc "FST (y2:hreal#hreal)")) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    "a hreal_add (b hreal_add c) = (a hreal_add c) hreal_add b"] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN CANCEL_TAC);;

let TREAL_LT_WELLDEF = prove_thm(`TREAL_LT_WELLDEF`,
  "!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_lt y1 = x2 treal_lt y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC "x1 treal_lt y2" THEN CONJ_TAC THENL
   [MATCH_MP_TAC TREAL_LT_WELLDEFL; MATCH_MP_TAC TREAL_LT_WELLDEFR] THEN
  ASM_REWRITE_TAC[]);;

let TREAL_INV_WELLDEF = prove_thm(`TREAL_INV_WELLDEF`,
  "!x1 x2. x1 treal_eq x2 ==> (treal_inv x1) treal_eq (treal_inv x2)",
  let lemma1 = PROVE
   ("(a hreal_add b' = b hreal_add a') ==>
        (a' hreal_lt a = b' hreal_lt b)",
    DISCH_TAC THEN EQ_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[HREAL_LT]) THEN
    POP_ASSUM MP_TAC THEN CANCEL_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM); DISCH_THEN SUBST1_TAC] THEN CANCEL_TAC)
  and lemma2 = PROVE
   ("(a hreal_add b' = b hreal_add a') ==>
        ((a = a') = (b = b'))",
    DISCH_TAC THEN EQ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC
    THEN CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_inv; treal_eq] THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma1) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma2) THEN COND_CASES_TAC THEN
  REWRITE_TAC[TREAL_EQ_REFL] THEN COND_CASES_TAC THEN REWRITE_TAC[treal_eq]
  THEN CANCEL_TAC THEN AP_TERM_TAC THEN
  W(FREEZE_THEN(CONV_TAC o REWR_CONV) o GSYM o C SPEC HREAL_EQ_LADD o
    mk_comb o (curry mk_comb "$hreal_add" # I) o (rand # rand) o dest_eq o snd)
  THEN ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [] [HREAL_ADD_SYM] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC] THENL
   [RULE_ASSUM_TAC GSYM;
    MP_TAC(SPECL["FST(x2:hreal#hreal)"; "SND(x2:hreal#hreal)"]
    HREAL_LT_TOTAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[HREAL_ADD_SYM])] THEN
  FIRST_ASSUM(\th. FIRST_ASSUM(MP_TAC o EQ_MP (MATCH_MP lemma1 th))) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert(curry$="$hreal_lt" o rator o rator) o concl)
  THEN REPEAT(DISCH_THEN(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD)) THEN
  FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);;

%----------------------------------------------------------------------------%
% Now define the functions over the equivalence classes                      %
%----------------------------------------------------------------------------%

let [REAL_10; REAL_ADD_SYM; REAL_MUL_SYM; REAL_ADD_ASSOC;
     REAL_MUL_ASSOC; REAL_LDISTRIB; REAL_ADD_LID; REAL_MUL_LID;
     REAL_ADD_LINV; REAL_MUL_LINV; REAL_LT_TOTAL; REAL_LT_REFL;
     REAL_LT_TRANS; REAL_LT_IADD; REAL_LT_MUL; REAL_BIJ; REAL_ISO] =
  define_equivalence_type `real` TREAL_EQ_EQUIV
    [("treal_0",         `r0`,            false);
     ("treal_1",         `r1`,            false);
     ("treal_neg",       `real_neg`,      false);
     ("treal_inv",       `real_inv`,      false);
     ("$treal_add",      `real_add`,      true);
     ("$treal_mul",      `real_mul`,      true);
     ("$treal_lt",       `real_lt`,       true);
     ("$treal_of_hreal", `real_of_hreal`, false);
     ("$hreal_of_treal", `hreal_of_real`, false)]
    [TREAL_NEG_WELLDEF; TREAL_INV_WELLDEF; TREAL_LT_WELLDEF;
     TREAL_ADD_WELLDEF; TREAL_MUL_WELLDEF; TREAL_BIJ_WELLDEF]
    ([TREAL_10] @
     (map (GEN_ALL o MATCH_MP TREAL_EQ_AP o SPEC_ALL)
       [TREAL_ADD_SYM; TREAL_MUL_SYM; TREAL_ADD_ASSOC;
        TREAL_MUL_ASSOC; TREAL_LDISTRIB]) @
      [TREAL_ADD_LID; TREAL_MUL_LID; TREAL_ADD_LINV; TREAL_MUL_LINV;
       TREAL_LT_TOTAL; TREAL_LT_REFL;TREAL_LT_TRANS; TREAL_LT_ADD;
       TREAL_LT_MUL; TREAL_BIJ; TREAL_ISO]);;

%----------------------------------------------------------------------------%
% Transfer of supremum property for all-positive sets - bit painful          %
%----------------------------------------------------------------------------%

let REAL_ISO_EQ = prove_thm(`REAL_ISO_EQ`,
  "!h i. h hreal_lt i = (real_of_hreal h) real_lt (real_of_hreal i)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC REAL_ISO;
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL ["h:hreal"; "i:hreal"] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    POP_ASSUM(\th. DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_ISO th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_REFL]]);;

let REAL_POS = prove_thm(`REAL_POS`,
  "!X. r0 real_lt (real_of_hreal X)",
  GEN_TAC THEN REWRITE_TAC[REAL_BIJ]);;

let SUP_ALLPOS_LEMMA1 = prove_thm(`SUP_ALLPOS_LEMMA1`,
  "(!x. P x ==> r0 real_lt x) ==>
     ((?x. P x /\ y real_lt x) =
      (?X. P(real_of_hreal X) /\ y real_lt (real_of_hreal X)))",
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN "x:real" (\th. MP_TAC th THEN POP_ASSUM
     (SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ] o C MATCH_MP (CONJUNCT1 th))))
    THEN DISCH_TAC THEN EXISTS_TAC "hreal_of_real x" THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN "X:hreal" ASSUME_TAC) THEN
    EXISTS_TAC "real_of_hreal X" THEN ASM_REWRITE_TAC[]]);;

let SUP_ALLPOS_LEMMA2 = prove_thm(`SUP_ALLPOS_LEMMA2`,
  "P(real_of_hreal X) :bool = (\h. P(real_of_hreal h)) X",
  BETA_TAC THEN REFL_TAC);;

let SUP_ALLPOS_LEMMA3 = prove_thm(`SUP_ALLPOS_LEMMA3`,
  "(!x. P x ==> r0 real_lt x) /\ (?x. P x) /\ (?z. !x. P x ==> x real_lt z)
      ==> (?X. (\h. P(real_of_hreal h)) X) /\
          (?Y. !X. (\h. P(real_of_hreal h)) X ==> X hreal_lt Y)",
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [EXISTS_TAC "hreal_of_real x" THEN BETA_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[REAL_BIJ] o
                C MATCH_MP (ASSUME "(P:real->bool) x")) THEN
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC "hreal_of_real z" THEN BETA_TAC THEN GEN_TAC THEN
    UNDISCH_TAC "(P:real->bool) x" THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(\th. EVERY_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[REAL_ISO_EQ] THEN
    MP_TAC(SPECL["r0"; "real_of_hreal X"; "z:real"] REAL_LT_TRANS) THEN
    ASM_REWRITE_TAC[REAL_BIJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let SUP_ALLPOS_LEMMA4 = prove_thm(`SUP_ALLPOS_LEMMA4`,
  "!y. ~(r0 real_lt y) ==> !x. y real_lt (real_of_hreal x)",
  GEN_TAC THEN DISCH_THEN($THEN GEN_TAC o MP_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL ["y:real"; "r0"] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM(MP_TAC o C CONJ (SPEC "x:hreal" REAL_POS)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_TRANS));;

let REAL_SUP_ALLPOS = prove_thm(`REAL_SUP_ALLPOS`,
  "!P. (!x. P x ==> r0 real_lt x) /\ (?x. P x) /\ (?z. !x. P x ==> x real_lt z)
    ==> (?s. !y. (?x. P x /\ y real_lt x) = y real_lt s)",
  let lemma = TAUT_CONV "a /\ b ==> (a = b)" in
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC "real_of_hreal(hreal_sup(\h. P(real_of_hreal h)))" THEN GEN_TAC
  THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUP_ALLPOS_LEMMA1 o CONJUNCT1) THEN
  ASM_CASES_TAC "r0 real_lt y" THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ]) THEN
    REWRITE_TAC[GSYM REAL_ISO_EQ] THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [] [SUP_ALLPOS_LEMMA2] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_SUP o MATCH_MP SUP_ALLPOS_LEMMA3)
    THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SUP_ALLPOS_LEMMA3) THEN
      BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC "X:hreal" o CONJUNCT1) THEN
      EXISTS_TAC "X:hreal" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SUP_ALLPOS_LEMMA4)]);;

%----------------------------------------------------------------------------%
% Now save all the unsaved theorems                                          %
%----------------------------------------------------------------------------%

map save_thm
 [`REAL_10`,REAL_10;               `REAL_ADD_SYM`,REAL_ADD_SYM;
  `REAL_MUL_SYM`,REAL_MUL_SYM;     `REAL_ADD_ASSOC`,REAL_ADD_ASSOC;
  `REAL_MUL_ASSOC`,REAL_MUL_ASSOC; `REAL_LDISTRIB`,REAL_LDISTRIB;
  `REAL_ADD_LID`,REAL_ADD_LID;     `REAL_MUL_LID`,REAL_MUL_LID;
  `REAL_ADD_LINV`,REAL_ADD_LINV;   `REAL_MUL_LINV`,REAL_MUL_LINV;
  `REAL_LT_TOTAL`,REAL_LT_TOTAL;   `REAL_LT_REFL`,REAL_LT_REFL;
  `REAL_LT_TRANS`,REAL_LT_TRANS;   `REAL_LT_IADD`,REAL_LT_IADD;
  `REAL_LT_MUL`,REAL_LT_MUL];;

close_theory();;
