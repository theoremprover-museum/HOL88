%============================================================================%
% Theory of integers.                                                        %
%                                                                            %
% The integers are constructed as equivalence classes of pairs of integers   %
% using the quotient type procedure in "equiv.ml".                           %
%                                                                            %
% This theory was constructed for use in the HOL-ELLA system, using many of  %
% the principles, and some of the code, used in the reals library. It is my  %
% eventual intention to produce a more unified library of number systems.    %
%============================================================================%

can unlink `INT.th`;;

new_theory `INT`;;

loadt `useful`;;

loadt `equiv`;;

%----------------------------------------------------------------------------%
% Required lemmas about the natural numbers - mostly to drive CANCEL_TAC     %
%----------------------------------------------------------------------------%

let EQ_LADD = prove_thm(`EQ_LADD`,
  "!x y z. (x + y = x + z) = (y = z)",
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_ACCEPT_TAC EQ_MONO_ADD_EQ);;

let EQ_ADDL = prove_thm(`EQ_ADDL`,
  "!x y. (x = x + y) = (y = 0)",
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC ADD_INV_0_EQ);;

let LT_LADD = prove_thm(`LT_LADD`,
  "!x y z. (x + y) < (x + z) = y < z",
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_ACCEPT_TAC LESS_MONO_ADD_EQ);;

let LT_ADDL = prove_thm(`LT_ADDL`,
  "!x y. x < (x + y) = 0 < y",
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL ["x:num"; "0"; "y:num"] LT_LADD) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let LT_ADDR = prove_thm(`LT_ADDR`,
  "!x y. ~((x + y) < x)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC o MATCH_MP LESS_ADD_1) THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ADD_INV_0_EQ] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; NOT_SUC]);;

let LT_ADD2 = prove_thm(`LT_ADD2`,
  "!x1 x2 y1 y2. x1 < y1 /\ x2 < y2 ==> (x1 + x2) < (y1 + y2)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(CHOOSE_TAC o MATCH_MP LESS_ADD_1)) THEN
  ASM_REWRITE_TAC[GSYM ADD1] THEN
  ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
    "(a + b) + (c + d) = (a + c) + (b + d)"] THEN
  REWRITE_TAC[LT_ADDL] THEN
  REWRITE_TAC[ADD_CLAUSES; LESS_0]);;

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
 [(ADD_ASSOC,ADD_SYM,
   [EQ_LADD; EQ_ADDL; ADD_INV_0_EQ; EQ_SYM_EQ]);
  (ADD_ASSOC,ADD_SYM,
   [LT_LADD; LT_ADDL; LT_ADDR; LESS_REFL])]);;

%----------------------------------------------------------------------------%
% Define operations on representatives.                                      %
%----------------------------------------------------------------------------%

let tint_0 = new_definition(`tint_0`,
  "tint_0 = (1,1)");;

let tint_1 = new_definition(`tint_1`,
  "tint_1 = (1 + 1,1)");;

let tint_neg = new_definition(`tint_neg`,
  "tint_neg (x:num,y:num) = (y,x)");;

let tint_add = new_infix_definition(`tint_add`,
  "$tint_add (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)");;

let tint_mul = new_infix_definition(`tint_mul`,
  "$tint_mul (x1,y1) (x2,y2) = ((x1 * x2) + (y1 * y2),
                                (x1 * y2) + (y1 * x2))");;

let tint_lt = new_infix_definition(`tint_lt`,
  "$tint_lt (x1,y1) (x2,y2) = (x1 + y2) < (x2 + y1)");;

%----------------------------------------------------------------------------%
% Define the equivalence relation and prove it *is* one                      %
%----------------------------------------------------------------------------%

let tint_eq = new_infix_definition(`tint_eq`,
  "$tint_eq (x1,y1) (x2,y2) = x1 + y2 = x2 + y1");;

let TINT_EQ_REFL = prove_thm(`TINT_EQ_REFL`,
  "!x. x tint_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_eq] THEN REFL_TAC);;

let TINT_EQ_SYM = prove_thm(`TINT_EQ_SYM`,
  "!x y. x tint_eq y = y tint_eq x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_eq] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC);;

let TINT_EQ_TRANS = prove_thm(`TINT_EQ_TRANS`,
  "!x y z. x tint_eq y /\ y tint_eq z ==> x tint_eq z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_eq] THEN
  DISCH_THEN(MP_TAC o MK_COMB o (AP_TERM "$+" # I) o CONJ_PAIR) THEN
  CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN CANCEL_TAC);;

let TINT_EQ_EQUIV = prove_thm(`TINT_EQ_EQUIV`,
  "!p q. p tint_eq q = ($tint_eq p = $tint_eq q)",
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV "r:num#num")) THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC "q:num#num") THEN REWRITE_TAC[TINT_EQ_REFL];
      DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TINT_EQ_SYM]); ALL_TAC] THEN
      POP_ASSUM(\th. DISCH_THEN(MP_TAC o CONJ th)) THEN
      MATCH_ACCEPT_TAC TINT_EQ_TRANS]);;

let TINT_EQ_AP = prove_thm(`TINT_EQ_AP`,
  "!p q. (p = q) ==> p tint_eq q",
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TINT_EQ_REFL);;

%----------------------------------------------------------------------------%
% Prove the properties of representatives                                    %
%----------------------------------------------------------------------------%

let TINT_10 = prove_thm(`TINT_10`,
  "~(tint_1 tint_eq tint_0)",
  REWRITE_TAC[tint_1; tint_0; tint_eq] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ADD_INV_0_EQ] THEN
  REWRITE_TAC[num_CONV "1"; NOT_SUC]);;

let TINT_ADD_SYM = prove_thm(`TINT_ADD_SYM`,
  "!x y. x tint_add y = y tint_add x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_add] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [ADD_SYM] THEN
  REFL_TAC);;

let TINT_MUL_SYM = prove_thm(`TINT_MUL_SYM`,
  "!x y. x tint_mul y = y tint_mul x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [MULT_SYM] THEN
  REWRITE_TAC[PAIR_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM);;

let TINT_ADD_ASSOC = prove_thm(`TINT_ADD_ASSOC`,
  "!x y z. x tint_add (y tint_add z) = (x tint_add y) tint_add z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_add] THEN
  REWRITE_TAC[ADD_ASSOC]);;

let TINT_MUL_ASSOC = prove_thm(`TINT_MUL_ASSOC`,
  "!x y z. x tint_mul (y tint_mul z) = (x tint_mul y) tint_mul z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; PAIR_EQ; GSYM MULT_ASSOC]
  THEN CONJ_TAC THEN CANCEL_TAC);;

let TINT_LDISTRIB = prove_thm(`TINT_LDISTRIB`,
  "!x y z. x tint_mul (y tint_add z) =
       (x tint_mul y) tint_add (x tint_mul z)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul; tint_add] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; PAIR_EQ] THEN
  CONJ_TAC THEN CANCEL_TAC);;

let TINT_ADD_LID = prove_thm(`TINT_ADD_LID`,
  "!x. (tint_0 tint_add x) tint_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_0; tint_add; tint_eq] THEN
  CANCEL_TAC);;

let TINT_MUL_LID = prove_thm(`TINT_MUL_LID`,
  "!x. (tint_1 tint_mul x) tint_eq x",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_1; tint_mul; tint_eq] THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  CANCEL_TAC);;

let TINT_ADD_LINV = prove_thm(`TINT_ADD_LINV`,
  "!x. ((tint_neg x) tint_add x) tint_eq tint_0",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_neg; tint_add; tint_eq; tint_0]
  THEN CANCEL_TAC);;

let TINT_LT_TOTAL = prove_thm(`TINT_LT_TOTAL`,
  "!x y. x tint_eq y \/ x tint_lt y \/ y tint_lt x",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt; tint_eq] THEN
  MP_TAC(SPECL ["FST(x:num#num) + SND(y:num#num)";
                "FST(y:num#num) + SND(x:num#num)"] LESS_CASES) THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LESS_OR_EQ]) THEN
  POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let TINT_LT_REFL = prove_thm(`TINT_LT_REFL`,
  "!x. ~(x tint_lt x)",
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt] THEN
  MATCH_ACCEPT_TAC LESS_REFL);;

let TINT_LT_TRANS = prove_thm(`TINT_LT_TRANS`,
  "!x y z. x tint_lt y /\ y tint_lt z ==> x tint_lt z",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LT_ADD2) THEN CANCEL_TAC THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [] [ADD_SYM] THEN
  POP_ASSUM ACCEPT_TAC);;

let TINT_LT_ADD = prove_thm(`TINT_LT_ADD`,
  "!x y z. (y tint_lt z) ==> (x tint_add y) tint_lt (x tint_add z)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt; tint_add] THEN
  CANCEL_TAC);;

let TINT_LT_MUL = prove_thm(`TINT_LT_MUL`,
  "!x y. tint_0 tint_lt x /\ tint_0 tint_lt y ==>
            tint_0 tint_lt (x tint_mul y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_0; tint_lt; tint_mul] THEN
  CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1)) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN CANCEL_TAC THEN
  REWRITE_TAC[num_CONV "1"; MULT_CLAUSES; ADD_CLAUSES; LESS_0]);;

%----------------------------------------------------------------------------%
% Prove that the operations on representatives are well-defined              %
%----------------------------------------------------------------------------%

let TINT_NEG_WELLDEF = prove_thm(`TINT_NEG_WELLDEF`,
  "!x1 x2. x1 tint_eq x2 ==> (tint_neg x1) tint_eq (tint_neg x2)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_neg; tint_eq] THEN
  DISCH_THEN($THEN (ONCE_REWRITE_TAC[ADD_SYM]) o SUBST1_TAC) THEN
  REFL_TAC);;

let TINT_ADD_WELLDEFR = prove_thm(`TINT_ADD_WELLDEFR`,
  "!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_add y) tint_eq (x2 tint_add y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_add; tint_eq] THEN
  CANCEL_TAC);;

let TINT_ADD_WELLDEF = prove_thm(`TINT_ADD_WELLDEF`,
  "!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
     (x1 tint_add y1) tint_eq (x2 tint_add y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TINT_EQ_TRANS THEN EXISTS_TAC "x1 tint_add y2" THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TINT_ADD_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC TINT_ADD_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TINT_MUL_WELLDEFR = prove_thm(`TINT_MUL_WELLDEFR`,
  "!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_mul y) tint_eq (x2 tint_mul y)",
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_mul; tint_eq] THEN
  ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
    "(a + b) + (c + d) =
     (a + d) + (b + c)"] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);;

let TINT_MUL_WELLDEF = prove_thm(`TINT_MUL_WELLDEF`,
  "!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
     (x1 tint_mul y1) tint_eq (x2 tint_mul y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TINT_EQ_TRANS THEN EXISTS_TAC "x1 tint_mul y2" THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TINT_MUL_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC TINT_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TINT_LT_WELLDEFR = prove_thm(`TINT_LT_WELLDEFR`,
  "!x1 x2 y. x1 tint_eq x2 ==> (x1 tint_lt y = x2 tint_lt y)",
  let mkc v tm = SYM(SPECL (v.snd(strip_comb tm)) LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt; tint_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc "SND (x1:num#num)")) THEN
  CONV_TAC(LAND_CONV(mkc "SND (x2:num#num)")) THEN
  ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
    "a + (b + c) = (b + a) + c"] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC);;

let TINT_LT_WELLDEFL = prove_thm(`TINT_LT_WELLDEFL`,
  "!x y1 y2. y1 tint_eq y2 ==> (x tint_lt y1 = x tint_lt y2)",
  let mkc v tm = SYM(SPECL (v.snd(strip_comb tm)) LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[tint_lt; tint_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc "FST (y1:num#num)")) THEN
  CONV_TAC(LAND_CONV(mkc "FST (y2:num#num)")) THEN
  ONCE_REWRITE_TAC[AC(ADD_ASSOC,ADD_SYM)
    "a + (b + c) = (a + c) + b"] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN CANCEL_TAC);;

let TINT_LT_WELLDEF = prove_thm(`TINT_LT_WELLDEF`,
  "!x1 x2 y1 y2. x1 tint_eq x2 /\ y1 tint_eq y2 ==>
     (x1 tint_lt y1 = x2 tint_lt y2)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC "x1 tint_lt y2" THEN CONJ_TAC THENL
   [MATCH_MP_TAC TINT_LT_WELLDEFL; MATCH_MP_TAC TINT_LT_WELLDEFR] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Now define the functions over the equivalence classes                      %
%----------------------------------------------------------------------------%

let [INT_10; INT_ADD_SYM; INT_MUL_SYM;
     INT_ADD_ASSOC; INT_MUL_ASSOC; INT_LDISTRIB;
     INT_ADD_LID; INT_MUL_LID; INT_ADD_LINV;
     INT_LT_TOTAL; INT_LT_REFL; INT_LT_TRANS;
     INT_LT_LADD_IMP; INT_LT_MUL] =
  define_equivalence_type `int` TINT_EQ_EQUIV
    [("tint_0",         `int_0`,        false);
     ("tint_1",         `int_1`,        false);
     ("tint_neg",       `int_neg`,      false);
     ("$tint_add",      `int_add`,      true);
     ("$tint_mul",      `int_mul`,      true);
     ("$tint_lt",       `int_lt`,       true)]
    [TINT_NEG_WELLDEF; TINT_LT_WELLDEF; TINT_ADD_WELLDEF; TINT_MUL_WELLDEF]
    ([TINT_10] @
     (map (GEN_ALL o MATCH_MP TINT_EQ_AP o SPEC_ALL)
       [TINT_ADD_SYM; TINT_MUL_SYM; TINT_ADD_ASSOC;
        TINT_MUL_ASSOC; TINT_LDISTRIB]) @
      [TINT_ADD_LID; TINT_MUL_LID; TINT_ADD_LINV;
       TINT_LT_TOTAL; TINT_LT_REFL; TINT_LT_TRANS;
       TINT_LT_ADD; TINT_LT_MUL]);;

let int_tybij = definition `-` `int_tybij`;;

%----------------------------------------------------------------------------%
% Define subtraction and the other orderings                                 %
%----------------------------------------------------------------------------%

let int_sub = new_infix_definition(`int_sub`,
  "$int_sub x y = x int_add (int_neg y)");;

let int_le = new_infix_definition(`int_le`,
  "$int_le x y = ~(y int_lt x)");;

let int_gt = new_infix_definition(`int_gt`,
  "$int_gt x y = y int_lt x");;

let int_ge = new_infix_definition(`int_ge`,
  "$int_ge x y = y int_le x");;

%----------------------------------------------------------------------------%
% Now define the inclusion homomorphism int_of_num:num->int.                 %
%----------------------------------------------------------------------------%

let int_of_num = new_prim_rec_definition(`int_of_num`,
  "(int_of_num 0 = int_0) /\
   (int_of_num (SUC n) = (int_of_num n) int_add int_1)");;

let INT_0 = prove_thm(`INT_0`,
  "int_0 = int_of_num 0",
  REWRITE_TAC[int_of_num]);;

let INT_1 = prove_thm(`INT_1`,
  "int_1 = int_of_num 1",
  REWRITE_TAC[num_CONV "1"; int_of_num; INT_ADD_LID]);;

%----------------------------------------------------------------------------%
% Set up a nice interface map. Use & for the inclusion homomorphism; adjust  %
% theorems retrospectively to use &n as "notation" for int constants.       %
%----------------------------------------------------------------------------%

new_special_symbol `--`;;

set_interface_map
[               `--`,`int_neg`;
 `num_add`,`+`;  `+`,`int_add`;
 `num_mul`,`*`;  `*`,`int_mul`;
 `num_sub`,`-`;  `-`,`int_sub`;
 `num_lt`,`<` ;  `<`,`int_lt`;
 `num_le`,`<=`; `<=`,`int_le`;
 `num_gt`,`>` ;  `>`,`int_gt`;
 `num_ge`,`>=`; `>=`,`int_ge`;
                 `&`,`int_of_num`];;

let reeducate (s,t) = save_thm(s,REWRITE_RULE[INT_0; INT_1] t);;

let thlist =
 [`INT_10`,INT_10;
  `INT_ADD_SYM`,INT_ADD_SYM;
  `INT_MUL_SYM`,INT_MUL_SYM;
  `INT_ADD_ASSOC`,INT_ADD_ASSOC;
  `INT_MUL_ASSOC`,INT_MUL_ASSOC;
  `INT_ADD_LID`,INT_ADD_LID;
  `INT_MUL_LID`,INT_MUL_LID;
  `INT_ADD_LINV`,INT_ADD_LINV;
  `INT_LDISTRIB`,INT_LDISTRIB;
  `INT_LT_TOTAL`,INT_LT_TOTAL;
  `INT_LT_REFL`,INT_LT_REFL;
  `INT_LT_TRANS`,INT_LT_TRANS;
  `INT_LT_LADD_IMP`,INT_LT_LADD_IMP;
  `INT_LT_MUL`,INT_LT_MUL] in

do (map reeducate thlist; map (load_theorem `-` o fst) thlist);;

%----------------------------------------------------------------------------%
% Prove lots of boring field theorems                                        %
%----------------------------------------------------------------------------%

let INT_ADD_RID = prove_thm(`INT_ADD_RID`,
  "!x. x + &0 = x",
  GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_ADD_LID);;

let INT_ADD_RINV = prove_thm(`INT_ADD_RINV`,
  "!x. x + (--x) = &0",
  GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_ADD_LINV);;

let INT_MUL_RID = prove_thm(`INT_MUL_RID`,
  "!x. x * &1 = x",
  GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_MUL_LID);;

let INT_RDISTRIB = prove_thm(`INT_RDISTRIB`,
  "!x y z. (x + y) * z = (x * z) + (y * z)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_LDISTRIB);;

let INT_EQ_LADD = prove_thm(`INT_EQ_LADD`,
  "!x y z. (x + y = x + z) = (y = z)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM "$+ (-- x)") THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let INT_EQ_RADD = prove_thm(`INT_EQ_RADD`,
  "!x y z. (x + z = y + z) = (x = y)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_EQ_LADD);;

let INT_ADD_LID_UNIQ = prove_thm(`INT_ADD_LID_UNIQ`,
  "!x y. (x + y = y) = (x = &0)",
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [GSYM INT_ADD_LID]
  THEN MATCH_ACCEPT_TAC INT_EQ_RADD);;

let INT_ADD_RID_UNIQ = prove_thm(`INT_ADD_RID_UNIQ`,
  "!x y. (x + y = x) = (y = &0)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_ADD_LID_UNIQ);;

let INT_LNEG_UNIQ = prove_thm(`INT_LNEG_UNIQ`,
  "!x y. (x + y = &0) = (x = --y)",
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC "y:int" INT_ADD_LINV)) THEN
  MATCH_ACCEPT_TAC INT_EQ_RADD);;

let INT_RNEG_UNIQ = prove_thm(`INT_RNEG_UNIQ`,
  "!x y. (x + y = &0) = (y = --x)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_LNEG_UNIQ);;

let INT_NEG_ADD = prove_thm(`INT_NEG_ADD`,
  "!x y. --(x + y) = (--x) + (--y)",
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM INT_LNEG_UNIQ] THEN
  ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
    "(a + b) + (c + d) = (a + c) + (b + d)"] THEN
  REWRITE_TAC[INT_ADD_LINV; INT_ADD_LID]);;

let INT_MUL_LZERO = prove_thm(`INT_MUL_LZERO`,
  "!x. &0 * x = &0",
  GEN_TAC THEN SUBST1_TAC(SYM(SPECL ["&0 * x"; "&0 * x"] INT_ADD_LID_UNIQ))
  THEN REWRITE_TAC[GSYM INT_RDISTRIB; INT_ADD_LID]);;

let INT_MUL_RZERO = prove_thm(`INT_MUL_RZERO`,
  "!x. x * &0 = &0",
  GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_MUL_LZERO);;

let INT_NEG_LMUL = prove_thm(`INT_NEG_LMUL`,
  "!x y. --(x * y) = (--x) * y",
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM INT_LNEG_UNIQ; GSYM INT_RDISTRIB;
              INT_ADD_LINV; INT_MUL_LZERO]);;

let INT_NEG_RMUL = prove_thm(`INT_NEG_RMUL`,
  "!x y. --(x * y) = x * (--y)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_NEG_LMUL);;

let INT_NEGNEG = prove_thm(`INT_NEGNEG`,
  "!x. --(--x) = x",
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM INT_LNEG_UNIQ; INT_ADD_RINV]);;

let INT_NEG_MUL2 = prove_thm(`INT_NEG_MUL2`,
  "!x y. (--x) * (--y) = x * y",
  REWRITE_TAC[GSYM INT_NEG_LMUL; GSYM INT_NEG_RMUL; INT_NEGNEG]);;

let INT_LT_LADD = prove_thm(`INT_LT_LADD`,
  "!x y z. (x + y) < (x + z) = y < z",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC "--x" o MATCH_MP INT_LT_LADD_IMP) THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID];
    MATCH_ACCEPT_TAC INT_LT_LADD_IMP]);;

let INT_LT_RADD = prove_thm(`INT_LT_RADD`,
  "!x y z. (x + z) < (y + z) = x < y",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_LT_LADD);;

let INT_NOT_LT = prove_thm(`INT_NOT_LT`,
  "!x y. ~(x < y) = y <= x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);;

let INT_LT_ANTISYM = prove_thm(`INT_LT_ANTISYM`,
  "!x y. ~(x < y /\ y < x)",
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_TRANS) THEN
  REWRITE_TAC[INT_LT_REFL]);;

let INT_LT_GT = prove_thm(`INT_LT_GT`,
  "!x y. x < y ==> ~(y < x)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(\th. DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[INT_LT_ANTISYM]);;

let INT_NOT_LE = prove_thm(`INT_NOT_LE`,
  "!x y. ~(x <= y) = y < x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le]);;

let INT_LE_TOTAL = prove_thm(`INT_LE_TOTAL`,
  "!x y. x <= y \/ y <= x",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_le; GSYM DE_MORGAN_THM; INT_LT_ANTISYM]);;

let INT_LET_TOTAL = prove_thm(`INT_LET_TOTAL`,
  "!x y. x <= y \/ y < x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
  BOOL_CASES_TAC "y < x" THEN REWRITE_TAC[]);;

let INT_LTE_TOTAL = prove_thm(`INT_LTE_TOTAL`,
  "!x y. x < y \/ y <= x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
  BOOL_CASES_TAC "x < y" THEN REWRITE_TAC[]);;

let INT_LE_REFL = prove_thm(`INT_LE_REFL`,
  "!x. x <= x",
  GEN_TAC THEN REWRITE_TAC[int_le; INT_LT_REFL]);;

let INT_LE_LT = prove_thm(`INT_LE_LT`,
  "!x y. x <= y = x < y \/ (x = y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL ["x:int"; "y:int"] INT_LT_TOTAL) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2
     ($THEN (MATCH_MP_TAC INT_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC INT_LT_REFL]);;

let INT_LT_LE = prove_thm(`INT_LT_LE`,
  "!x y. x < y = x <= y /\ ~(x = y)",
  let lemma = TAUT_CONV "~(a /\ ~a)" in
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT; RIGHT_AND_OVER_OR; lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LT_REFL]);;

let INT_LT_IMP_LE = prove_thm(`INT_LT_IMP_LE`,
  "!x y. x < y ==> x <= y",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[INT_LE_LT]);;

let INT_LTE_TRANS = prove_thm(`INT_LTE_TRANS`,
  "!x y z. x < y /\ y <= z ==> x < z",
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT; LEFT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN REWRITE_TAC[]);;

let INT_LET_TRANS = prove_thm(`INT_LET_TRANS`,
  "!x y z. x <= y /\ y < z ==> x < z",
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT; RIGHT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP INT_LT_TRANS)
    (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));;

let INT_LE_TRANS = prove_thm(`INT_LE_TRANS`,
  "!x y z. x <= y /\ y <= z ==> x <= z",
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [INT_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME "y < z")) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP INT_LT_IMP_LE o MATCH_MP INT_LET_TRANS));;

let INT_LE_ANTISYM = prove_thm(`INT_LE_ANTISYM`,
  "!x y. x <= y /\ y <= x = (x = y)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[int_le] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL ["x:int"; "y:int"] INT_LT_TOTAL) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_LE_REFL]]);;

let INT_LET_ANTISYM = prove_thm(`INT_LET_ANTISYM`,
  "!x y. ~(x < y /\ y <= x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
  BOOL_CASES_TAC "x < y" THEN REWRITE_TAC[]);;

let INT_LTE_ANTSYM = prove_thm(`INT_LTE_ANTSYM`,
  "!x y. ~(x <= y /\ y < x)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_ACCEPT_TAC INT_LET_ANTISYM);;

let INT_NEG_LT0 = prove_thm(`INT_NEG_LT0`,
  "!x. (--x) < &0 = &0 < x",
  GEN_TAC THEN SUBST1_TAC(SYM(SPECL ["--x"; "&0"; "x:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[INT_ADD_LINV; INT_ADD_LID]);;

let INT_NEG_GT0 = prove_thm(`INT_NEG_GT0`,
  "!x. &0 < (--x) = x < &0",
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LT0; INT_NEGNEG]);;

let INT_NEG_LE0 = prove_thm(`INT_NEG_LE0`,
  "!x. (--x) <= &0 = &0 <= x",
  GEN_TAC THEN REWRITE_TAC[int_le] THEN
  REWRITE_TAC[INT_NEG_GT0]);;

let INT_NEG_GE0 = prove_thm(`INT_NEG_GE0`,
  "!x. &0 <= (--x) = x <= &0",
  GEN_TAC THEN REWRITE_TAC[int_le] THEN
  REWRITE_TAC[INT_NEG_LT0]);;

let INT_LT_NEGTOTAL = prove_thm(`INT_LT_NEGTOTAL`,
  "!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)",
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL ["x:int"; "&0"] INT_LT_TOTAL) THEN
  ASM_REWRITE_TAC[SYM(REWRITE_RULE[INT_NEGNEG] (SPEC "--x" INT_NEG_LT0))]);;

let INT_LE_NEGTOTAL = prove_thm(`INT_LE_NEGTOTAL`,
  "!x. &0 <= x \/ &0 <= --x",
  GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC "x:int" INT_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[]);;

let INT_LE_MUL = prove_thm(`INT_LE_MUL`,
  "!x y. &0 <= x /\ &0 <= y ==> &0 <= (x * y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC ["&0 = x"; "&0 = y"] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC INT_LT_MUL THEN
  ASM_REWRITE_TAC[]);;

let INT_LE_SQUARE = prove_thm(`INT_LE_SQUARE`,
  "!x. &0 <= x * x",
  GEN_TAC THEN DISJ_CASES_TAC (SPEC "x:int" INT_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP INT_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM INT_NEG_RMUL; GSYM INT_NEG_LMUL; INT_NEGNEG]);;

let INT_LE_01 = prove_thm(`INT_LE_01`,
  "&0 <= &1",
  SUBST1_TAC(SYM(SPEC "&1" INT_MUL_LID)) THEN
  MATCH_ACCEPT_TAC INT_LE_SQUARE);;

let INT_LT_01 = prove_thm(`INT_LT_01`,
  "&0 < &1",
  REWRITE_TAC[INT_LT_LE; INT_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[INT_10]);;

let INT_LE_LADD = prove_thm(`INT_LE_LADD`,
  "!x y z. (x + y) <= (x + z) = y <= z",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_LADD);;

let INT_LE_RADD = prove_thm(`INT_LE_RADD`,
  "!x y z. (x + z) <= (y + z) = x <= y",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_le] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC INT_LT_RADD);;

let INT_LT_ADD2 = prove_thm(`INT_LT_ADD2`,
  "!w x y z. w < x /\ y < z ==> (w + y) < (x + z)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC INT_LT_TRANS THEN EXISTS_TAC "w + z" THEN
  ASM_REWRITE_TAC[INT_LT_LADD; INT_LT_RADD]);;

let INT_LE_ADD2 = prove_thm(`INT_LE_ADD2`,
  "!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC "w + z" THEN
  ASM_REWRITE_TAC[INT_LE_LADD; INT_LE_RADD]);;

let INT_LE_ADD = prove_thm(`INT_LE_ADD`,
  "!x y. &0 <= x /\ &0 <= y ==> &0 <= (x + y)",
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2) THEN
  REWRITE_TAC[INT_ADD_LID]);;

let INT_LT_ADD = prove_thm(`INT_LT_ADD`,
  "!x y. &0 < x /\ &0 < y ==> &0 < (x + y)",
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2) THEN
  REWRITE_TAC[INT_ADD_LID]);;

let INT_LT_ADDNEG = prove_thm(`INT_LT_ADDNEG`,
  "!x y z. y < (x + (--z)) = (y + z) < x",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["y:int"; "x + (--z)"; "z:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[GSYM INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_RID]);;

let INT_LT_ADDNEG2 = prove_thm(`INT_LT_ADDNEG2`,
  "!x y z. (x + (--y)) < z = x < (z + y)",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x + (-- y)"; "z:int"; "y:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[GSYM INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_RID]);;

let INT_LT_ADD1 = prove_thm(`INT_LT_ADD1`,
  "!x y. x <= y ==> x < (y + &1)",
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [POP_ASSUM(MP_TAC o MATCH_MP INT_LT_ADD2 o C CONJ INT_LT_01) THEN
    REWRITE_TAC[INT_ADD_RID];
    POP_ASSUM SUBST1_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [] [GSYM INT_ADD_RID] THEN
    REWRITE_TAC[INT_LT_LADD; INT_LT_01]]);;

let INT_SUB_ADD = prove_thm(`INT_SUB_ADD`,
  "!x y. (x - y) + y = x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; GSYM INT_ADD_ASSOC;
    INT_ADD_LINV; INT_ADD_RID]);;

let INT_SUB_ADD2 = prove_thm(`INT_SUB_ADD2`,
  "!x y. y + (x - y) = x",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_SUB_ADD);;

let INT_SUB_REFL = prove_thm(`INT_SUB_REFL`,
  "!x. x - x = &0",
  GEN_TAC THEN REWRITE_TAC[int_sub; INT_ADD_RINV]);;

let INT_SUB_0 = prove_thm(`INT_SUB_0`,
  "!x y. (x - y = &0) = (x = y)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM "y:int" o AP_TERM "$+") THEN
    REWRITE_TAC[INT_SUB_ADD; INT_ADD_LID];
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC INT_SUB_REFL]);;

let INT_LE_DOUBLE = prove_thm(`INT_LE_DOUBLE`,
  "!x. &0 <= x + x = &0 <= x",
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[INT_NOT_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_LT_ADD2 o W CONJ);
    DISCH_THEN(MP_TAC o MATCH_MP INT_LE_ADD2 o W CONJ)] THEN
  REWRITE_TAC[INT_ADD_LID]);;

let INT_LE_NEGL = prove_thm(`INT_LE_NEGL`,
  "!x. (--x <= x) = (&0 <= x)",
  GEN_TAC THEN SUBST1_TAC (SYM(SPECL ["x:int"; "--x"; "x:int"] INT_LE_LADD))
  THEN REWRITE_TAC[INT_ADD_RINV; INT_LE_DOUBLE]);;

let INT_LE_NEGR = prove_thm(`INT_LE_NEGR`,
  "!x. (x <= --x) = (x <= &0)",
  GEN_TAC THEN SUBST1_TAC(SYM(SPEC "x:int" INT_NEGNEG)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [INT_NEGNEG] THEN
  REWRITE_TAC[INT_LE_NEGL] THEN REWRITE_TAC[INT_NEG_GE0] THEN
  REWRITE_TAC[INT_NEGNEG]);;

let INT_NEG_EQ0 = prove_thm(`INT_NEG_EQ0`,
  "!x. (--x = &0) = (x = &0)",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM "$+ x");
    DISCH_THEN(MP_TAC o AP_TERM "$+ (--x)")] THEN
  REWRITE_TAC[INT_ADD_RINV; INT_ADD_LINV; INT_ADD_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let INT_NEG_0 = prove_thm(`INT_NEG_0`,
  "--(&0) = &0",
  REWRITE_TAC[INT_NEG_EQ0]);;

let INT_NEG_SUB = prove_thm(`INT_NEG_SUB`,
  "!x y. --(x - y) = y - x",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; INT_NEG_ADD; INT_NEGNEG] THEN
  MATCH_ACCEPT_TAC INT_ADD_SYM);;

let INT_SUB_LT = prove_thm(`INT_SUB_LT`,
  "!x y. &0 < x - y = y < x",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["&0"; "x - y"; "y:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[INT_SUB_ADD; INT_ADD_LID]);;

let INT_SUB_LE = prove_thm(`INT_SUB_LE`,
  "!x y. &0 <= (x - y) = y <= x",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["&0"; "x - y"; "y:int"] INT_LE_RADD)) THEN
  REWRITE_TAC[INT_SUB_ADD; INT_ADD_LID]);;

let INT_ADD_SUB = prove_thm(`INT_ADD_SUB`,
  "!x y. (x + y) - x = y",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  REWRITE_TAC[int_sub; GSYM INT_ADD_ASSOC; INT_ADD_RINV; INT_ADD_RID]);;

let INT_SUB_LDISTRIB = prove_thm(`INT_SUB_LDISTRIB`,
  "!x y z. x * (y - z) = (x * y) - (x * z)",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; INT_LDISTRIB; INT_NEG_RMUL]);;

let INT_SUB_RDISTRIB = prove_thm(`INT_SUB_RDISTRIB`,
  "!x y z. (x - y) * z = (x * z) - (y * z)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_SUB_LDISTRIB);;

let INT_NEG_EQ = prove_thm(`INT_NEG_EQ`,
  "!x y. (--x = y) = (x = --y)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM); DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_NEGNEG]);;

let INT_NEG_MINUS1 = prove_thm(`INT_NEG_MINUS1`,
  "!x. --x = (--(&1)) * x",
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NEG_LMUL] THEN
  REWRITE_TAC[INT_MUL_LID]);;

let INT_LT_IMP_NE = prove_thm(`INT_LT_IMP_NE`,
  "!x y. x < y ==> ~(x = y)",
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_LT_REFL]);;

let INT_LE_ADDR = prove_thm(`INT_LE_ADDR`,
  "!x y. x <= x + y = &0 <= y",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x:int"; "&0"; "y:int"] INT_LE_LADD)) THEN
  REWRITE_TAC[INT_ADD_RID]);;

let INT_LE_ADDL = prove_thm(`INT_LE_ADDL`,
  "!x y. y <= x + y = &0 <= x",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_LE_ADDR);;

let INT_LT_ADDR = prove_thm(`INT_LT_ADDR`,
  "!x y. x < x + y = &0 < y",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x:int"; "&0"; "y:int"] INT_LT_LADD)) THEN
  REWRITE_TAC[INT_ADD_RID]);;

let INT_LT_ADDL = prove_thm(`INT_LT_ADDL`,
  "!x y. y < x + y = &0 < x",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_LT_ADDR);;

let INT_ENTIRE = prove_thm(`INT_ENTIRE`,
  "!x y. (x * y = &0) = (x = &0) \/ (y = &0)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPEC "x:int" INT_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPEC "y:int" INT_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT_CONV "a ==> b ==> c = b /\ a ==> c"] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_LT_MUL) THEN
    REWRITE_TAC[GSYM INT_NEG_LMUL; GSYM INT_NEG_RMUL] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_NEG_0; INT_LT_REFL];
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO]]);;

let INT_EQ_LMUL = prove_thm(`INT_EQ_LMUL`,
  "!x y z. (x * y = x * z) = (x = &0) \/ (y = z)",
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [] [GSYM INT_SUB_0] THEN
  REWRITE_TAC[GSYM INT_SUB_LDISTRIB] THEN
  REWRITE_TAC[INT_ENTIRE; INT_SUB_0]);;

let INT_EQ_RMUL = prove_thm(`INT_EQ_RMUL`,
  "!x y z. (x * z = y * z) = (z = &0) \/ (x = y)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC INT_EQ_LMUL);;

%----------------------------------------------------------------------------%
% Prove homomorphisms for the inclusion map                                  %
%----------------------------------------------------------------------------%

let INT = prove_thm(`INT`,
  "!n. &(SUC n) = &n + &1",
  GEN_TAC THEN REWRITE_TAC[int_of_num] THEN
  REWRITE_TAC[INT_1]);;

let INT_POS = prove_thm(`INT_POS`,
  "!n. &0 <= &n",
  INDUCT_TAC THEN REWRITE_TAC[INT_LE_REFL] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC "&n" THEN ASM_REWRITE_TAC[INT] THEN
  REWRITE_TAC[INT_LE_ADDR; INT_LE_01]);;

let INT_LE = prove_thm(`INT_LE`,
  "!m n. &m <= &n = m num_le n",
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [INT; INT_LE_RADD; ZERO_LESS_EQ; LESS_EQ_MONO; INT_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LESS; LESS_0] THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC "&n" THEN
    ASM_REWRITE_TAC[ZERO_LESS_EQ; INT_LE_ADDR; INT_LE_01];
    DISCH_THEN(MP_TAC o C CONJ (SPEC "m:num" INT_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_LE_TRANS) THEN
    REWRITE_TAC[INT_NOT_LE; INT_LT_ADDR; INT_LT_01]]);;

let INT_LT = prove_thm(`INT_LT`,
  "!m n. &m < &n = m num_lt n",
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC ((REWRITE_RULE[] o AP_TERM "$~" o
    REWRITE_RULE[GSYM NOT_LESS; GSYM INT_NOT_LT]) (SPEC_ALL INT_LE)));;

let INT_INJ = prove_thm(`INT_INJ`,
  "!m n. (&m = &n) = (m = n)",
  let th = PROVE("(m = n) = m num_le n /\ n num_le m",
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL];
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[th; GSYM INT_LE_ANTISYM; INT_LE]);;

let INT_ADD = prove_thm(`INT_ADD`,
  "!m n. &m + &n = &(m num_add n)",
  INDUCT_TAC THEN REWRITE_TAC[INT; ADD; INT_ADD_LID] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));;

let INT_MUL = prove_thm(`INT_MUL`,
  "!m n. &m * &n = &(m num_mul n)",
  INDUCT_TAC THEN REWRITE_TAC[INT_MUL_LZERO; MULT_CLAUSES; INT;
    GSYM INT_ADD; INT_RDISTRIB] THEN
  FIRST_ASSUM(\th. REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[INT_MUL_LID]);;

%----------------------------------------------------------------------------%
% Now more theorems                                                          %
%----------------------------------------------------------------------------%

let INT_LT_NZ = prove_thm(`INT_LT_NZ`,
  "!n. ~(&n = &0) = (&0 < &n)",
  GEN_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC "&n = &0" THEN ASM_REWRITE_TAC[INT_LE_REFL; INT_POS]);;

let INT_NZ_IMP_LT = prove_thm(`INT_NZ_IMP_LT`,
  "!n. ~(n = 0) ==> &0 < &n",
  GEN_TAC THEN REWRITE_TAC[GSYM INT_INJ; INT_LT_NZ]);;

let INT_DOUBLE = prove_thm(`INT_DOUBLE`,
  "!x. x + x = &2 * x",
  GEN_TAC THEN REWRITE_TAC[num_CONV "2"; INT] THEN
  REWRITE_TAC[INT_RDISTRIB; INT_MUL_LID]);;

let INT_SUB_SUB = prove_thm(`INT_SUB_SUB`,
  "!x y. (x - y) - x = --y",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
  ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
    "(a + b) + c = (c + a) + b"] THEN
  REWRITE_TAC[INT_ADD_LINV; INT_ADD_LID]);;

let INT_LT_ADD_SUB = prove_thm(`INT_LT_ADD_SUB`,
  "!x y z. (x + y) < z = x < (z - y)",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x:int"; "z - y"; "y:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[INT_SUB_ADD]);;

let INT_LT_SUB_RADD = prove_thm(`INT_LT_SUB_RADD`,
  "!x y z. (x - y) < z = x < z + y",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x - y"; "z:int"; "y:int"] INT_LT_RADD)) THEN
  REWRITE_TAC[INT_SUB_ADD]);;

let INT_LT_SUB_LADD = prove_thm(`INT_LT_SUB_LADD`,
  "!x y z. x < (y - z) = (x + z) < y",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL ["x + z"; "y:int"; "--z"] INT_LT_RADD)) THEN
  REWRITE_TAC[int_sub; GSYM INT_ADD_ASSOC; INT_ADD_RINV; INT_ADD_RID]);;

let INT_LE_SUB_LADD = prove_thm(`INT_LE_SUB_LADD`,
  "!x y z. x <= (y - z) = (x + z) <= y",
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT; INT_LT_SUB_RADD]);;

let INT_LE_SUB_RADD = prove_thm(`INT_LE_SUB_RADD`,
  "!x y z. (x - y) <= z = x <= z + y",
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT; INT_LT_SUB_LADD]);;

let INT_LT_NEG = prove_thm(`INT_LT_NEG`,
  "!x y. --x < --y = y < x",
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL["--x"; "--y"; "x + y"] INT_LT_RADD)) THEN
  REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_RINV; INT_ADD_LID]);;

let INT_LE_NEG = prove_thm(`INT_LE_NEG`,
  "!x y. --x <= --y = y <= x",
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN
  REWRITE_TAC[INT_LT_NEG]);;

let INT_ADD2_SUB2 = prove_thm(`INT_ADD2_SUB2`,
  "!a b c d. (a + b) - (c + d) = (a - c) + (b - d)",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; INT_NEG_ADD] THEN
  CONV_TAC(AC_CONV(INT_ADD_ASSOC,INT_ADD_SYM)));;

let INT_SUB_LZERO = prove_thm(`INT_SUB_LZERO`,
  "!x. &0 - x = --x",
  GEN_TAC THEN REWRITE_TAC[int_sub; INT_ADD_LID]);;

let INT_SUB_RZERO = prove_thm(`INT_SUB_RZERO`,
  "!x. x - &0 = x",
  GEN_TAC THEN REWRITE_TAC[int_sub; INT_NEG_0; INT_ADD_RID]);;

let INT_LET_ADD2 = prove_thm(`INT_LET_ADD2`,
  "!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)",
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC INT_LTE_TRANS THEN
  EXISTS_TAC "w + z" THEN
  ASM_REWRITE_TAC[INT_LE_RADD; INT_LT_LADD]);;

let INT_LTE_ADD2 = prove_thm(`INT_LTE_ADD2`,
  "!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC INT_LET_ADD2);;

let INT_LET_ADD = prove_thm(`INT_LET_ADD`,
  "!x y. &0 <= x /\ &0 < y ==> &0 < (x + y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC "&0" INT_ADD_LID)) THEN
  MATCH_MP_TAC INT_LET_ADD2 THEN
  ASM_REWRITE_TAC[]);;

let INT_LTE_ADD = prove_thm(`INT_LTE_ADD`,
  "!x y. &0 < x /\ &0 <= y ==> &0 < (x + y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC "&0" INT_ADD_LID)) THEN
  MATCH_MP_TAC INT_LTE_ADD2 THEN
  ASM_REWRITE_TAC[]);;

let INT_LT_MUL2 = prove_thm(`INT_LT_MUL2`,
  "!x1 x2 y1 y2. &0 <= x1 /\ &0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_SUB_LT] THEN
  REWRITE_TAC[INT_SUB_RZERO] THEN
  SUBGOAL_THEN "!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))"
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
    ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
      "(a + b) + (c + d) = (b + c) + (a + d)"] THEN
    REWRITE_TAC[INT_ADD_LINV; INT_ADD_LID];
    DISCH_THEN(\th. ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM INT_SUB_LDISTRIB; GSYM INT_SUB_RDISTRIB] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC INT_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC "x1:int" THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM INT_SUB_LT] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

let INT_SUB_LNEG = prove_thm(`INT_SUB_LNEG`,
  "!x y. (--x) - y = --(x + y)",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; INT_NEG_ADD]);;

let INT_SUB_RNEG = prove_thm(`INT_SUB_RNEG`,
  "!x y. x - (--y) = x + y",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub; INT_NEGNEG]);;

let INT_SUB_NEG2 = prove_thm(`INT_SUB_NEG2`,
  "!x y. (--x) - (--y) = y - x",
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_SUB_LNEG] THEN
  REWRITE_TAC[int_sub; INT_NEG_ADD; INT_NEGNEG] THEN
  MATCH_ACCEPT_TAC INT_ADD_SYM);;

let INT_SUB_TRIANGLE = prove_thm(`INT_SUB_TRIANGLE`,
  "!a b c. (a - b) + (b - c) = a - c",
  REPEAT GEN_TAC THEN REWRITE_TAC[int_sub] THEN
  ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
    "(a + b) + (c + d) = (b + c) + (a + d)"] THEN
  REWRITE_TAC[INT_ADD_LINV; INT_ADD_LID]);;

let INT_EQ_SUB_LADD = prove_thm(`INT_EQ_SUB_LADD`,
  "!x y z. (x = y - z) = (x + z = y)",
  REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL INT_EQ_RADD)
   ["x:int"; "y - z"; "z:int"] THEN REWRITE_TAC[INT_SUB_ADD]);;

let INT_EQ_SUB_RADD = prove_thm(`INT_EQ_SUB_RADD`,
  "!x y z. (x - y = z) = (x = z + y)",
  REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC INT_EQ_SUB_LADD);;

let INT_SUB_SUB2 = prove_thm(`INT_SUB_SUB2`,
  "!x y. x - (x - y) = y",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEGNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[INT_NEG_SUB; INT_SUB_SUB]);;

let INT_ADD_SUB2 = prove_thm(`INT_ADD_SUB2`,
  "!x y. x - (x + y) = --y",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_NEG_SUB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[INT_ADD_SUB]);;

let INT_EQ_LMUL2 = prove_thm(`INT_EQ_LMUL2`,
  "!x y z. ~(x = &0) ==> ((y = z) = (x * y = x * z))",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL ["x:int"; "y:int"; "z:int"] INT_EQ_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);;

let INT_EQ_IMP_LE = prove_thm(`INT_EQ_IMP_LE`,
  "!x y. (x = y) ==> x <= y",
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC INT_LE_REFL);;

let INT_POS_NZ = prove_thm(`INT_POS_NZ`,
  "!x. &0 < x ==> ~(x = &0)",
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP INT_LT_IMP_NE) THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);;

let INT_EQ_RMUL_IMP = prove_thm(`INT_EQ_RMUL_IMP`,
  "!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[INT_EQ_RMUL]);;

let INT_EQ_LMUL_IMP = prove_thm(`INT_EQ_LMUL_IMP`,
  "!x y z. ~(x = &0) /\ (x * y = x * z) ==> (y = z)",
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN MATCH_ACCEPT_TAC INT_EQ_RMUL_IMP);;

let INT_DIFFSQ = prove_thm(`INT_DIFFSQ`,
  "!x y. (x + y) * (x - y) = (x * x) - (y * y)",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INT_LDISTRIB; INT_RDISTRIB; int_sub; GSYM INT_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(INT_ADD_ASSOC,INT_ADD_SYM)
    "a + b + c + d = (b + c) + (a + d)"] THEN
  REWRITE_TAC[INT_ADD_LID_UNIQ; GSYM INT_NEG_RMUL] THEN
  REWRITE_TAC[INT_LNEG_UNIQ] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC INT_MUL_SYM);;

let INT_POSSQ = prove_thm(`INT_POASQ`,
  "!x. &0 < (x * x) = ~(x = &0)",
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC "x:int" INT_LE_SQUARE)) THEN
    REWRITE_TAC[INT_LE_ANTISYM; INT_ENTIRE];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_MUL_LZERO; INT_LE_REFL]]);;

let INT_SUMSQ = prove_thm(`INT_SUMSQ`,
  "!x y. ((x * x) + (y * y) = &0) = (x = &0) /\ (y = &0)",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC INT_POS_NZ THENL
     [MATCH_MP_TAC INT_LTE_ADD; MATCH_MP_TAC INT_LET_ADD] THEN
    ASM_REWRITE_TAC[INT_POSSQ; INT_LE_SQUARE];
    DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID]]);;

let INT_EQ_NEG = prove_thm(`INT_EQ_NEG`,
  "!x y. (--x = --y) = (x = y)",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM; INT_LE_NEG] THEN
  MATCH_ACCEPT_TAC CONJ_SYM);;

%----------------------------------------------------------------------------%
% Some nasty hacking round to show that the positive integers are a copy     %
% of the natural numbers.                                                    %
%----------------------------------------------------------------------------%

let INT_DECOMPOSE = prove_thm(`INT_DECOMPOSE`,
  "!i. ?m n. i = mk_int($tint_eq(m,n))",
  GEN_TAC THEN
  MP_TAC(SPEC "dest_int i" (CONJUNCT2 int_tybij)) THEN
  REWRITE_TAC[CONJUNCT1 int_tybij] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "x:num#num" MP_TAC) THEN
  DISCH_THEN(MP_TAC o AP_TERM "mk_int") THEN
  REWRITE_TAC[CONJUNCT1 int_tybij] THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC ["FST(x:num#num)"; "SND(x:num#num)"] THEN
  REWRITE_TAC[]);;

let DEST_MK_EQCLASS = prove_thm(`DEST_MK_EQCLASS`,
  "!v. dest_int (mk_int ($tint_eq v)) = $tint_eq v",
  GEN_TAC THEN REWRITE_TAC[GSYM int_tybij] THEN
  BETA_TAC THEN EXISTS_TAC "v:num#num" THEN REFL_TAC);;

let REP_EQCLASS = prove_thm(`REP_EQCLASS`,
  "!v. $@($tint_eq v) tint_eq v",
  GEN_TAC THEN ONCE_REWRITE_TAC[TINT_EQ_SYM] THEN
  MATCH_MP_TAC SELECT_AX THEN
  EXISTS_TAC "v:num#num" THEN
  MATCH_ACCEPT_TAC TINT_EQ_REFL);;

map (load_definition `-`) [`int_0`; `int_1`; `int_add`; `int_lt`];;

let NUM_LEMMA = prove_thm(`NUM_LEMMA`,
  "!i. &0 <= i ==> ?n. i = mk_int($tint_eq (n,0))",
  GEN_TAC THEN
  X_CHOOSE_THEN "m:num" (X_CHOOSE_THEN "n:num" SUBST1_TAC)
    (SPEC "i:int" INT_DECOMPOSE) THEN
  REWRITE_TAC[GSYM INT_0; int_lt; int_0; int_le; tint_lt] THEN
  REWRITE_TAC[DEST_MK_EQCLASS] THEN
  DISCH_TAC THEN EXISTS_TAC "m num_sub n" THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM TINT_EQ_EQUIV; tint_eq] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUB_ADD THEN POP_ASSUM MP_TAC THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[GSYM NOT_LESS] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN "$@($tint_eq(m,n)) tint_eq (m,n) /\
                $@($tint_eq tint_0) tint_eq (1,1)"
    (\th. REWRITE_TAC[MATCH_MP TINT_LT_WELLDEF th])
  THENL [REWRITE_TAC[REP_EQCLASS; tint_0]; ALL_TAC] THEN
  REWRITE_TAC[tint_lt] THEN
  GEN_REWRITE_TAC RAND_CONV [] [ADD_SYM] THEN
  ASM_REWRITE_TAC[LESS_MONO_ADD_EQ]);;

let NUM_DECOMPOSE = prove_thm(`NUM_DECOMPOSE`,
  "!n. &n = mk_int($tint_eq (n,0))",
  INDUCT_TAC THEN REWRITE_TAC[int_of_num; int_0; tint_0] THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV; tint_eq; ADD_CLAUSES];
    ASM_REWRITE_TAC[int_1; int_add; tint_1] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM TINT_EQ_EQUIV; DEST_MK_EQCLASS] THEN
    REWRITE_TAC[TINT_EQ_EQUIV] THEN
    SUBGOAL_THEN "$@($tint_eq(n,0)) tint_eq (n,0) /\
                  $@($tint_eq(1 num_add 1,1)) tint_eq (1 num_add 1,1)"
      (\th. REWRITE_TAC[REWRITE_RULE[TINT_EQ_EQUIV]
              (MATCH_MP TINT_ADD_WELLDEF th)])
    THENL [REWRITE_TAC[REP_EQCLASS; tint_0]; ALL_TAC] THEN
    REWRITE_TAC[tint_add; GSYM TINT_EQ_EQUIV; tint_eq] THEN
    REWRITE_TAC[num_CONV "1"; ADD_CLAUSES]]);;

let NUM_POSINT = prove_thm(`NUM_POSINT`,
  "!i. &0 <= i ==> ?!n. i = &n",
  GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [] [GSYM INT_INJ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    REFL_TAC] THEN
  POP_ASSUM(\th. X_CHOOSE_THEN "n:num" SUBST1_TAC (MATCH_MP NUM_LEMMA th)) THEN
  EXISTS_TAC "n:num" THEN REWRITE_TAC[NUM_DECOMPOSE]);;

%----------------------------------------------------------------------------%
% Theorems about mapping both ways between :num and :int                     %
%----------------------------------------------------------------------------%

let Num = new_definition(`Num`,
  "Num i = @n. i = &n");;

let NUM_OF_INT = prove_thm(`NUM_OF_INT`,
  "!n. Num(&n) = n",
  GEN_TAC THEN REWRITE_TAC[Num; INT_INJ] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  REWRITE_TAC[SELECT_REFL]);;

let INT_OF_NUM = prove_thm(`INT_OF_NUM`,
  "!i. (&(Num i) = i) = &0 <= i",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC INT_POS;
    DISCH_THEN(ASSUME_TAC o EXISTENCE o MATCH_MP NUM_POSINT) THEN
    REWRITE_TAC[Num] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPEC "\n. i = &n" SELECT_AX) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    POP_ASSUM ACCEPT_TAC]);;

close_theory();;
