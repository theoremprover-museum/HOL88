%============================================================================%
% Theory of limits, continuity and differentiation of real->real functions   %
%============================================================================%

can unlink `LIM.th`;;

new_theory `LIM`;;

new_parent `SEQ`;;

loadt `useful`;;

let real_interface_map =
[               `--`,`real_neg`;
 `num_add`,`+`;  `+`,`real_add`;
 `num_mul`,`*`;  `*`,`real_mul`;
 `num_sub`,`-`;  `-`,`real_sub`;
 `num_lt`,`<` ;  `<`,`real_lt`;
 `num_le`,`<=`; `<=`,`real_le`;
 `num_gt`,`>` ;  `>`,`real_gt`;
 `num_ge`,`>=`; `>=`,`real_ge`;
               `inv`,`real_inv`;
                 `&`,`real_of_num`];;

do map autoload_definitions [`REAL`; `TOPOLOGY`; `NETS`; `SEQ`];;

do map autoload_theorems [`REAL`; `TOPOLOGY`; `NETS`; `SEQ`];;

hide_constant `S`;;

%----------------------------------------------------------------------------%
% Specialize nets theorems to the pointwise limit of real->real functions    %
%----------------------------------------------------------------------------%

let tends_real_real = new_infix_definition(`tends_real_real`,
  "($tends_real_real f l)(x0) =
        (f tends l)(mtop(mr1),tendsto(mr1,x0))");;

set_interface_map ((`-->`,`tends_real_real`).real_interface_map);;

let LIM = prove_thm(`LIM`,
  "!f y0 x0. (f --> y0)(x0) =
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tends_real_real; MATCH_MP LIM_TENDS2 (SPEC "x0:real" MR1_LIMPT)]
  THEN REWRITE_TAC[MR1_DEF] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [ABS_SUB] THEN
  REFL_TAC);;

let LIM_CONST = prove_thm(`LIM_CONST`,
  "!k x. ((\x. k) --> k)(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real; MTOP_TENDS] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[METRIC_SAME] THEN
  REWRITE_TAC[tendsto; REAL_LE_REFL] THEN
  MP_TAC(REWRITE_RULE[MTOP_LIMPT] (SPEC "x:real" MR1_LIMPT)) THEN
  DISCH_THEN(MP_TAC o SPEC "e:real") THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN "z:real" (ASSUME_TAC o CONJUNCT1)) THEN
  EXISTS_TAC "z:real" THEN REWRITE_TAC[MR1_DEF; GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[]);;

let LIM_ADD = prove_thm(`LIM_ADD`,
  "!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) + g(x)) --> (l + m))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_ADD THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_MUL = prove_thm(`LIM_MUL`,
  "!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) * g(x)) --> (l * m))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_MUL THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_NEG = prove_thm(`LIM_NEG`,
  "!f l. (f --> l)(x) = ((\x. --(f(x))) --> --l)(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_INV = prove_thm(`LIM_INV`,
  "!f l. (f --> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) --> inv l)(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_INV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_SUB = prove_thm(`LIM_SUB`,
  "!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) - g(x)) --> (l - m))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_SUB THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_DIV = prove_thm(`LIM_DIV`,
  "!f g l m. (f --> l)(x) /\ (g --> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) --> (l / m))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_NULL = prove_thm(`LIM_NULL`,
  "!f l x. (f --> l)(x) = ((\x. f(x) - l) --> &0)(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_ACCEPT_TAC NET_NULL);;

%----------------------------------------------------------------------------%
% One extra theorem is handy                                                 %
%----------------------------------------------------------------------------%

let LIM_X = prove_thm(`LIM_X`,
  "!x0. ((\x. x) --> x0)(x0)",
  GEN_TAC THEN REWRITE_TAC[LIM] THEN X_GEN_TAC "e:real" THEN
  DISCH_TAC THEN EXISTS_TAC "e:real" THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Uniqueness of limit                                                        %
%----------------------------------------------------------------------------%

let LIM_UNIQ = prove_thm(`LIM_UNIQ`,
  "!f l m x. (f --> l)(x) /\ (f --> m)(x) ==> (l = m)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_TENDSTO);;

%----------------------------------------------------------------------------%
% Show that limits are equal when functions are equal except at limit point  %
%----------------------------------------------------------------------------%

let LIM_EQUAL = prove_thm(`LIM_EQUAL`,
  "!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f --> l)(x0) = (g --> l)(x0))",
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV "(a ==> b = a ==> c) = a ==> (b = c)"] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ASM_REWRITE_TAC[ABS_NZ]);;

%----------------------------------------------------------------------------%
% A more general theorem about rearranging the body of a limit               %
%----------------------------------------------------------------------------%

let LIM_TRANSFORM = prove_thm(`LIM_TRANSFORM`,
  "!f g x0 l. ((\x. f(x) - g(x)) --> &0)(x0) /\ (g --> l)(x0)
        ==> (f --> l)(x0)",
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN($THEN (X_GEN_TAC "e:real" THEN DISCH_TAC) o MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC "e / &2")) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN "c:real" STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL ["c:real"; "d:real"] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN "b:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "b:real" THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC "x:real" THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC "(e / &2) + (e / &2)" THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC "abs(f(x:real) - g(x)) + abs(g(x) - l)" THEN
  SUBST1_TAC(SYM(SPECL
    ["(f:real->real) x"; "(g:real->real) x"; "l:real"] REAL_SUB_TRIANGLE)) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_ADD2 THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC "b:real" THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Define differentiation and continuity                                      %
%----------------------------------------------------------------------------%

let diffl = new_infix_definition(`diffl`,
  "($diffl f l)(x) = ((\h. (f(x+h) - f(x)) / h) --> l)(&0)");;

let contl = new_infix_definition(`contl`,
  "$contl f x = ((\h. f(x + h)) --> f(x))(&0)");;

let differentiable = new_infix_definition(`differentiable`,
  "$differentiable f x = ?l. (f diffl l)(x)");;

%----------------------------------------------------------------------------%
% Derivative is unique                                                       %
%----------------------------------------------------------------------------%

let DIFF_UNIQ = prove_thm(`DIFF_UNIQ`,
  "!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)",
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  MATCH_ACCEPT_TAC LIM_UNIQ);;

%----------------------------------------------------------------------------%
% Differentiability implies continuity                                       %
%----------------------------------------------------------------------------%

let DIFF_CONT = prove_thm(`DIFF_CONT`,
  "!f l x. ($diffl f l)(x) ==> contl f x",
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl; contl] THEN DISCH_TAC THEN
  REWRITE_TAC[tends_real_real] THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[GSYM tends_real_real] THEN BETA_TAC THEN
  SUBGOAL_THEN "((\h. f(x + h) - f(x)) --> &0)(&0) =
                ((\h. ((f(x + h) - f(x)) / h) * h) --> &0)(&0)" SUBST1_TAC
  THENL
   [MATCH_MP_TAC LIM_EQUAL THEN
    X_GEN_TAC "z:real" THEN BETA_TAC THEN
    DISCH_THEN(\th. REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]); ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o RAND_CONV)
    [] [SYM(BETA_CONV "(\h:real. h) h")] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV "h:real" "(f(x + h) - f(x)) / h"]) THEN
  SUBST1_TAC(SYM(SPEC "l:real" REAL_MUL_RZERO)) THEN
  MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIM] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  X_GEN_TAC "e:real" THEN DISCH_TAC THEN EXISTS_TAC "e:real" THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Alternative definition of continuity                                       %
%----------------------------------------------------------------------------%

let CONTL_LIM = prove_thm(`CONTL_LIM`,
  "!f x. f contl x = (f --> f(x))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[contl; LIM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV "(a ==> b = a ==> c) = a ==> (b = c)"] THEN
  DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC "k:real" THENL
   [DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[REAL_SUB_ADD2];
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB]]);;

%----------------------------------------------------------------------------%
% Simple combining theorems for continuity                                   %
%----------------------------------------------------------------------------%

let CONT_CONST = prove_thm(`CONT_CONST`,
  "!x. contl (\x. k) x",
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN
  MATCH_ACCEPT_TAC LIM_CONST);;

let CONT_ADD = prove_thm(`CONT_ADD`,
  "!x. contl f x /\ contl g x ==> contl (\x. f(x) + g(x)) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_ADD);;

let CONT_MUL = prove_thm(`CONT_MUL`,
  "!x. contl f x /\ contl g x ==> contl (\x. f(x) * g(x)) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_MUL);;

let CONT_NEG = prove_thm(`CONT_NEG`,
  "!x. contl f x ==> contl (\x. --(f(x))) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM LIM_NEG]);;

let CONT_INV = prove_thm(`CONT_INV`,
  "!x. contl f x /\ ~(f x = &0) ==> contl (\x. inv(f(x))) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_INV);;

let CONT_SUB = prove_thm(`CONT_SUB`,
  "!x. contl f x /\ contl g x ==> contl (\x. f(x) - g(x)) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_SUB);;

let CONT_DIV = prove_thm(`CONT_DIV`,
  "!x. contl f x /\ contl g x /\ ~(g x = &0) ==>
        contl (\x. f(x) / g(x)) x",
  GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_DIV);;

%----------------------------------------------------------------------------%
% Intermediate Value Theorem (we prove contrapositive by bisection)          %
%----------------------------------------------------------------------------%

let IVT = prove_thm(`IVT`,
  "!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    "\(u,v). a <= u /\ u <= v /\ v <= b ==> ~(f(u) <= y /\ y <= f(v))" THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (\t. REWRITE_TAC[t]) o funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL ["a:real"; "b:real"]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC ["u:real"; "v:real"; "w:real"] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM; NOT_IMP] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY ASM_CASES_TAC ["u <= v"; "v <= w"] THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(SPECL ["y:real"; "(f:real->real) v"] REAL_LE_TOTAL) THEN
    ASM_REWRITE_TAC[] THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC "w:real"; EXISTS_TAC "u:real"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC "x:real" THEN ASM_CASES_TAC "a <= x /\ x <= b" THENL
   [ALL_TAC;
    EXISTS_TAC "&1" THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC ["u:real"; "v:real"] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC "~(a <= x /\ x <= b)" THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC "u:real"; EXISTS_TAC "v:real"] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC "!x. ~(a <= x /\ x <= b /\ (f(x) = (y:real)))" THEN
  DISCH_THEN(MP_TAC o SPEC "x:real") THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC "!x. a <= x /\ x <= b ==> f contl x" THEN
  DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[contl; LIM] THEN
  DISCH_THEN(MP_TAC o SPEC "abs(y - f(x:real))") THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [] [GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0; REAL_SUB_RZERO] THEN BETA_TAC THEN
  ASSUM_LIST(\thl. REWRITE_TAC(map GSYM thl)) THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC ["u:real"; "v:real"] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL ["(f:real->real) x"; "y:real"] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THENL
   [DISCH_THEN(MP_TAC o SPEC "v - x") THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[abs; REAL_SUB_LE; REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC "f(v:real) < y" THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE];
      ASM_REWRITE_TAC[abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC "v - u" THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_LADD; REAL_LE_NEG; REAL_LE_RADD];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT; abs; REAL_SUB_LE] THEN
      SUBGOAL_THEN "f(x:real) <= y" ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN "f(x:real) <= f(v)" ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "y:real"; ALL_TAC] THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_RADD]];
    DISCH_THEN(MP_TAC o SPEC "u - x") THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[abs; REAL_SUB_LE; REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC "y < f(x:real)" THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE];
      ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC "v - u" THEN
      ASM_REWRITE_TAC[real_sub; REAL_LE_LADD; REAL_LE_NEG; REAL_LE_RADD];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT; abs; REAL_SUB_LE] THEN
      SUBGOAL_THEN "f(u:real) < f(x)" ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC "y:real" THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      ASM_REWRITE_TAC[REAL_NOT_LT; REAL_LE_NEG; real_sub; REAL_LE_RADD]]]);;

%----------------------------------------------------------------------------%
% Intermediate value theorem where value at the left end is bigger           %
%----------------------------------------------------------------------------%

let IVT2 = prove_thm(`IVT2`,
  "!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> contl f x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL ["\x:real. --(f x)"; "a:real"; "b:real"; "--y"] IVT) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG; REAL_NEG_EQ; REAL_NEGNEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONT_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Prove the simple combining theorems for differentiation                    %
%----------------------------------------------------------------------------%

let DIFF_CONST = prove_thm(`DIFF_CONST`,
  "!k x. ((\x. k) diffl &0)(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
  MATCH_ACCEPT_TAC LIM_CONST);;

let DIFF_ADD = prove_thm(`DIFF_ADD`,
  "!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD2_SUB2] THEN
  REWRITE_TAC[real_div; REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV "h:real" "(f(x + h) - f(x)) / h"]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV "h:real" "(g(x + h) - g(x)) / h"]) THEN
  MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]);;

let DIFF_MUL = prove_thm(`DIFF_MUL`,
  "!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN
    "!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))"
  (\th. ONCE_REWRITE_TAC[GEN_ALL th]) THENL
   [REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      "(a + b) + (c + d) = (b + c) + (a + d)"] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN SUBGOAL_THEN
    "!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)"
    (\th. ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN BINOP_TAC THEN
    CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)); ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [] [REAL_ADD_SYM] THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV "h:real")
    ["((g(x + h) - g(x)) / h) * f(x + h)";
     "((f(x + h) - f(x)) / h) * g(x)"])) THEN
  MATCH_MP_TAC LIM_ADD THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV "h:real")
    ["(g(x + h) - g(x)) / h"; "f(x + h):real";
     "(f(x + h) - f(x)) / h"; "g(x:real):real"])) THEN
  CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[GSYM contl] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC "l:real" THEN
  ASM_REWRITE_TAC[diffl]);;

let DIFF_CMUL = prove_thm(`DIFF_CMUL`,
  "!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL ["c:real"; "x:real"] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC(TAUT_CONV("(a = b) ==> a ==> b")) THEN AP_THM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [] [REAL_MUL_SYM] THEN
  REWRITE_TAC[]);;

let DIFF_NEG = prove_thm(`DIFF_NEG`,
  "!f l x. (f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC DIFF_CMUL);;

let DIFF_SUB = prove_thm(`DIFF_SUB`,
  "!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD o (uncurry CONJ) o
              (I # MATCH_MP DIFF_NEG) o CONJ_PAIR) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]);;

%----------------------------------------------------------------------------%
% Now the chain rule                                                         %
%----------------------------------------------------------------------------%

let LIM_NULL_MUL = prove_thm(`LIM_NULL_MUL`,
  "!x x0 y. bounded(mr1,tendsto(mr1,x0)) x /\ (y --> &0)(x0)
        ==> ((\u. x(u) * y(u)) --> &0)(x0)",
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_NULL_MUL THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);;

let LIM_BOUNDED = prove_thm(`LIM_BOUNDED`,
  "bounded(mr1,tendsto(mr1,x0)) f =
     ?k d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==> abs(f x) < k",
   REWRITE_TAC[MR1_BOUNDED; tendsto; REAL_LE_REFL; MR1_DEF] THEN EQ_TAC THENL
    [DISCH_THEN(X_CHOOSE_THEN "k:real" (X_CHOOSE_THEN "z:real" MP_TAC)) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN
     MAP_EVERY EXISTS_TAC ["k:real"; "abs(z - x0)"] THEN
     ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
     DISCH_THEN(X_CHOOSE_THEN "k:real" (X_CHOOSE_THEN "d:real" MP_TAC)) THEN
     DISCH_THEN STRIP_ASSUME_TAC THEN
     MAP_EVERY EXISTS_TAC ["k:real"; "x0 + (d / &2)"] THEN
     REWRITE_TAC[REAL_ADD_SUB] THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC "d / &2" THEN
       ASM_REWRITE_TAC[REAL_LT_HALF1; ABS_LE];
       GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
       EXISTS_TAC "abs(d / &2)" THEN ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN "abs(d / &2) = d / &2" SUBST1_TAC THENL
        [REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
         ASM_REWRITE_TAC[REAL_LT_HALF1]; ASM_REWRITE_TAC[REAL_LT_HALF2]]]]);;

let CHAIN_LEMMA1 = prove_thm(`CHAIN_LEMMA1`,
  "!f g x h. (f(g(x + h)) - f(g(x))) / h =
    ((f(g(x + h)) - f(g(x))) / (g(x + h) - g(x))) * ((g(x + h) - g(x)) / h)",
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  ASM_CASES_TAC "g(x + h):real = g(x)" THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO];
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      "(a * b) * (c * d) = (b * c) * (a * d)"] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
    POP_ASSUM(\th. REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID]]);;

let CHAIN_LEMMA2 = prove_thm(`CHAIN_LEMMA2`,
  "!x y d. abs(x - y) < d ==> abs(x) < abs(y) + d",
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  SUBST1_TAC(SYM(SPECL ["x:real"; "y:real"] REAL_SUB_ADD)) THEN
  EXISTS_TAC "abs(x - y) + abs(y)" THEN REWRITE_TAC[ABS_TRIANGLE] THEN
  GEN_REWRITE_TAC RAND_CONV [] [REAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[REAL_LT_RADD]);;

let DIFF_CHAIN = prove_thm(`DIFF_CHAIN`,
  "!f g x . (f diffl l)(g x) /\ (g diffl m)(x) ==>
                ((\x. f(g x)) diffl (l * m))(x)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIFF_CONT o CONJUNCT2) THEN ASM_CASES_TAC
    "?k. &0 < k /\
         !h. &0 < abs(h) /\ abs(h) < k ==> ~(g(x + h):real = g(x))" THENL
   [REWRITE_TAC[diffl] THEN
    BETA_TAC THEN ONCE_REWRITE_TAC[CHAIN_LEMMA1] THEN
    (CONV_TAC o EXACT_CONV o map (X_BETA_CONV "h:real"))
      ["(f(g(x + h)) - f(g(x))) / (g(x + h) - g(x))";
       "(g(x + h) - g(x)) / h"] THEN
    MATCH_MP_TAC LIM_MUL THEN ASM_REWRITE_TAC[GSYM diffl] THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_exists o concl) THEN
    DISCH_THEN(X_CHOOSE_THEN "k:real" STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[LIM] THEN X_GEN_TAC "e:real" THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[diffl] THEN
    REWRITE_TAC[LIM; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC "e:real") THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC "d:real") THEN
    UNDISCH_TAC "g contl x" THEN REWRITE_TAC[contl] THEN
    REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC "d:real") THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN "c:real" MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL ["c:real"; "k:real"] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN "b:real" STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN($THEN (EXISTS_TAC "b:real") o MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    DISCH_THEN($THEN (X_GEN_TAC "z:real" THEN DISCH_TAC) o MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC "z:real") THEN ASM_REWRITE_TAC[] THEN
    W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC "b:real" THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC "g(x + z) - g(x)" o CONJUNCT2) THEN
    REWRITE_TAC[ASSUME "abs(g(x + z) - g(x)) < d"] THEN BETA_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_SUB_ADD] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
    REWRITE_TAC[REAL_SUB_0] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC "b:real" THEN ASM_REWRITE_TAC[];

    FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
    DISCH_THEN(MP_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
    REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN
    SUBGOAL_THEN "m = &0" SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[TAUT_CONV "a = ~(~a)"] THEN
      PURE_REWRITE_TAC[ABS_NZ] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[diffl] o CONJUNCT2) THEN
      REWRITE_TAC[LIM] THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC "abs(m)") THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC "d:real") THEN
      FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
      DISCH_THEN(MP_TAC o SPEC "d:real") THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN "h:real" STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o SPEC "h:real" o CONJUNCT2) THEN
      REWRITE_TAC[ASSUME "&0 < abs(h)"] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
      REWRITE_TAC[REAL_SUB_LZERO; ABS_NEG; REAL_LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[diffl] THEN
    BETA_TAC THEN ONCE_REWRITE_TAC[CHAIN_LEMMA1] THEN
    (CONV_TAC o EXACT_CONV o map (X_BETA_CONV "h:real"))
      ["(f(g(x + h)) - f(g(x))) / (g(x + h) - g(x))";
       "(g(x + h) - g(x)) / h"] THEN
    MATCH_MP_TAC LIM_NULL_MUL THEN ASM_REWRITE_TAC[GSYM diffl] THEN
    REWRITE_TAC[LIM_BOUNDED] THEN EXISTS_TAC "abs(l) + &1" THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[diffl] THEN
    REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC "&1") THEN
    REWRITE_TAC[REAL_LT_01] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC "e:real") THEN
    UNDISCH_TAC "g contl x" THEN REWRITE_TAC[contl] THEN
    REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC "e:real") THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN "d:real" ($THEN (EXISTS_TAC "d:real") o MP_TAC))
    THEN REWRITE_TAC[MR1_DEF; REAL_SUB_RZERO] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN($THEN (X_GEN_TAC "z:real" THEN DISCH_TAC) o MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC "z:real") THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC "g(x + z) - g(x)" o CONJUNCT2)
    THEN REWRITE_TAC[ASSUME "abs(g(x + z) - g(x)) < e"] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_SUB_ADD] THEN
    REWRITE_TAC[GSYM ABS_NZ; REAL_SUB_0] THEN
    ASM_CASES_TAC "g(x + z):real = g(x)" THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC "&1" THEN
      REWRITE_TAC[ABS_0; REAL_LT_01] THEN
      REWRITE_TAC[REAL_LE_ADDL; ABS_POS];
      MATCH_ACCEPT_TAC CHAIN_LEMMA2]]);;

%----------------------------------------------------------------------------%
% Differentiation of natural number powers                                   %
%----------------------------------------------------------------------------%

let DIFF_X = prove_thm(`DIFF_X`,
  "!x. ((\x. x) diffl &1)(x)",
  GEN_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN REWRITE_TAC[LIM; REAL_SUB_RZERO] THEN
  BETA_TAC THEN X_GEN_TAC "e:real" THEN DISCH_TAC THEN
  EXISTS_TAC "&1" THEN REWRITE_TAC[REAL_LT_01] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(\th. REWRITE_TAC[MATCH_MP REAL_DIV_REFL th]) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0]);;

let DIFF_POW = prove_thm(`DIFF_POW`,
  "!n x. ((\x. x pow n) diffl (&n * (x pow (n num_sub 1))))(x)",
  INDUCT_TAC THEN REWRITE_TAC[pow; DIFF_CONST; REAL_MUL_LZERO] THEN
  X_GEN_TAC "x:real" THEN
  POP_ASSUM(MP_TAC o CONJ(SPEC "x:real" DIFF_X) o SPEC "x:real") THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT_CONV "(a = b) ==> a ==> b") THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[REAL; REAL_RDISTRIB; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [] [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [REWRITE_TAC[ADD1; ADD_SUB];
    STRUCT_CASES_TAC (SPEC "n:num" num_CASES) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD1; ADD_SUB; POW_ADD] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[num_CONV "1"; pow] THEN
    REWRITE_TAC[SYM(num_CONV "1"); REAL_MUL_RID]]);;

%----------------------------------------------------------------------------%
% Now power of -1 (then differentiation of inverses follows from chain rule) %
%----------------------------------------------------------------------------%

let DIFF_XM1 = prove_thm(`DIFF_XM1`,
  "!x. ~(x = &0) ==> ((\x. inv(x)) diffl (--(inv(x) pow 2)))(x)",
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC "\h. --(inv(x + h) * inv(x))" THEN
  BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC "e:real" THEN DISCH_TAC THEN
    EXISTS_TAC "abs(x)" THEN
    EVERY_ASSUM(\th. REWRITE_TAC[REWRITE_RULE[ABS_NZ] th]) THEN
    X_GEN_TAC "h:real" THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN BETA_TAC THEN
    W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) "&0" o
      rand o rator o snd) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ABS_ZERO; REAL_SUB_0] THEN
    SUBGOAL_THEN "~(x + h = &0)" ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC "abs(h) < abs(--h)" THEN
      REWRITE_TAC[ABS_NEG; REAL_LT_REFL]; ALL_TAC] THEN
    W(\(asl,w). MP_TAC(SPECL ["x * (x + h)"; lhs w; rhs w] REAL_EQ_LMUL)) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[real_div; REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      "(a * b) * (c * d) = (c * b) * (d * a)"] THEN
    REWRITE_TAC(map (MATCH_MP REAL_MUL_LINV o ASSUME)
     ["~(x = &0)"; "~(x + h = &0)"]) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      "(a * b) * (c * d) = (a * d) * (c * b)"] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME "~(x = &0)")] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REWRITE_RULE[REAL_NEG_SUB]
      (AP_TERM "$--" (SPEC_ALL REAL_ADD_SUB))] THEN
    REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[ABS_NZ];

    REWRITE_TAC[POW_2] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV "h:real" "inv(x + h) * inv(x)"]) THEN
    REWRITE_TAC[GSYM LIM_NEG] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV "h:real") ["inv(x + h)"; "inv(x)"]))
    THEN MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN
    REWRITE_TAC[LIM_CONST] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV "h:real" "x + h"]) THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [] [GSYM REAL_ADD_RID] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV "h:real") ["x:real"; "h:real"])) THEN
    MATCH_MP_TAC LIM_ADD THEN BETA_TAC THEN REWRITE_TAC[LIM_CONST] THEN
    MATCH_ACCEPT_TAC LIM_X]);;

%----------------------------------------------------------------------------%
% Now differentiation of inverse and quotient                                %
%----------------------------------------------------------------------------%

let DIFF_INV = prove_thm(`DIFF_INV`,
  "!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)",
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; REAL_NEG_RMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP POW_INV (CONJUNCT2 th)]) THEN
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) DIFF_XM1) THEN
  ASM_REWRITE_TAC[]);;

let DIFF_DIV = prove_thm(`DIFF_DIV`,
  "!f g l m. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)",
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div] THEN
  MP_TAC(SPECL ["g:real->real"; "m:real"; "x:real"] DIFF_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME "(f diffl l)(x)")) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN SUBST1_TAC o mk_eq o
      ((rand o rator) # (rand o rator)) o dest_imp o snd) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
  REWRITE_TAC[REAL_LDISTRIB; REAL_RDISTRIB] THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[POW_2] THEN
    FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP REAL_INV_MUL (W CONJ th)]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID];
    REWRITE_TAC[real_div; GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    AP_TERM_TAC THEN CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM))]);;

%----------------------------------------------------------------------------%
% Differentiation of finite sum                                              %
%----------------------------------------------------------------------------%

let DIFF_SUM = prove_thm(`DIFF_SUM`,
  "!f f' m n x. (!r. m num_le r /\ r num_lt (m num_add n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. Sum(m,n)(\n. f n x)) diffl (Sum(m,n) (\r. f' r x)))(x)",
  REPEAT GEN_TAC THEN SPEC_TAC("n:num","n:num") THEN
  INDUCT_TAC THEN REWRITE_TAC[Sum; DIFF_CONST] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_ADD THEN
  BETA_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
    EXISTS_TAC "m num_add n" THEN ASM_REWRITE_TAC[ADD_CLAUSES; LESS_SUC_REFL];
    REWRITE_TAC[LESS_EQ_ADD; ADD_CLAUSES; LESS_SUC_REFL]]);;

%----------------------------------------------------------------------------%
% By bisection, function continuous on closed interval is bounded above      %
%----------------------------------------------------------------------------%

let CONT_BOUNDED = prove_thm(`CONT_BOUNDED`,
  "!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> contl f x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M",
  REPEAT STRIP_TAC THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    "\(u,v). a <= u /\ u <= v /\ v <= b ==>
               ?M. !x. u <= x /\ x <= v ==> f x <= M" THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (\t. REWRITE_TAC[t]) o funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL ["a:real"; "b:real"]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC ["u:real"; "v:real"; "w:real"] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN
    REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN "v <= b" ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "w:real" THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN "a <= v" ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "u:real" THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC "M1:real") THEN
    DISCH_THEN(X_CHOOSE_TAC "M2:real") THEN
    DISJ_CASES_TAC(SPECL ["M1:real"; "M2:real"] REAL_LE_TOTAL) THENL
     [EXISTS_TAC "M2:real" THEN X_GEN_TAC "x:real" THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL ["x:real"; "v:real"] REAL_LE_TOTAL) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "M1:real" THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC "M1:real" THEN X_GEN_TAC "x:real" THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL ["x:real"; "v:real"] REAL_LE_TOTAL) THENL
       [ALL_TAC; MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC "M2:real" THEN ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC "x:real" THEN ASM_CASES_TAC "a <= x /\ x <= b" THENL
   [ALL_TAC;
    EXISTS_TAC "&1" THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC ["u:real"; "v:real"] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC "~(a <= x /\ x <= b)" THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC "u:real"; EXISTS_TAC "v:real"] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC "!x. a <= x /\ x <= b ==> f contl x" THEN
  DISCH_THEN(MP_TAC o SPEC "x:real") THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[definition `LIM` `contl`; theorem `LIM` `LIM`] THEN
  DISCH_THEN(MP_TAC o SPEC "&1") THEN REWRITE_TAC[REAL_LT_01] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC ["u:real"; "v:real"] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC "abs(f(x:real)) + &1" THEN
  X_GEN_TAC "z:real" THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC "z - x") THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [] [REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_TAC THEN
  MP_TAC(SPECL ["f(z:real) - f(x)"; "(f:real->real) x"] ABS_TRIANGLE) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "abs(f(z:real))" THEN
  REWRITE_TAC[ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC "abs(f(x:real)) + (abs(f(z) - f(x)))" THEN
  ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_CASES_TAC "z:real = x" THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; ABS_0; REAL_LT_01];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
    ASM_REWRITE_TAC[REAL_SUB_0; abs; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC "v - u" THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC "v - x"; EXISTS_TAC "v - z"] THEN
    ASM_REWRITE_TAC[real_sub; REAL_LE_RADD; REAL_LE_LADD; REAL_LE_NEG]]);;

%----------------------------------------------------------------------------%
% Refine the above to existence of least upper bound                         %
%----------------------------------------------------------------------------%

let CONT_HASSUP = prove_thm(`CONT_HASSUP`,
  "!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))",
  let tm = "\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))" in
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC tm REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN (\t. REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC ["(f:real->real) a"; "a:real"] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_LT];
      POP_ASSUM(X_CHOOSE_TAC "M:real" o MATCH_MP CONT_BOUNDED) THEN
      EXISTS_TAC "M:real" THEN X_GEN_TAC "y:real" THEN
      DISCH_THEN(X_CHOOSE_THEN "x:real" MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
      POP_ASSUM MATCH_ACCEPT_TAC];
    DISCH_TAC THEN EXISTS_TAC "sup ^tm" THEN CONJ_TAC THENL
     [X_GEN_TAC "x:real" THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC "sup ^tm") THEN
      REWRITE_TAC[REAL_LT_REFL] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(MP_TAC o SPEC "(f:real->real) x") THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC "x:real") THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC "N:real") THEN
      DISCH_THEN(X_CHOOSE_THEN "y:real" MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN "x:real" MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      DISCH_TAC THEN EXISTS_TAC "x:real" THEN ASM_REWRITE_TAC[]]]);;

%----------------------------------------------------------------------------%
% Now show that it attains its upper bound                                   %
%----------------------------------------------------------------------------%

let CONT_ATTAINS = prove_thm(`CONT_ATTAINS`,
  "!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN "M:real" STRIP_ASSUME_TAC o MATCH_MP CONT_HASSUP)
  THEN EXISTS_TAC "M:real" THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [] [TAUT_CONV "a = ~~a"] THEN
  CONV_TAC(RAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT_CONV "~(a /\ b /\ c) = a /\ b ==> ~c"] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> f(x) < M" MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> contl (\x. inv(M - f(x))) x"
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_INV THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_SUB THEN BETA_TAC THEN
    REWRITE_TAC[CONT_CONST] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k"
  MP_TAC THENL
   [MATCH_MP_TAC CONT_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC "k:real") THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))" ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INV_POS THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)"
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC "k:real" THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_01] THEN
    BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==>
         inv(k + &1) < inv((\x. inv(M - (f x))) x)" MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    CONJ_TAC THENL
     [BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))"
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN "~(M - f(x:real) = &0)"
      (SUBST1_TAC o SYM o MATCH_MP REAL_INVINV) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  UNDISCH_TAC "!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))" THEN
  DISCH_THEN(MP_TAC o SPEC "M - inv(k + &1)") THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LT_ADDR] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC "k:real" THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC "inv(M - f(a:real))" THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_THEN(X_CHOOSE_THEN "x:real" MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Same theorem for lower bound                                               %
%----------------------------------------------------------------------------%

let CONT_ATTAINS2 = prove_thm(`CONT_ATTAINS2`,
  "!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))",
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> (\x. --(f x)) contl x" MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME "a <= b")) THEN
  DISCH_THEN(X_CHOOSE_THEN "M:real" MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  BETA_TAC THEN DISCH_TAC THEN EXISTS_TAC "--M" THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_LE_NEG] THEN
    ASM_REWRITE_TAC[REAL_NEGNEG];
    ASM_REWRITE_TAC[GSYM REAL_NEG_EQ]]);;

%----------------------------------------------------------------------------%
% If f'(x) > 0 then x is locally strictly increasing at the right            %
%----------------------------------------------------------------------------%

let DIFF_LINC = prove_thm(`DIFF_LINC`,
  "!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl; LIM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC "l:real") THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(\th. ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC ABS_SIGN THEN EXISTS_TAC "l:real" THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  ASM_REWRITE_TAC[abs]);;

%----------------------------------------------------------------------------%
% If f'(x) < 0 then x is locally strictly increasing at the left             %
%----------------------------------------------------------------------------%

let DIFF_LDEC = prove_thm(`DIFF_LDEC`,
  "!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl; LIM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC "--l") THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(\th. ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0; REAL_NEG_RMUL] THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP REAL_NEG_INV
   (GSYM (MATCH_MP REAL_LT_IMP_NE (CONJUNCT1 th)))]) THEN
  MATCH_MP_TAC ABS_SIGN2 THEN EXISTS_TAC "l:real" THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o funpow 3 LAND_CONV o RAND_CONV)
    [] [real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  REWRITE_TAC[abs; GSYM REAL_NEG_LE0; REAL_NEGNEG] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT]);;

%----------------------------------------------------------------------------%
% If f is differentiable at a local maximum x, f'(x) = 0                     %
%----------------------------------------------------------------------------%

let DIFF_LMAX = prove_thm(`DIFF_LMAX`,
  "!f x l. (diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)",
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN "k:real" STRIP_ASSUME_TAC)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL ["l:real"; "&0"] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o C CONJ(ASSUME "l < &0")) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LDEC) THEN
    DISCH_THEN(X_CHOOSE_THEN "e:real" MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL ["k:real"; "e:real"] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC "d:real") THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC "x - d") THEN REWRITE_TAC[REAL_SUB_SUB2] THEN
    SUBGOAL_THEN "&0 <= d" ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT];
    DISCH_THEN(MP_TAC o C CONJ(ASSUME "&0 < l")) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LINC) THEN
    DISCH_THEN(X_CHOOSE_THEN "e:real" MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL ["k:real"; "e:real"] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC "d:real") THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC "x + d") THEN REWRITE_TAC[REAL_ADD_SUB2] THEN
    SUBGOAL_THEN "&0 <= d" ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ABS_NEG] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT]]);;

%----------------------------------------------------------------------------%
% Similar theorem for a local minimum                                        %
%----------------------------------------------------------------------------%

let DIFF_LMIN = prove_thm(`DIFF_LMIN`,
  "!f x l. (diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL ["\x:real. --(f x)"; "x:real"; "--l"] DIFF_LMAX) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LE_NEG; REAL_NEG_EQ0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_NEG THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% In particular if a function is locally flat                                %
%----------------------------------------------------------------------------%

let DIFF_LCONST = prove_thm(`DIFF_LCONST`,
  "!f x l. (diffl f l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFF_LMAX THEN
  MAP_EVERY EXISTS_TAC ["f:real->real"; "x:real"] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(\th. FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL);;

%----------------------------------------------------------------------------%
% Lemma about introducing open ball in open interval                         %
%----------------------------------------------------------------------------%

let INTERVAL_LEMMA = prove_thm(`INTERVAL_LEMMA`,
  "!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b",
  REPEAT GEN_TAC THEN DISCH_THEN (\th.
    STRIP_ASSUME_TAC th THEN
    MP_TAC (ONCE_REWRITE_RULE[GSYM REAL_SUB_LT] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN "d:real" MP_TAC o MATCH_MP REAL_DOWN2) THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC "y:real" THEN
  REWRITE_TAC[abs; REAL_SUB_LE] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB; REAL_LT_SUB_RADD] THEN DISCH_TAC THEN CONJ_TAC
  THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "x - d" THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THENL
     [REWRITE_TAC[REAL_LT_SUB_LADD]; REWRITE_TAC[REAL_LT_SUB_RADD]] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "x:real" THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC "x:real" THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC "d + x" THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Now Rolle's theorem                                                        %
%----------------------------------------------------------------------------%

let ROLLE = prove_thm(`ROLLE`,
  "!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)",
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL ["f:real->real"; "a:real"; "b:real"] CONT_ATTAINS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN "M:real" MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC "x1:real")) THEN
  MP_TAC(SPECL ["f:real->real"; "a:real"; "b:real"] CONT_ATTAINS2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN "m:real" MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC "x2:real")) THEN
  ASM_CASES_TAC "a < x1 /\ x1 < b" THENL
   [FIRST_ASSUM(X_CHOOSE_THEN "d:real" MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC "x1:real" THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     "?l. (f diffl l)(x1) /\
          ?d. &0 < d /\ (!y. abs(x1 - y) < d ==> f(y) <= f(x1))" MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC "y:real" THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN "l:real" MP_TAC) THEN
    DISCH_THEN(\th. ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LMAX th))
    THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC "a < x2 /\ x2 < b" THENL
   [FIRST_ASSUM(X_CHOOSE_THEN "d:real" MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC "x2:real" THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     "?l. (f diffl l)(x2) /\
          ?d. &0 < d /\ (!y. abs(x2 - y) < d ==> f(x2) <= f(y))" MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC "y:real" THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN "l:real" MP_TAC) THEN
    DISCH_THEN(\th. ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LMIN th))
    THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN "!x. a <= x /\ x <= b ==> (f(x):real = f(b))" MP_TAC THENL
   [REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl)) THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REPEAT (DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o SYM) MP_TAC) THEN
            DISCH_THEN(SUBST_ALL_TAC o AP_TERM "f:real->real")) THEN
    UNDISCH_TAC "(f:real->real) a = f b" THEN
    DISCH_THEN(\th. SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    (CONJ_TAC THENL
      [SUBGOAL_THEN "(f:real->real) b = M" SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 3 o CONJUNCTS);
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
       SUBGOAL_THEN "(f:real->real) b = m" SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 3 o CONJUNCTS);
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);
    X_CHOOSE_TAC "x:real" (MATCH_MP REAL_MEAN (ASSUME "a < b")) THEN
    DISCH_TAC THEN EXISTS_TAC "x:real" THEN
    REWRITE_TAC[ASSUME "a < x /\ x < b"] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN "d:real" STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN "?l. (diffl f l)(x) /\
        (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x))))" MP_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC "d:real" THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
        DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN "l:real" (\th.
       ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LCONST th))) THEN
      ASM_REWRITE_TAC[]]]);;

%----------------------------------------------------------------------------%
% Mean value theorem                                                         %
%----------------------------------------------------------------------------%

let gfn = "\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)";;

let MVT_LEMMA = prove_thm(`MVT_LEMMA`,
  "!(f:real->real) a b. ^gfn(a) = ^gfn(b)",
  REPEAT GEN_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC "b:real = a" THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
  MP_TAC(GENL ["x:real"; "y:real"]
   (SPECL ["x:real"; "y:real"; "b - a"] REAL_EQ_RMUL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(\th. GEN_REWRITE_TAC I [] [GSYM th]) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [] [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)[] [REAL_MUL_SYM] THEN
  REWRITE_TAC[real_sub; REAL_LDISTRIB; REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL;
              REAL_NEG_ADD; REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    "w + x + y + z = (y + w) + (x + z)"; REAL_ADD_LINV; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ADD_RID]);;

let MVT = prove_thm(`MVT`,
  "!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [gfn; "a:real"; "b:real"] ROLLE) THEN
  W(C SUBGOAL_THEN (\t.REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
   [ASM_REWRITE_TAC[MVT_LEMMA] THEN BETA_TAC THEN
    CONJ_TAC THEN X_GEN_TAC "x:real" THENL
     [DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
      MATCH_MP_TAC CONT_SUB THEN CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC CONT_MUL THEN
        REWRITE_TAC[CONT_CONST] THEN MATCH_MP_TAC DIFF_CONT THEN
        EXISTS_TAC "&1" THEN MATCH_ACCEPT_TAC DIFF_X];
      DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(X_CHOOSE_TAC "l:real") THEN
      EXISTS_TAC "l - ((f(b) - f(a)) / (b - a))" THEN
      CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_SUB THEN
      CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [] [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC DIFF_CMUL THEN MATCH_ACCEPT_TAC DIFF_X]];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN "z:real" MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN($THEN (MAP_EVERY EXISTS_TAC
   ["((f(b) - f(a)) / (b - a))"; "z:real"]) o MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN($THEN CONJ_TAC o MP_TAC) THENL
   [ALL_TAC; DISCH_THEN(K ALL_TAC) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC "a < a" THEN
    REWRITE_TAC[REAL_LT_REFL]] THEN
  SUBGOAL_THEN "((\x. ((f(b) - f(a)) / (b - a)) * x ) diffl
                      ((f(b) - f(a)) / (b - a)))(z)"
  (\th. DISCH_THEN(MP_TAC o C CONJ th)) THENL
   [CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [] [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CMUL THEN REWRITE_TAC[DIFF_X]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

%----------------------------------------------------------------------------%
% Theorem that function is constant if its derivative is 0 over an interval. %
%                                                                            %
% We could have proved this directly by bisection; consider instantiating    %
% BOLZANO_LEMMA with                                                         %
%                                                                            %
%     \(x,y). f(y) - f(x) <= C * (y - x)                                     %
%                                                                            %
% However the Rolle and Mean Value theorems are useful to have anyway        %
%----------------------------------------------------------------------------%

let DIFF_ISCONST_END = prove_thm(`DIFF_ISCONST_END`,
  "!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL ["f:real->real"; "a:real"; "b:real"] MVT) THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
    DISCH_THEN($THEN (EXISTS_TAC "&0") o MP_TAC) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(\th. REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN "l:real" (X_CHOOSE_THEN "x:real" MP_TAC)) THEN
  ONCE_REWRITE_TAC[TAUT_CONV "a /\ b /\ c /\ d = (a /\ b) /\ (c /\ d)"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(\th. FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME "(f diffl l)(x)")) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP DIFF_UNIQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO; REAL_SUB_0]) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let DIFF_ISCONST = prove_thm(`DIFF_ISCONST`,
  "!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL ["f:real->real"; "a:real"; "x:real"] DIFF_ISCONST_END) THEN
  DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME "a <= x")) THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC "z:real" THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC "x:real";
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC "x:real"] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let DIFF_ISCONST_ALL = prove_thm(`DIFF_ISCONST_ALL`,
  "!f. (!x. (f diffl &0)(x)) ==> (!x y. f(x) = f(y))",
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN "!x. f contl x" ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC "&0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL ["x:real"; "y:real"] REAL_LT_TOTAL) THENL
   [DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    CONV_TAC(RAND_CONV SYM_CONV);
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
  ASM_REWRITE_TAC[]);;

close_theory();;
