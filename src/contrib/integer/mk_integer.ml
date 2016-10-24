% FILE		: mk_integer.ml						%
% DESCRIPTION   : defines the type of integer, the operations of        %
%                 plus, minus, neg, and times, the predicates POS,      %
%                 and NEG, and the relation below.  Develops much of    %
%                 the basic algebraic, and some basic order theoretic   %
%                 properties of the integers.				%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
% Modified 23 July 1989 to include more theorems. ELG			%
%									%
%-----------------------------------------------------------------------%

% --------------------------------------------------------------------- %
% add_lib_path `group`;; Not needed for HOL88.1.05 (MJCG 14 April, 1989)%
% But, see below. [TFM 90.12.02]					%
% --------------------------------------------------------------------- %

new_theory `integer`;;

% --------------------------------------------------------------------- %
% Uses (only) parts of the group library!		 [TFM 90.12.02] %
% --------------------------------------------------------------------- %

load_library `group`;;
new_parent `elt_gp`;;
loadf `load_elt_gp`;;

new_parent `more_arith`;;
loadf `load_more_arith`;;

let IS_INTEGER_DEF=new_definition(`IS_INTEGER_DEF`,"is_integer (X:num#num) =
 ((?p.X=(p,0))\/(?n.X=(0,n)))");;

%|- !X. is_integer X = (?p:num. X = p,0) \/ (?n:num. X = 0,n)%

let thm1=prove("is_integer (p,0)",
((PURE_ONCE_REWRITE_TAC [IS_INTEGER_DEF]) THEN
 DISJ1_TAC THEN
 (EXISTS_TAC "p:num") THEN
 REFL_TAC));;

%thm1 = |- is_integer(p,0)%


let thm2=prove("is_integer (0,n)",
((PURE_ONCE_REWRITE_TAC [IS_INTEGER_DEF]) THEN
 DISJ2_TAC THEN
 (EXISTS_TAC "n:num") THEN
 REFL_TAC));;

%thm2 = |- is_integer(0,n)%

let thm3=prove("?X.(is_integer X)",
 ((EXISTS_TAC "(p:num,0)") THEN (ACCEPT_TAC thm1)));;

%thm3 = |- ?X:num # num. is_integer X%


let integer_TY_DEF = new_type_definition (`integer`,"is_integer",thm3);;

% integer_TY_DEF = |- ?rep. TYPE_DEFINITION is_integer rep		%

let integer_ISO_DEF =
  define_new_type_bijections
    `integer_ISO_DEF` `ABS_integer` `REP_integer` integer_TY_DEF;;

%
integer_ISO_DEF = 
|- (!a. ABS_integer(REP_integer a) = a) /\
   (!r. is_integer r = (REP_integer(ABS_integer r) = r))
%

let thm4 = prove_rep_fn_one_one integer_ISO_DEF and
    thm5 = prove_rep_fn_onto integer_ISO_DEF;;

%
thm4 = |- !a a'. (REP_integer a = REP_integer a') = (a = a')
thm5 = |- !r. is_integer r = (?a. r = REP_integer a)
%

let thm4 = SPECL ["N1:integer";"N2:integer"] thm4;;

%thm4 = |- (REP_integer N1 = REP_integer N2) = (N1 = N2)%

include_definitions `integer`;;

%
  IS_INTEGER_DEF  |- !X. is_integer X = (?p. X = p,0) \/ (?n. X = 0,n)
  integer_TY_DEF  |- ?rep. TYPE_DEFINITION is_integer rep
  REP_integer
    |- REP_integer =
       (@rep.
         (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\
         (!x. is_integer x = (?x'. x = rep x')))
  ABS_integer  |- !x. ABS_integer x = (@x'. x = REP_integer x')
%

%What follows is a collection of lemmas useful for dealing with REP_integer%

let thm5a = prove("!X. (?N.REP_integer N=X)=is_integer X",
(GEN_TAC THEN 
 (SUBST_TAC [(SPEC "X:num#num" thm5)]) THEN 
 (ACCEPT_TAC
  (EXISTS_EQ 
    "N:integer"
    (AUTO_SPECL["REP_integer N";"X:num#num"]EQ_SYM_EQ)))));;

%thm5a = |- !X:num # num. (?N:integer. REP_integer N = X) = is_integer X%


let thm6 = ((prove ("is_integer(REP_integer M)",
 ((PURE_REWRITE_TAC[(SPEC "X:num#num" thm5)]) THEN
  (EXISTS_TAC "M:integer") THEN
  (ACCEPT_TAC (REFL "REP_integer M")))))
and_then (REWRITE_RULE [IS_INTEGER_DEF]));;

%thm6 = |- (?p:num. REP_integer M = p,0) \/ (?n:num. REP_integer M = 0,n)%


let thm6a = prove ("REP_integer M=
 ((SND(REP_integer M)) < (FST(REP_integer M)) => 
  ((FST(REP_integer M)) - (SND(REP_integer M)),0) | 
  (0,(SND(REP_integer M)) - (FST(REP_integer M)))) ",
((DISJ_CASES_TAC thm6) THENL
 [(SUBST1_TAC(SELECT_RULE(ASSUME(fst(dest_disj(concl(thm6)))))));
  (SUBST1_TAC(SELECT_RULE(ASSUME(snd(dest_disj(concl(thm6)))))))] THEN
 (PURE_REWRITE_TAC([FST;SND]@(CONJUNCTS (SPEC_ALL SUB_0))))THEN
 NEW_COND_CASES_TAC THENL
 [REFL_TAC;
  ((SUBST1_TAC (SYM(UNDISCH_ALL(DISJ_IMP(PURE_ONCE_REWRITE_RULE[DISJ_SYM]
   (SPEC("(@p:num. REP_integer M = p,0)") LESS_0_CASES))))))THEN 
   REFL_TAC);
  (CONTR_TAC (FALSITY_INTRO
   (ASSUME "(@n:num. REP_integer M = 0,n)<0")
   (SPEC "(@n:num. REP_integer M = 0,n)"NOT_LESS_0)));
  REFL_TAC]));;

%thm6a = 
 |- REP_integer M =
    ((SND(REP_integer M)) < (FST(REP_integer M)) => 
     ((FST(REP_integer M)) - (SND(REP_integer M)),0) | 
     (0,(SND(REP_integer M)) - (FST(REP_integer M))))%


let thm7  = prove("REP_integer(@N.((n,0) = REP_integer N))= (n,0)",
((CONV_TAC SYM_CONV) THEN (SELECT_TAC "@N.((n,0)=REP_integer N)") THEN
 (REWRITE_TAC [(SYM(SPEC "X:num#num" thm5))]) THEN
 (REWRITE_TAC [IS_INTEGER_DEF]) THEN DISJ1_TAC THEN
 (EXISTS_TAC "n:num") THEN (REWRITE_TAC [])));;

%thm7 = |- REP_integer(@N:integer. n,0 = REP_integer N) = n,0%


let thm7a  = prove("REP_integer(@N.(REP_integer N = (n,0)))= (n,0)",
((SELECT_TAC "@N.REP_integer N=(n,0)") THEN
 (REWRITE_TAC [(SPEC "X:num#num" thm5a)]) THEN
 (REWRITE_TAC [IS_INTEGER_DEF]) THEN DISJ1_TAC THEN
 (EXISTS_TAC "n:num") THEN (REWRITE_TAC [])));;

%thm7a = |- REP_integer(@N:integer. REP_integer N = n,0) = n,0%


let thm8  = prove("REP_integer(@N.((0,n) = REP_integer N))= (0,n)",
((CONV_TAC SYM_CONV) THEN (SELECT_TAC "@N.((0,n)=REP_integer N)") THEN
 (REWRITE_TAC [(SYM(SPEC "X:num#num" thm5))]) THEN
 (REWRITE_TAC [IS_INTEGER_DEF]) THEN DISJ2_TAC THEN
 (EXISTS_TAC "n:num") THEN (REWRITE_TAC [])));;

%thm8 = |- REP_integer(@N:integer. 0,n = REP_integer N) = 0,n%


let thm8a  = prove("REP_integer(@N.(REP_integer N = (0,n)))= (0,n)",
((SELECT_TAC "@N.(REP_integer N=(0,n))") THEN
 (REWRITE_TAC [(SPEC "X:num#num" thm5a)]) THEN
 (REWRITE_TAC [IS_INTEGER_DEF]) THEN DISJ2_TAC THEN
 (EXISTS_TAC "n:num") THEN (REWRITE_TAC [])));;

%thm8a = |- REP_integer(@N:integer. REP_integer N = 0,n) = 0,n%


%The Natural Numbers can be embedded into the integers.%


let INT_DEF=new_definition (`INT_DEF`,"INT p=(@N.((p,0)=REP_integer N))");;

%INT_DEF = |- !p. INT p = (@N:integer. p,0 = REP_integer N)%


let INT_ONE_ONE = prove_thm (`INT_ONE_ONE`,
"!m n.(INT m =INT n) = (m = n)",
  ((REPEAT GEN_TAC) THEN EQ_TAC THENL 
  [(ACCEPT_TAC(
    (ASSUME "INT m =INT n") and_then
    (PURE_ONCE_REWRITE_RULE [INT_DEF]) and_then
    (AP_TERM "REP_integer") and_then
    (PURE_ONCE_REWRITE_RULE [thm7]) and_then
    (AP_TERM "FST:(num#num)->num") and_then
    (PURE_ONCE_REWRITE_RULE [FST]) and_then
    DISCH_ALL));
   (DISCH_TAC THEN AP_TERM_TAC THEN (FIRST_ASSUM ACCEPT_TAC))]));;

%INT_ONE_ONE = |- !m:num n:num. (INT m = INT n) = (m = n)%


%The ring structure of the integers%

%In defining the operations which shall yield the ring structure on the
 integers, we shall proceed by definining appropriate opperations on
 ":num#num" and then projecting on to the integers.%

let PROJ_DEF = new_definition(`PROJ_DEF`, "proj (p,n)=
 (n<p=>(@K1:integer.REP_integer K1 = ((p-n),0)) |
       (@K1:integer.REP_integer K1 = (0,(n-p))) )");;

%PROJ_DEF = 
 |- !p n.
     proj(p,n) =
     (n < p => 
      (@K1:integer. REP_integer K1 = p - n,0) | 
      (@K1:integer. REP_integer K1 = 0,n - p))%


%The additive group structure%

let PLUS_DEF = new_infix_definition(`PLUS_DEF`,"plus M N =
    (proj(((FST(REP_integer M)) + (FST(REP_integer N))),
       ((SND(REP_integer M)) + (SND(REP_integer N)))))");;

%PLUS_DEF = 
 |- !M N.
     M plus N =
     proj
     ((FST(REP_integer M)) + (FST(REP_integer N)),
      (SND(REP_integer M)) + (SND(REP_integer N)))%


let thm9 = prove ("REP_integer (M plus N) =
 (((SND(REP_integer M))+(SND(REP_integer N)))
  <((FST(REP_integer M))+(FST(REP_integer N))))
 =>((((FST(REP_integer M))+(FST(REP_integer N)))-
     ((SND(REP_integer M))+(SND(REP_integer N)))),0)
  |(0,(((SND(REP_integer M))+(SND(REP_integer N)))-
       ((FST(REP_integer M))+(FST(REP_integer N)))))",
((PURE_REWRITE_TAC [PLUS_DEF;PROJ_DEF]) THEN
 NEW_COND_CASES_TAC THEN
 (REWRITE_TAC [thm7a;thm8a])));;

%thm9 = 
 |- REP_integer(M plus N) =
    (((SND(REP_integer M)) + (SND(REP_integer N))) <
     ((FST(REP_integer M)) + (FST(REP_integer N))) => 
     (((FST(REP_integer M)) + (FST(REP_integer N))) -
      ((SND(REP_integer M)) + (SND(REP_integer N))),0) | 
     (0,
      ((SND(REP_integer M)) + (SND(REP_integer N))) -
      ((FST(REP_integer M)) + (FST(REP_integer N)))))%


let NUM_ADD_IS_INT_ADD = prove_thm (`NUM_ADD_IS_INT_ADD`,
"!m n. (INT m) plus (INT n) = INT (m + n)",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[(SYM thm4);thm9]) THEN
 (SUBST_TAC[(INST [("INT(m+n)","M:integer")] thm6a)]) THEN
 (PURE_ONCE_REWRITE_TAC[INT_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[thm7]) THEN
 (PURE_ONCE_REWRITE_TAC[FST;SND]) THEN
 (PURE_ONCE_REWRITE_TAC[(CONJUNCT1 ADD_CLAUSES)]) THEN
 REFL_TAC));;

%NUM_ADD_IS_INT_ADD = |- !m:num n:num. (INT m) plus (INT n) = INT(m + n)%


let ASSOC_PLUS = prove_thm (`ASSOC_PLUS`,
"!M N P. M plus (N plus P) = (M plus N) plus P",
(let M1="(FST(REP_integer M))" in
 let M2="(SND(REP_integer M))" in
 let N1="(FST(REP_integer N))" in
 let N2="(SND(REP_integer N))" in
 let P1="(FST(REP_integer P))" in
 let P2="(SND(REP_integer P))" in
 let MN=TAC_PROOF((["(^M2+^N2)<(^M1+^N1)"],
  "(^P2<(((^M1+^N1)+^P1)-(^M2+^N2)))=(((^M2+^N2)+^P2)<((^M1+^N1)+^P1))"),
  ((ASSUME_TAC(SPECL["^M2+^N2";"^M1+^N1";P1]ADDR_GREATER)) THEN RES_TAC THEN
   (ASSUME_TAC(SPECL["^M2+^N2";"(^M1+^N1)+^P1"]LESS_IMP_LESS_OR_EQ)) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["((^M1+^N1)+^P1)";"^M2+^N2";P2]LESS_SUB_TO_ADDL_LESS))
   THEN RES_TAC THEN (FIRST_ASSUM ACCEPT_TAC) )) in
 let NOT_MN=TAC_PROOF((["~((^M2+^N2)<(^M1+^N1))"],
  "((((^M2+^N2)+^P2)-(^M1+^N1))<^P1)=(((^M2+^N2)+^P2)<((^M1+^N1)+^P1))"),
  ((ASSUME_TAC(fst(EQ_IMP_RULE(SPECL["^M2+^N2";"^M1+^N1"]NOT_LESS)))) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["^M1+^N1";"^M2+^N2";P2]ADDR_GREATER_EQ)) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["(^M2+^N2)+^P2";"^M1+^N1";P1]SUB_LESS_TO_LESS_ADDL))
   THEN RES_TAC THEN (FIRST_ASSUM ACCEPT_TAC) )) in
 let NP=TAC_PROOF((["(^N2+^P2)<(^N1+^P1)"],
"^M2<((^M1+(^N1+^P1))-(^N2+^P2))=((^M2+(^N2+^P2))<(^M1+(^N1+^P1)))"),
  ((ASSUME_TAC(SPECL["^N2+^P2";"^N1+^P1";M1]ADDL_GREATER)) THEN RES_TAC THEN
   (ASSUME_TAC(SPECL["^N2+^P2";"^M1+(^N1+^P1)"]LESS_IMP_LESS_OR_EQ)) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["^M1+(^N1+^P1)";M2;"^N2+^P2"]LESS_SUB_TO_ADDR_LESS))
   THEN RES_TAC THEN (FIRST_ASSUM ACCEPT_TAC) )) in
 let NOT_NP=TAC_PROOF((["~((^N2+^P2)<(^N1+^P1))"],
  "(((^M2+(^N2+^P2))-(^N1+^P1))<^M1)=((^M2+(^N2+^P2))<(^M1+(^N1+^P1)))"),
  ((ASSUME_TAC(fst(EQ_IMP_RULE(SPECL["^N2+^P2";"^N1+^P1"]NOT_LESS)))) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["^N1+^P1";"^N2+^P2";M2]ADDL_GREATER_EQ)) THEN
   RES_TAC THEN
   (ASSUME_TAC(SPECL["^M2+(^N2+^P2)";M1;"^N1+^P1"]SUB_LESS_TO_LESS_ADDR))
   THEN RES_TAC THEN (FIRST_ASSUM ACCEPT_TAC) )) in
 (REPEAT GEN_TAC) THEN (PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]) THEN
 (PURE_REWRITE_TAC[(SYM(thm4));thm9]) THEN
 (FILTER_COND_CASES_TAC "(^M2 + ^N2)<(^M1 + ^N1)") THEN
 (FILTER_COND_CASES_TAC "(^N2 + ^P2)<(^N1 + ^P1)") THEN
 (PURE_REWRITE_TAC
  [(AUTO_SPECL ["m:num";"n:num"] FST);(AUTO_SPECL ["m:num";"n:num"] SND);
   (CONJUNCT1 ADD_CLAUSES);(CONJUNCT1(CONJUNCT2 ADD_CLAUSES))]) THENL

(let NP_TAC=(
 (SUBST1_TAC
  (UNDISCH_ALL(IMP_TRANS (SPECL["^N2+^P2";"^N1+^P1"]LESS_IMP_LESS_OR_EQ)
   (SPECL[M1;"^N1+^P1";"^N2+^P2"]SIMP1)))) THEN
 (SUBST1_TAC NP) THEN
 (SUBST1_TAC
  (REWRITE_RULE[(SPECL["^N2+^P2";M2]ADD_SYM)]
   (SPECL["^M1+(^N1+^P1)";"^N2+^P2";M2]DOUBLE_SUB))) THEN
 (SUBST1_TAC
  (UNDISCH_ALL(IMP_TRANS (SPECL["^N2+^P2";"^N1+^P1"]LESS_IMP_LESS_OR_EQ)
   (IMP_TRANS (SPECL["^N2+^P2";"^N1+^P1";M1]ADDL_GREATER_EQ)
    (SPECL[M2;"^N2+^P2";"^M1+(^N1+^P1)"]SIMP3))))) ) in
 let MN_TAC = (
 (SUBST1_TAC
  (UNDISCH_ALL(IMP_TRANS (SPECL["^M2+^N2";"^M1+^N1"]LESS_IMP_LESS_OR_EQ)
   (SPECL["^M1+^N1";P1;"^M2+^N2"]SIMP2)))) THEN
 (SUBST1_TAC MN) THEN
 (SUBST1_TAC (SPECL["(^M1+^N1)+^P1";"^M2+^N2";P2]DOUBLE_SUB)) THEN
 (SUBST1_TAC
  (REWRITE_RULE[(SPECL["m:num";"^M2+^N2"]ADD_SYM)]
   (UNDISCH_ALL(IMP_TRANS (SPECL["^M2+^N2";"^M1+^N1"]LESS_IMP_LESS_OR_EQ)
    (IMP_TRANS (SPECL["^M2+^N2";"^M1+^N1";P1]ADDR_GREATER_EQ)
     (SPECL[P2;"^M2+^N2";"(^M1+^N1)+^P1"]SIMP3)))))) ) in
 let NOT_NP_TAC = (
 (SUBST1_TAC
   (UNDISCH_ALL(IMP_TRANS
    (fst(EQ_IMP_RULE(SPECL["^N2+^P2";"^N1+^P1"]NOT_LESS)))
    (SPECL[M2;"^N2+^P2";"^N1+^P1"]SIMP1)))) THEN
 (SUBST1_TAC NOT_NP) THEN
 (SUBST1_TAC
  (UNDISCH_ALL(IMP_TRANS
   (fst(EQ_IMP_RULE(SPECL["^N2+^P2";"^N1+^P1"]NOT_LESS)))
   (IMP_TRANS (SPECL["^N1+^P1";"^N2+^P2";M2]ADDL_GREATER_EQ)
   (SPECL[M1;"^N1+^P1";"^M2+(^N2+^P2)"]SIMP3))))) THEN
 (SUBST1_TAC
   (REWRITE_RULE[(SPECL["^N1+^P1";M1]ADD_SYM)]
    (SPECL["^M2+(^N2+^P2)";"^N1+^P1";M1]DOUBLE_SUB))) )in
 let NOT_MN_TAC = (
 (SUBST1_TAC
   (UNDISCH_ALL(IMP_TRANS
    (fst(EQ_IMP_RULE(SPECL["^M2+^N2";"^M1+^N1"]NOT_LESS)))
    (SPECL["^M2+^N2";P2;"^M1+^N1"]SIMP2)))) THEN
 (SUBST1_TAC NOT_MN) THEN
 (SUBST1_TAC
  (REWRITE_RULE[(SPECL["m:num";"^M1+^N1"]ADD_SYM)]
   (UNDISCH_ALL(IMP_TRANS
    (fst(EQ_IMP_RULE(SPECL["^M2+^N2";"^M1+^N1"]NOT_LESS)))
    (IMP_TRANS (SPECL["^M1+^N1";"^M2+^N2";P2]ADDR_GREATER_EQ)
     (SPECL[P1;"^M1+^N1";"(^M2+^N2)+^P2"]SIMP3)))))) THEN
 (SUBST1_TAC (SPECL["(^M2+^N2)+^P2";"^M1+^N1";P1]DOUBLE_SUB)) )in
[(MN_TAC THEN NP_TAC);
 (MN_TAC THEN NOT_NP_TAC);
 (NOT_MN_TAC THEN NP_TAC);
 (NOT_MN_TAC THEN NOT_NP_TAC)]) THEN

(REWRITE_TAC [(SPEC_ALL ADD_ASSOC)]) ));;

%ASSOC_PLUS = 
 |- !M:integer N:integer P:integer.  M plus (N plus P) = (M plus N) plus P%


let COMM_PLUS = prove_thm (`COMM_PLUS`,
"!M N. M plus N =N plus M",
(let M1="FST(REP_integer M)" in
 let M2="SND(REP_integer M)" in
 let N1="FST(REP_integer N)" in
 let N2="SND(REP_integer N)" in
 (REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[(SYM(thm4));thm9]) THEN
 (SUBST_TAC [(SPECL[N1;M1]ADD_SYM);(SPECL[N2;M2]ADD_SYM)]) THEN
 REFL_TAC));;

%COMM_PLUS = |- !M:integer N:integer. M plus N = N plus M%


let PLUS_ID = prove_thm (`PLUS_ID`,
"!M. ((INT 0) plus M = M)",
(GEN_TAC THEN
 (PURE_REWRITE_TAC[(SYM thm4);thm9]) THEN
 (PURE_REWRITE_TAC[INT_DEF;thm7]) THEN
 (PURE_REWRITE_TAC[FST;SND]) THEN
 (REWRITE_TAC [(CONJUNCT1 ADD_CLAUSES)])THEN
 (ACCEPT_TAC(SYM thm6a))));;

%PLUS_ID = 
 |- !M:integer. (INT 0) plus M = M%


let thm10 = prove("!M.?N.REP_integer N=
  ((SND(REP_integer M)),(FST(REP_integer M)))",
(GEN_TAC THEN
 (PURE_ONCE_REWRITE_TAC[(SPEC_ALL(EQ_SYM_EQ))]) THEN
 (PURE_REWRITE_TAC[(SYM(SPEC_ALL thm5))]) THEN
 (DISJ_CASES_TAC thm6) THEN
 (FIRST_ASSUM(\thm.(PURE_ONCE_REWRITE_TAC[(SELECT_RULE(thm))]))) THEN
 (PURE_REWRITE_TAC
  [(AUTO_SPECL["m:num";"n:num"] FST);(AUTO_SPECL ["m:num";"n:num"] SND)])
 THENL
 [(ACCEPT_TAC(INST[("(@p:num. REP_integer M = p,0)","n:num")] thm2));
  (ACCEPT_TAC(INST[("(@n:num. REP_integer M = 0,n)","p:num")] thm1))]));;

%thm10 =
 |- !M:integer.
     ?N:integer. REP_integer N = SND(REP_integer M),FST(REP_integer M)%


let thm10a = prove("(@N.REP_integer N = 
 (SND(REP_integer M),FST(REP_integer M))) plus M = INT 0",
((PURE_REWRITE_TAC[(SYM thm4);thm9]) THEN
 (PURE_ONCE_REWRITE_TAC[(SELECT_RULE(SPEC_ALL thm10))]) THEN
 (PURE_REWRITE_TAC[FST;SND]) THEN
 (SUBST1_TAC(SPECL["SND(REP_integer M)";"FST(REP_integer M)"]ADD_SYM)) THEN
 (REWRITE_TAC[INT_DEF;thm7]) THEN
 NEW_COND_CASES_TAC THEN
 (REWRITE_TAC [SUB_SAME_EQ_0]) ));;

%thm10a = 
|- (@N. REP_integer N = SND(REP_integer M),FST(REP_integer M)) plus M =
   INT 0%


let PLUS_INV=prove_thm(`PLUS_INV`,
"!M.?N.N plus M=INT 0",
(GEN_TAC THEN
 (EXISTS_TAC "@N.REP_integer N = SND(REP_integer M),FST(REP_integer M)") THEN
  (ACCEPT_TAC thm10a)));;

%PLUS_INV = |- !M:integer. ?N:integer. N plus M = INT 0%

%Now we have proven the pieces neccesary to show that the integers under
 addition form a group.  We shall formally prove this fact, and then
 instantiate the theory of groups in this particular case. %


let integer_as_GROUP=prove_thm(`integer_as_GROUP`,
"GROUP((\N:integer.T),$plus)",
((PURE_ONCE_REWRITE_TAC[GROUP_DEF]) THEN BETA_TAC THEN
  (REWRITE_TAC[(SYM (SPEC_ALL ASSOC_PLUS))]) THEN (EXISTS_TAC "INT 0") THEN
  (REWRITE_TAC[PLUS_ID;PLUS_INV])));;

%integer_as_GROUP = |- GROUP((\N. T),$plus)%

let ID_EQ_0 = prove_thm(`ID_EQ_0`,"ID((\N:integer.T),$plus) = INT 0",
((PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ]) THEN
 (MP_IMP_TAC (SPEC "INT 0" 
  (return_GROUP_thm `UNIQUE_ID` integer_as_GROUP []))) THEN
  DISJ1_TAC THEN (EXISTS_TAC "M:integer") THEN
  (ACCEPT_TAC (SPEC "M:integer" PLUS_ID))));;

%ID_EQ_0 = |- ID((\N. T),$plus) = INT 0%


let neg_DEF = new_definition (`neg_DEF`,"neg = INV((\N:integer.T),$plus)");;

%neg_DEF = |- neg = INV((\N. T),$plus)%

include_GROUP_theory `PLUS` integer_as_GROUP [ID_EQ_0;(SYM neg_DEF)];;

%[(); (); (); (); (); (); (); (); (); (); (); (); (); ()] : void list

PLUS_GROUP_ASSOC = |- !x y z. (x plus y) plus z = x plus (y plus z)

PLUS_ID_LEMMA = 
|- (!x. (INT 0) plus x = x) /\
   (!x. x plus (INT 0) = x) /\
   (!x. ?y. y plus x = INT 0)

PLUS_LEFT_RIGHT_INV = |- !x y. (y plus x = INT 0) ==> (x plus y = INT 0)

PLUS_INV_LEMMA = 
|- !x. ((neg x) plus x = INT 0) /\ (x plus (neg x) = INT 0)

PLUS_LEFT_CANCELLATION = |- !x y z. (x plus y = x plus z) ==> (y = z)

PLUS_RIGHT_CANCELLATION = |- !x y z. (y plus x = z plus x) ==> (y = z)

PLUS_RIGHT_ONE_ONE_ONTO = 
|- !x y. ?z. (x plus z = y) /\ (!u. (x plus u = y) ==> (u = z))

PLUS_LEFT_ONE_ONE_ONTO = 
|- !x y. ?z. (z plus x = y) /\ (!u. (u plus x = y) ==> (u = z))

PLUS_UNIQUE_ID = 
|- !e. (?x. e plus x = x) \/ (?x. x plus e = x) ==> (e = INT 0)

PLUS_UNIQUE_INV = |- !x u. (u plus x = INT 0) ==> (u = neg x)

PLUS_INV_ID_LEMMA = |- neg(INT 0) = INT 0

PLUS_INV_INV_LEMMA = |- !x. neg(neg x) = x

PLUS_DIST_INV_LEMMA = |- !x y. (neg x) plus (neg y) = neg(y plus x)
%

%These are principly for compatability with previous versions%

let neg_PLUS_DISTRIB =save_thm (`neg_PLUS_DISTRIB`,
(SYM(SUBS[(SPECL ["N:integer";"M:integer"] COMM_PLUS)]
 (SPECL["M:integer";"N:integer"] PLUS_DIST_INV_LEMMA))));;

%neg_PLUS_DISTRIB = |- neg(M plus N) = (neg M) plus (neg N)%

let PLUS_IDENTITY = prove_thm (`PLUS_IDENTITY`,
"!M. (M plus (INT 0) = M) /\ ((INT 0) plus M = M)",
(REWRITE_TAC[PLUS_ID_LEMMA]));;

%PLUS_IDENTITY = |- !M. (M plus (INT 0) = M) /\ ((INT 0) plus M = M)%

let PLUS_INVERSE = prove_thm (`PLUS_INVERSE`,
"!M. (M plus (neg M) = INT 0) /\ ((neg M) plus M = INT 0)",
(REWRITE_TAC[PLUS_INV_LEMMA]));;

%PLUS_INVERSE =
|- !M. (M plus (neg M) = INT 0) /\ ((neg M) plus M = INT 0)%

let NEG_NEG_IS_IDENTITY = prove_thm (`NEG_NEG_IS_IDENTITY`,
"!M. (neg (neg M)) = M", (REWRITE_TAC[PLUS_INV_INV_LEMMA]));;

%NEG_NEG_IS_IDENTITY = |- !M. neg(neg M) = M%

%This is used in the order theory later on.%
let thm11 = ((SPEC_ALL thm10) and_then SELECT_RULE and_then
  (PURE_ONCE_REWRITE_RULE[(MP
    (SPECL ["M:integer";
            "@N. REP_integer N = SND(REP_integer M),FST(REP_integer M)"]
            PLUS_UNIQUE_INV) thm10a)]));;

%thm11 = |- REP_integer(neg M) = SND(REP_integer M),FST(REP_integer M)%


let MINUS_DEF = new_infix_definition(`MINUS_DEF`, "minus M N = 
                   (M plus (neg N))");;

%MINUS_DEF = |- !M N. M minus N = M plus (neg N)%


%The multiplicative structure of the integers%

let TIMES_DEF = new_infix_definition(`TIMES_DEF`, "times M N =
 (proj(
       (((FST(REP_integer M)) * (FST(REP_integer N))) +
        ((SND(REP_integer M)) * (SND(REP_integer N)))),
       (((FST(REP_integer M)) * (SND(REP_integer N))) +
        ((SND(REP_integer M)) * (FST(REP_integer N)))) ))" );;

%TIMES_DEF = 
 |- !M N.
     M times N =
     proj
     (((FST(REP_integer M)) * (FST(REP_integer N))) +
      ((SND(REP_integer M)) * (SND(REP_integer N))),
      ((FST(REP_integer M)) * (SND(REP_integer N))) +
      ((SND(REP_integer M)) * (FST(REP_integer N))))%


let thm12 = prove("REP_integer(M times N) =
   ((((FST(REP_integer M)) * (SND(REP_integer N))) +
     ((SND(REP_integer M)) * (FST(REP_integer N)))) <
    (((FST(REP_integer M)) * (FST(REP_integer N))) +
     ((SND(REP_integer M)) * (SND(REP_integer N)))) => 
     ((((FST(REP_integer M)) * (FST(REP_integer N))) +
       ((SND(REP_integer M)) * (SND(REP_integer N)))) -
      (((FST(REP_integer M)) * (SND(REP_integer N))) +
       ((SND(REP_integer M)) * (FST(REP_integer N)))),0) | 
     (0,
      (((FST(REP_integer M)) * (SND(REP_integer N))) +
       ((SND(REP_integer M)) * (FST(REP_integer N)))) -
      (((FST(REP_integer M)) * (FST(REP_integer N))) +
       ((SND(REP_integer M)) * (SND(REP_integer N))))))",
((PURE_REWRITE_TAC [TIMES_DEF;PROJ_DEF]) THEN
 NEW_COND_CASES_TAC THEN
 (REWRITE_TAC [thm7a;thm8a])));;

%thm12 = 
|- REP_integer(M times N) =
   ((((FST(REP_integer M)) * (SND(REP_integer N))) +
     ((SND(REP_integer M)) * (FST(REP_integer N)))) <
    (((FST(REP_integer M)) * (FST(REP_integer N))) +
     ((SND(REP_integer M)) * (SND(REP_integer N)))) => 
    ((((FST(REP_integer M)) * (FST(REP_integer N))) +
      ((SND(REP_integer M)) * (SND(REP_integer N)))) -
     (((FST(REP_integer M)) * (SND(REP_integer N))) +
      ((SND(REP_integer M)) * (FST(REP_integer N)))),0) | 
    (0,
     (((FST(REP_integer M)) * (SND(REP_integer N))) +
      ((SND(REP_integer M)) * (FST(REP_integer N)))) -
     (((FST(REP_integer M)) * (FST(REP_integer N))) +
      ((SND(REP_integer M)) * (SND(REP_integer N))))))%


let thm13 = prove("!n.((n<0)=F)",REWRITE_TAC[NOT_LESS_0]);;

%thm13 = |- !n:num. n < 0 = F%


let NUM_MULT_IS_INT_MULT = prove_thm (`NUM_MULT_IS_INT_MULT`,
"!m n. (INT m) times (INT n) = INT (m * n)",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[(SYM thm4);thm12]) THEN
 (SUBST_TAC[(INST [("INT(m*n)","M:integer")] thm6a)]) THEN
 (PURE_ONCE_REWRITE_TAC[INT_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[thm7]) THEN
 (PURE_ONCE_REWRITE_TAC[FST;SND]) THEN
 (PURE_ONCE_REWRITE_TAC (CONJUNCTS(SPEC_ALL(MULT_CLAUSES)))) THEN
 (PURE_ONCE_REWRITE_TAC[(CONJUNCT1(CONJUNCT2(ADD_CLAUSES)))]) THEN
 REFL_TAC));;

%NUM_MULT_IS_INT_MULT = 
 |- !m:num n:num. (INT m) times (INT n) = INT(m * n)%


%Some useful functions for doing arithmetic simplifications%

let first=\thm.(rand(rator(rand(concl(thm)))));;
let second=\thm.(rand(rand(concl(thm)))) ;;

%if term="a+b" then FLIP term  relaces all "a+b"  by "b+a" %

let FLIP=\term.(SUBS[(REWR_CONV ADD_SYM term)]);;


%STRAIGHTEN_OUT replaces 
  |- E=((a1+b1)+(c1+d1))op((a2+b2)+(c2+d2))
 by
  |- E=((a1+c1)+(b1+d1))op((a2+c2)+(b2+d2)) %

let STRAIGHTEN_OUT=
(let str=\term.
(SUBS
[(REWR_CONV
 ((REWR_CONV ADD_ASSOC "(a+b)+(c+d)")and_then
  (SUBS[(REWR_CONV(SYM(SPEC_ALL ADD_ASSOC))"(a+b)+c")])and_then
  (SUBS[(REWR_CONV ADD_SYM "b+c")])and_then
  (SUBS[(REWR_CONV ADD_ASSOC "a+(c+b)")])and_then
  (SUBS[(REWR_CONV(SYM(SPEC_ALL ADD_ASSOC))"((a+c)+b)+d")]))term)])
in
 ((\thm.str(first thm)thm)o(\thm.str(second thm)thm) ));;

%if thm1=|-(term2 <= term1)  thm2=|-(term4 <= term3) then
 we get from fun1
 |- (term1 - term2 < term3 - term4)=(term1 + term4 < term2 + term3)%

let fun1 =\thm1 thm2 term1 term2 term3 term4.(
(MP(SPECL[term1;term2;"^term3-^term4"]SUB_LESS_TO_LESS_ADDL)thm1)
and_then
(SUBS[(MP(SPECL[term2;term3;term4]SIMP1)thm2)])
and_then
(SUBS[(MP(SPECL["^term2+^term3";term1;term4]LESS_SUB_TO_ADDR_LESS)
  (MP(SPECL[term4;term3;term2]ADDL_GREATER_EQ)thm2))]) );;

%if thm1=|-(term2 <= term1)  thm2=|-(term4 <= term3) then
 we get from fun2
 |- (term1 - term2) - (term3 - term4)=(term1 + term4) - (term2 + term3)%

let fun2 =\thm1 thm2 term1 term2 term3 term4.(
(MP(SPECL["^term1-^term2";term4;term3]SIMP3)thm2)
and_then
(SUBS[(MP(SPECL[term1;term4;term2]SIMP2)thm1)])
and_then
(SUBS[(SPECL["^term1+^term4";term2;term3]DOUBLE_SUB)]) );;

%if thm1=|-(term2 <= term1)  thm2=|-(term4 <= term3) then
 we get from fun3
 |- (term1 - term2) + (term3 - term4)=(term1 + term3) - (term2 + term4)%

let fun3 =\thm1 thm2 term1 term2 term3 term4.(
(MP(SPECL["^term1-^term2";term3;term4]SIMP1)thm2)
and_then
(SUBS[(MP(SPECL[term1;term3;term2]SIMP2)thm1)])
and_then
(SUBS[(SPECL["^term1+^term3";term2;term4]DOUBLE_SUB)]) );;


let ASSOC_TIMES = prove_thm (`ASSOC_TIMES`,
"!M N P. M times (N times P) = (M times N) times P",
(let M1="(FST(REP_integer M))" in
 let M2="(SND(REP_integer M))" in
 let N1="(FST(REP_integer N))" in
 let N2="(SND(REP_integer N))" in
 let P1="(FST(REP_integer P))" in
 let P2="(SND(REP_integer P))" in

 (REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM(thm4))]) THEN
 (PURE_REWRITE_TAC[thm12]) THEN
 (FILTER_COND_CASES_TAC
      "((^M1*^N2)+(^M2*^N1))<((^M1*^N1)+(^M2*^N2))") THEN
 (FILTER_COND_CASES_TAC
      "((^N1*^P2)+(^N2*^P1))<((^N1*^P1)+(^N2*^P2))") THEN
 (PURE_ONCE_REWRITE_TAC[FST]) THEN
 (PURE_ONCE_REWRITE_TAC[SND]) THEN
 (PURE_REWRITE_TAC [(CONJUNCT1(SPEC_ALL MULT_CLAUSES));
   (CONJUNCT1(CONJUNCT2(SPEC_ALL MULT_CLAUSES)));
   (CONJUNCT1 ADD_CLAUSES);(CONJUNCT1(CONJUNCT2 ADD_CLAUSES));
   (CONJUNCT1(SPEC "m:num" SUB_0));(CONJUNCT2(SPEC "m:num" SUB_0))]) THEN
 (PURE_REWRITE_TAC[LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB;LEFT_SUB_DISTRIB;
   RIGHT_SUB_DISTRIB]) THENL(

let rule1=\term.(
 (MP(SPECL["((^N1*^P2)+(^N2*^P1))";"((^N1*^P1)+(^N2*^P2))";term]
 (PURE_ONCE_REWRITE_RULE [MULT_SYM] LESS_MONO_MULT))
 ((ASSUME "((^N1*^P2)+(^N2*^P1))<((^N1*^P1)+(^N2*^P2))") and_then
  (MP(SPECL["((^N1*^P2)+(^N2*^P1))";"((^N1*^P1)+(^N2*^P2))"]
    LESS_IMP_LESS_OR_EQ)))) and_then
 (PURE_ONCE_REWRITE_RULE[LEFT_ADD_DISTRIB]))
in
let NP1=(
(fun1 (rule1 M2) (rule1 M1)
      "((^M2*(^N1*^P1))+(^M2*(^N2*^P2)))"
      "((^M2*(^N1*^P2))+(^M2*(^N2*^P1)))"
      "((^M1*(^N1*^P1))+(^M1*(^N2*^P2)))"
      "((^M1*(^N1*^P2))+(^M1*(^N2*^P1)))" ) and_then
(\thm.FLIP(first thm)thm) and_then
(\thm.FLIP(second thm)thm))
in

let NPrule=\term1 term2.
(fun2 (rule1 term1) (rule1 term2)
      "((^term1*(^N1*^P1))+(^term1*(^N2*^P2)))"
      "((^term1*(^N1*^P2))+(^term1*(^N2*^P1)))"
      "((^term2*(^N1*^P1))+(^term2*(^N2*^P2)))"
      "((^term2*(^N1*^P2))+(^term2*(^N2*^P1)))" )
in
let NP2=(NPrule M1 M2) in
let NP3=((NPrule M2 M1)and_then
  (\thm.FLIP(first thm)thm)and_then(\thm.FLIP(second thm)thm))
in

let rule2=\term.(
 (MP(SPECL["((^M1*^N2)+(^M2*^N1))";"((^M1*^N1)+(^M2*^N2))";term]
     LESS_MONO_MULT)
 ((ASSUME "((^M1*^N2)+(^M2*^N1))<((^M1*^N1)+(^M2*^N2))") and_then
  (MP(SPECL["((^M1*^N2)+(^M2*^N1))";"((^M1*^N1)+(^M2*^N2))"]
   LESS_IMP_LESS_OR_EQ)))) and_then
 (PURE_ONCE_REWRITE_RULE[RIGHT_ADD_DISTRIB]))
in
let MN1=(
(fun1 (rule2 P2) (rule2 P1)
      "(((^M1*^N1)*^P2)+((^M2*^N2)*^P2))"
      "(((^M1*^N2)*^P2)+((^M2*^N1)*^P2))"
      "(((^M1*^N1)*^P1)+((^M2*^N2)*^P1))"
      "(((^M1*^N2)*^P1)+((^M2*^N1)*^P1))" ) and_then
 STRAIGHTEN_OUT and_then
 (\thm.FLIP(rand(first thm))thm)and_then
 (\thm.FLIP(rand(rator(second thm)))thm))
in
let MNrule=\term1 term2.(
(fun2 (rule2 term1) (rule2 term2)
      "(((^M1*^N1)*^term1)+((^M2*^N2)*^term1))"
      "(((^M1*^N2)*^term1)+((^M2*^N1)*^term1))"
      "(((^M1*^N1)*^term2)+((^M2*^N2)*^term2))"
      "(((^M1*^N2)*^term2)+((^M2*^N1)*^term2))" ) and_then
STRAIGHTEN_OUT and_then
(\thm.FLIP (rand(first thm))thm) and_then
(\thm.FLIP (rand(rator(second thm)))thm))
in
let MN2=(MNrule P1 P2) in
let MN3=(MNrule P2 P1) in

let rule3=\term.(
 (MP(SPECL["((^N1*^P1)+(^N2*^P2))";"((^N1*^P2)+(^N2*^P1))";term]
 (PURE_ONCE_REWRITE_RULE [MULT_SYM] LESS_MONO_MULT))
 ((ASSUME "~((^N1*^P2)+(^N2*^P1))<((^N1*^P1)+(^N2*^P2))") and_then
  (PURE_ONCE_REWRITE_RULE[NOT_LESS]))) and_then
 (PURE_ONCE_REWRITE_RULE[LEFT_ADD_DISTRIB]))
in
let NOT_NP1=
(fun1 (rule3 M1) (rule3 M2)
      "((^M1*(^N1*^P2))+(^M1*(^N2*^P1)))"
      "((^M1*(^N1*^P1))+(^M1*(^N2*^P2)))"
      "((^M2*(^N1*^P2))+(^M2*(^N2*^P1)))"
      "((^M2*(^N1*^P1))+(^M2*(^N2*^P2)))" )
in
let NOT_NPrule=\term1 term2.
(fun2 (rule3 term1) (rule3 term2)
      "((^term1*(^N1*^P2))+(^term1*(^N2*^P1)))"
      "((^term1*(^N1*^P1))+(^term1*(^N2*^P2)))"
      "((^term2*(^N1*^P2))+(^term2*(^N2*^P1)))"
      "((^term2*(^N1*^P1))+(^term2*(^N2*^P2)))" )
in
let NOT_NP2=((NOT_NPrule M2 M1)and_then
  (\thm.FLIP(first thm)thm)and_then(\thm.FLIP(second thm)thm))
in
let NOT_NP3=(NOT_NPrule M1 M2) in

let rule4=\term.(
 (MP(SPECL["((^M1*^N1)+(^M2*^N2))";"((^M1*^N2)+(^M2*^N1))";term]
  LESS_MONO_MULT)
 ((ASSUME "~((^M1*^N2)+(^M2*^N1))<((^M1*^N1)+(^M2*^N2))") and_then
  (PURE_ONCE_REWRITE_RULE[NOT_LESS]))) and_then
 (PURE_ONCE_REWRITE_RULE[RIGHT_ADD_DISTRIB]))
in
let NOT_MN1=(
(fun1 (rule4 P1) (rule4 P2)
      "(((^M1*^N2)*^P1)+((^M2*^N1)*^P1))"
      "(((^M1*^N1)*^P1)+((^M2*^N2)*^P1))"
      "(((^M1*^N2)*^P2)+((^M2*^N1)*^P2))"
      "(((^M1*^N1)*^P2)+((^M2*^N2)*^P2))" ) and_then 
 STRAIGHTEN_OUT and_then
 (\thm.FLIP(rand(rator(first thm)))thm)and_then
 (\thm.FLIP(rand(second thm))thm))
in
let NOT_MNrule=\term1 term2.(
(fun2 (rule4 term1) (rule4 term2)
      "(((^M1*^N2)*^term1)+((^M2*^N1)*^term1))"
      "(((^M1*^N1)*^term1)+((^M2*^N2)*^term1))"
      "(((^M1*^N2)*^term2)+((^M2*^N1)*^term2))"
      "(((^M1*^N1)*^term2)+((^M2*^N2)*^term2))" ) and_then
STRAIGHTEN_OUT and_then
(\thm.FLIP (rand(rator(first thm)))thm) and_then
(\thm.FLIP (rand(second thm))thm))
in
let NOT_MN2=(NOT_MNrule P2 P1) in
let NOT_MN3=(NOT_MNrule P1 P2) in

[(SUBST_TAC[MN1;MN2;MN3;NP2;NP1;NP3]);
(SUBST_TAC[MN1;MN2;MN3;NOT_NP2;NOT_NP1;NOT_NP3]);
(SUBST_TAC[NOT_MN1;NOT_MN2;NOT_MN3;NP2;NP1;NP3]);
(SUBST_TAC[NOT_MN1;NOT_MN2;NOT_MN3;NOT_NP2;NOT_NP1;NOT_NP3])] )THEN
REWRITE_TAC[MULT_ASSOC] ));;

%ASSOC_TIMES = 
 |- !M:integer N:integer P:integer.
     M times (N times P) = (M times N) times P%


let COMM_TIMES = prove_thm (`COMM_TIMES`,
"!M N. M times N =N times M",
(let M1="FST(REP_integer M)" in
 let M2="SND(REP_integer M)" in
 let N1="FST(REP_integer N)" in
 let N2="SND(REP_integer N)" in
 (REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[(SYM(thm4));thm12]) THEN
 (SUBST_TAC [(SPECL[N1;M1]MULT_SYM);(SPECL[N2;M2]MULT_SYM);
             (SPECL[N1;M2]MULT_SYM);(SPECL[N2;M1]MULT_SYM)]) THEN
 (SUBST_TAC [(SPECL["^M2*^N1";"^M1*^N2"]ADD_SYM)]) THEN
 REFL_TAC));;

%COMM_TIMES = |- !M:integer N:integer. M times N = N times M%


let TIMES_IDENTITY=prove_thm(`TIMES_IDENTITY`,
"!M:integer.(M times (INT 1)=M)/\((INT 1) times M =M)",
(GEN_TAC THEN
 (PURE_REWRITE_TAC[(SYM thm4);thm12]) THEN
 (PURE_REWRITE_TAC[INT_DEF;thm7]) THEN
 (PURE_ONCE_REWRITE_TAC[FST;SND]) THEN
 (PURE_REWRITE_TAC (CONJUNCTS(SPEC_ALL(MULT_CLAUSES)))) THEN
 (REWRITE_TAC (CONJUNCTS(SPEC_ALL(ADD_CLAUSES)))) THEN
 (ACCEPT_TAC(SYM thm6a))));;

%TIMES_IDENTITY = 
 |- !M:integer. (M times (INT 1) = M) /\ ((INT 1) times M = M)%


let RIGHT_PLUS_DISTRIB=prove_thm(`RIGHT_PLUS_DISTRIB`,
"!M N P.(M plus N) times P = (M times P) plus (N times P)",
(let M1="(FST(REP_integer M))" in
 let M2="(SND(REP_integer M))" in
 let N1="(FST(REP_integer N))" in
 let N2="(SND(REP_integer N))" in
 let P1="(FST(REP_integer P))" in
 let P2="(SND(REP_integer P))" in

 (REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM(thm4))]) THEN
 (PURE_REWRITE_TAC[thm12;thm9]) THEN
 (FILTER_COND_CASES_TAC "(^M2 + ^N2) < (^M1 + ^N1)") THEN
 (FILTER_COND_CASES_TAC
    "((^M1 * ^P2) + (^M2 * ^P1)) < ((^M1 * ^P1) + (^M2 * ^P2))") THEN
 (FILTER_COND_CASES_TAC
    "((^N1 * ^P2) + (^N2 * ^P1)) < ((^N1 * ^P1) + (^N2 * ^P2))") THEN
 (PURE_ONCE_REWRITE_TAC[FST;SND]) THEN
 (PURE_REWRITE_TAC [(CONJUNCT1(SPEC_ALL MULT_CLAUSES));
   (CONJUNCT1(CONJUNCT2(SPEC_ALL MULT_CLAUSES)));
   (CONJUNCT1 ADD_CLAUSES);(CONJUNCT1(CONJUNCT2 ADD_CLAUSES));
   (CONJUNCT1(SPEC "m:num" SUB_0));(CONJUNCT2(SPEC "m:num" SUB_0))]) THEN
 (PURE_ONCE_REWRITE_TAC[RIGHT_SUB_DISTRIB]) THENL(

 let ruleR=\term1 term2 term3 .(
 (ASSUME "^term1<^term2") and_then
 (MP(SPECL[term1;term2]LESS_IMP_LESS_OR_EQ)) and_then
 (MP(SPECL[term1;term2;term3]LESS_MONO_MULT)) )
 in

 let NOTruleR=\term1 term2 term3 .(
 (ASSUME "~^term1<^term2") and_then
 (PURE_ONCE_REWRITE_RULE [NOT_LESS]) and_then
 (MP(SPECL[term2;term1;term3]LESS_MONO_MULT)) )
 in

let MN1=(
(fun1 (ruleR "^M2+^N2" "^M1+^N1" P2) (ruleR "^M2+^N2" "^M1+^N1" P1)
"(^M1+^N1)*^P2" "(^M2+^N2)*^P2" "(^M1+^N1)*^P1" "(^M2+^N2)*^P1" )and_then
(\thm.(FLIP(second thm)thm)) and_then
(\thm.(SUBS[(DEPTH_CONV(REWR_CONV RIGHT_ADD_DISTRIB)
             (rand(concl thm)))]thm))and_then
STRAIGHTEN_OUT)
in
let MNrule=\term1 term2.(
(fun2 (ruleR "^M2+^N2" "^M1+^N1" term1) (ruleR "^M2+^N2" "^M1+^N1" term2)
"(^M1+^N1)*^term1" "(^M2+^N2)*^term1" "(^M1+^N1)*^term2" "(^M2+^N2)*^term2" )
and_then
(\thm.(FLIP(second thm)thm)) and_then
(\thm.(SUBS[(DEPTH_CONV(REWR_CONV RIGHT_ADD_DISTRIB)
             (rand(concl thm)))]thm))and_then
STRAIGHTEN_OUT)
in
let MN2=(MNrule P1 P2) in
let MN3=(MNrule P2 P1) in

let NOTMN1=(
(fun1 (NOTruleR "^M2+^N2" "^M1+^N1" P1) (NOTruleR "^M2+^N2" "^M1+^N1" P2)
"(^M2+^N2)*^P1" "(^M1+^N1)*^P1" "(^M2+^N2)*^P2" "(^M1+^N1)*^P2" )and_then
(\thm.(FLIP(first thm)thm)) and_then
(\thm.(SUBS[(DEPTH_CONV(REWR_CONV RIGHT_ADD_DISTRIB)
             (rand(concl thm)))]thm))and_then
STRAIGHTEN_OUT)
in
let NOTMNrule=\term1 term2.(
(fun2 (NOTruleR "^M2+^N2" "^M1+^N1" term2)
      (NOTruleR "^M2+^N2" "^M1+^N1" term1)
"(^M2+^N2)*^term2" "(^M1+^N1)*^term2" "(^M2+^N2)*^term1" "(^M1+^N1)*^term1" )
and_then
(\thm.(FLIP(first thm)thm)) and_then
(\thm.(SUBS[(DEPTH_CONV(REWR_CONV RIGHT_ADD_DISTRIB)
             (rand(concl thm)))]thm))and_then
STRAIGHTEN_OUT)
in
let NOTMN2=(NOTMNrule P1 P2) in
let NOTMN3=(NOTMNrule P2 P1) in

let LtoLE=\term1 term2.(
 (ASSUME "^term1<^term2") and_then
 (MP(SPECL[term1;term2]LESS_IMP_LESS_OR_EQ)) )
in
let NOTLtoLE=\term1 term2.(
 (ASSUME "~(^term1<^term2)") and_then
 (PURE_ONCE_REWRITE_RULE[NOT_LESS]) )
in

let MP_NP1=(
(DEPTH_CONV
(REWR_CONV
(fun3 (LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P1)+(^M2*^P2))" "((^M1*^P2)+(^M2*^P1))"
      "((^N1*^P1)+(^N2*^P2))" "((^N1*^P2)+(^N2*^P1))" ))
"0<((((^M1*^P1)+(^M2*^P2))-((^M1*^P2)+(^M2*^P1)))+
    (((^N1*^P1)+(^N2*^P2))-((^N1*^P2)+(^N2*^P1))))" )and_then
(SUBS[(MP
 (PURE_ONCE_REWRITE_RULE[CONJUNCT1(ADD_CLAUSES)]
  (SPECL["((^M1*^P1)+(^M2*^P2))+((^N1*^P1)+(^N2*^P2))";"0";
         "((^M1*^P2)+(^M2*^P1))+((^N1*^P2)+(^N2*^P1))"]LESS_SUB_TO_ADDR_LESS))
 (MP
  (SPECL["((^M1*^P2)+(^M2*^P1))";"((^N1*^P2)+(^N2*^P1))";
         "((^M1*^P1)+(^M2*^P2))";"((^N1*^P1)+(^N2*^P2))"]LESS_EQ_LESS_EQ_MONO)
  (CONJ(LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
       (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")) ) )]))
in
let MP_NP2=
(fun3 (LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P1)+(^M2*^P2))" "((^M1*^P2)+(^M2*^P1))"
      "((^N1*^P1)+(^N2*^P2))" "((^N1*^P2)+(^N2*^P1))" )
in
let MN_MP_NP=(
SUBS[ 
(PURE_REWRITE_RULE[(SYM(SPEC_ALL SUB_EQ_0))]
 (MP
  (SPECL["((^M1*^P2)+(^M2*^P1))";"((^N1*^P2)+(^N2*^P1))";
         "((^M1*^P1)+(^M2*^P2))";"((^N1*^P1)+(^N2*^P2))"]LESS_EQ_LESS_EQ_MONO)
  (CONJ(LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
       (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")) ) )]MN3)
in

let MP_NOTNP1=(
(fun1 (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      (LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))"
      "((^M1*^P1)+(^M2*^P2))" "((^M1*^P2)+(^M2*^P1))") and_then
((\thm.(FLIP(first thm)thm))o(\thm.(FLIP(second thm)thm))) )
in
let MP_NOTNP2=
(fun2 (LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P1)+(^M2*^P2))" "((^M1*^P2)+(^M2*^P1))"
      "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))" )
in
let MP_NOTNP3=(
(fun2 (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      (LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))" 
      "((^M1*^P1)+(^M2*^P2))" "((^M1*^P2)+(^M2*^P1))" ) and_then
((\thm.(FLIP(first thm)thm))o(\thm.(FLIP(second thm)thm))) )
in

let NOTMP_NP1=
(fun1 (NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))" 
      "((^N1*^P1)+(^N2*^P2))" "((^N1*^P2)+(^N2*^P1))" )
in
let NOTMP_NP2=(
(fun2 (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      (NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      "((^N1*^P1)+(^N2*^P2))" "((^N1*^P2)+(^N2*^P1))"
      "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))" ) and_then
((\thm.(FLIP(first thm)thm))o(\thm.(FLIP(second thm)thm))) )
in
let NOTMP_NP3=
(fun2 (NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
      (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))"
      "((^N1*^P1)+(^N2*^P2))" "((^N1*^P2)+(^N2*^P1))" )
in

let NOTMP_NOTNP=
(fun3(NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
     (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")
      "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))"
      "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))" )
in
let MN_NOTMP_NOTNP=(
SUBS[
((PURE_ONCE_REWRITE_RULE[(SYM(SPEC_ALL NOT_LESS))]
  (MP
   (SPECL["((^M1*^P1)+(^M2*^P2))";"((^N1*^P1)+(^N2*^P2))";
          "((^M1*^P2)+(^M2*^P1))";"((^N1*^P2)+(^N2*^P1))"]
         LESS_EQ_LESS_EQ_MONO)
   (CONJ(NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
        (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")) ))and_then
 (\thm.(MP(SPEC(rand(concl(thm)))NOT_F)thm)))]MN1 )
in

let NOTMN_MP_NP=(
SUBS[ 
(PURE_REWRITE_RULE[(SYM(SPEC_ALL SUB_EQ_0))]
 (MP
  (SPECL["((^M1*^P2)+(^M2*^P1))";"((^N1*^P2)+(^N2*^P1))";
         "((^M1*^P1)+(^M2*^P2))";"((^N1*^P1)+(^N2*^P2))"]LESS_EQ_LESS_EQ_MONO)
  (CONJ(LtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
       (LtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")) ) )]NOTMN3)
in
let NOTMN_NOTMP_NOTNP=(
SUBS[
((PURE_ONCE_REWRITE_RULE[(SYM(SPEC_ALL NOT_LESS))]
  (MP
   (SPECL["((^M1*^P1)+(^M2*^P2))";"((^N1*^P1)+(^N2*^P2))";
          "((^M1*^P2)+(^M2*^P1))";"((^N1*^P2)+(^N2*^P1))"]
         LESS_EQ_LESS_EQ_MONO)
   (CONJ(NOTLtoLE "((^M1*^P2)+(^M2*^P1))" "((^M1*^P1)+(^M2*^P2))")
        (NOTLtoLE "((^N1*^P2)+(^N2*^P1))" "((^N1*^P1)+(^N2*^P2))")) ))and_then
 (\thm.(MP(SPEC(rand(concl(thm)))NOT_F)thm)))]NOTMN1 )
in

[(SUBST_TAC[MN1;MN2;MP_NP1;MP_NP2;MN_MP_NP]);
 (SUBST_TAC[MN1;MN2;MN3;MP_NOTNP1;MP_NOTNP2;MP_NOTNP3]);
 (SUBST_TAC[MN1;MN2;MN3;NOTMP_NP1;NOTMP_NP2;NOTMP_NP3]);
 ((REWRITE_TAC[MN_NOTMP_NOTNP;thm13])THEN(SUBST_TAC[MN3;NOTMP_NOTNP]));
 (SUBST_TAC[NOTMN1;NOTMN2;MP_NP1;MP_NP2;NOTMN_MP_NP]);
 (SUBST_TAC[NOTMN1;NOTMN2;NOTMN3;MP_NOTNP1;MP_NOTNP2;MP_NOTNP3]);
 (SUBST_TAC[NOTMN1;NOTMN2;NOTMN3;NOTMP_NP1;NOTMP_NP2;NOTMP_NP3]);
 ((REWRITE_TAC[NOTMN_NOTMP_NOTNP;thm13])THEN(SUBST_TAC[NOTMN3;NOTMP_NOTNP]))])
THEN REFL_TAC) );;

%RIGHT_PLUS_DISTRIB = 
 |- !M:integer N:integer P:integer.
     (M plus N) times P = (M times P) plus (N times P)%


let LEFT_PLUS_DISTRIB=prove_thm(`LEFT_PLUS_DISTRIB`,
"!M N P.M times (N plus P) = (M times N) plus (M times P)",
((REPEAT GEN_TAC)
 THEN
 (SUBST_TAC
  [(SPECL["N:integer";"P:integer"]COMM_PLUS);
   (SPECL["M times N";"M times P"]COMM_PLUS)])
 THEN
 (SUBST_TAC
  [(SPECL["M:integer";"P plus N"]COMM_TIMES);
   (SPECL["M:integer";"P:integer"]COMM_TIMES);
   (SPECL["M:integer";"N:integer"]COMM_TIMES)])
 THEN
 (REWRITE_TAC[RIGHT_PLUS_DISTRIB]) ));;

%LEFT_PLUS_DISTRIB = 
 |- !M:integer N:integer P:integer.
     M times (N plus P) = (M times N) plus (M times P)%


let TIMES_ZERO = prove_thm(`TIMES_ZERO`,
"!M. (M times (INT 0) = INT 0) /\ ((INT 0) times M = INT 0)",
(GEN_TAC THEN (ASM_CONJ2_TAC THENL
  [((PURE_ONCE_REWRITE_TAC[COMM_TIMES]) THEN (FIRST_ASSUM ACCEPT_TAC));
   ALL_TAC]) THEN
 (MP_IMP_TAC (SPECL["(INT 0) times M";"(INT 0) times M";"INT 0"]
   PLUS_RIGHT_CANCELLATION)) THEN
 (REWRITE_TAC[(SPEC_ALL (CONJUNCT1 PLUS_ID_LEMMA));
   (SYM (SPEC_ALL RIGHT_PLUS_DISTRIB))])));;

%TIMES_ZERO = 
|- !M. (M times (INT 0) = INT 0) /\ ((INT 0) times M = INT 0) %


let TIMES_neg = prove_thm(`TIMES_neg`,
"(!M N. (M times (neg N) = neg (M times N))) /\
 (!M N. ((neg M) times N = neg (M times N)))",
(ASM_CONJ1_TAC THENL
 [(GEN_TAC THEN
   (MATCH_MP_IMP_TAC (SPEC_ALL (SPEC "M times N" PLUS_RIGHT_CANCELLATION)))THEN
   (REWRITE_TAC[(SYM (SPEC_ALL LEFT_PLUS_DISTRIB));
     (CONJUNCT1 (SPEC_ALL PLUS_INV_LEMMA));
     (CONJUNCT1 (SPEC_ALL TIMES_ZERO))]));
  ((PURE_ONCE_REWRITE_TAC[COMM_TIMES]) THEN (ASM_REWRITE_TAC[]))]));;

%TIMES_neg = 
|- (!M N. M times (neg N) = neg(M times N)) /\
   (!M N. (neg M) times N = neg(M times N)) %


let neg_IS_TIMES_neg1 = prove_thm(`neg_IS_TIMES_neg1`,
"!M. neg M = M times (neg (INT 1))",
(STRIP_TAC THEN (ASM_REWRITE_TAC [TIMES_neg;TIMES_IDENTITY])));;

% neg_IS_TIMES_neg1 = |- !M. neg M = M times (neg(INT 1)) %


%The order structure on the integers%

let POS_DEF=new_definition (`POS_DEF`,
 "!M. POS M = (?n:num.M=INT(SUC n))");;

%POS_DEF = |- POS M = (?n:num. M = INT(SUC n))%


let NEG_DEF=new_definition (`NEG_DEF`,
 "!M. NEG M = POS(neg M)");;

%NEG_DEF = |- NEG M = POS(neg M)%


let TRICHOTOMY = prove_thm (`TRICHOTOMY`,
"!M.((POS M)\/(NEG M)\/(M=INT 0))
    /\~((POS M)/\(NEG M))
    /\~((POS M)/\(M=INT 0))
    /\~((NEG M)/\(M=INT 0))",
(
let part1 = prove("((POS M)\/(NEG M)\/(M=INT 0))",
((PURE_REWRITE_TAC [INT_DEF; POS_DEF; NEG_DEF]) THEN
 (ASM_CASES_TAC "((REP_integer M)=(0,0))") THENL
 [((DISJ2_TAC THEN DISJ2_TAC) THEN 
   (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
   (SUBST_TAC[(INST[("0","n:num")]thm7)]) THEN
   (FIRST_ASSUM ACCEPT_TAC) );
  ((DISJ_CASES_TAC thm6) THENL
  [(DISJ1_TAC THEN
    (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
    (PURE_ONCE_REWRITE_TAC[thm7]) THEN
    (EXISTS_TAC "(@n:num.(@p:num.REP_integer M = p,0)=SUC n)") THEN
    (let st1=((ASSUME "?p:num. REP_integer M = p,0")and_then SELECT_RULE) in

%st1 = . |- REP_integer M = (@p. REP_integer M = p,0),0%

     let st2=(
     (PURE_ONCE_REWRITE_RULE
      [(ASSUME "FST(REP_integer M)=0");
       (PURE_ONCE_REWRITE_RULE [SND](AP_TERM "SND:num#num->num" st1))]
      (SYM(AUTO_SPEC "REP_integer M" PAIR))) and_then
     (FALSITY_INTRO (ASSUME "~(REP_integer M = 0,0)")) and_then
     (NEG_DISCH "FST(REP_integer M)=0") and_then
     (PURE_ONCE_REWRITE_RULE
      [(PURE_ONCE_REWRITE_RULE [FST](AP_TERM "FST:num#num->num" st1))])
     and_then
     (MP(DISJ_IMP(SPEC "(@p:num. REP_integer M = p,0)" num_CASES)))and_then
     SELECT_RULE) in

%st2 = 
.. |- (@p. REP_integer M = p,0) =
      SUC(@n. (@p. REP_integer M = p,0) = SUC n)
hyp st2 =
["?p. REP_integer M = p,0"; "~(REP_integer M = 0,0)"] : term list%

     let st3=(PURE_ONCE_REWRITE_RULE[st2]st1) in

%st3 = .. |- REP_integer M = SUC(@n. (@p. REP_integer M = p,0) = SUC n),0
hyp st3 =
["?p. REP_integer M = p,0"; "~(REP_integer M = 0,0)"] : term list%

     (ACCEPT_TAC st3)));
   ((DISJ2_TAC THEN DISJ1_TAC) THEN
    (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
    (PURE_ONCE_REWRITE_TAC[thm7;thm11]) THEN
    (EXISTS_TAC "(@n':num.(@n:num.REP_integer M = 0,n)=SUC n')") THEN
    (let st1=((ASSUME "?n:num. REP_integer M = 0,n")and_then SELECT_RULE) in
     let st2=(
     (PURE_ONCE_REWRITE_RULE
      [(ASSUME "SND(REP_integer M)=0");
       (PURE_ONCE_REWRITE_RULE [FST](AP_TERM "FST:num#num->num" st1))]
      (SYM(AUTO_SPEC "REP_integer M" PAIR))) and_then
     (FALSITY_INTRO (ASSUME "~(REP_integer M = 0,0)")) and_then
     (NEG_DISCH "SND(REP_integer M)=0") and_then
     (PURE_ONCE_REWRITE_RULE
      [(PURE_ONCE_REWRITE_RULE [SND](AP_TERM "SND:num#num->num" st1))])
     and_then
     (MP(DISJ_IMP(SPEC "(@n:num. REP_integer M = 0,n)" num_CASES)))and_then
     SELECT_RULE) in
     let st3=(PURE_ONCE_REWRITE_RULE[st2]st1) in
     (REWRITE_TAC
      [(PURE_ONCE_REWRITE_RULE[FST](AP_TERM "FST:num#num->num" st3));
       (PURE_ONCE_REWRITE_RULE[SND](AP_TERM "SND:num#num->num" st3))])
       ))])])) in

%part1 = |- !M:integer. POS M \/ NEG M \/ (M = INT 0)%

let part2 = prove("~((POS M)/\(NEG M))",
((PURE_REWRITE_TAC [INT_DEF; POS_DEF; NEG_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
 (PURE_ONCE_REWRITE_TAC[thm7;thm11]) THEN
(let st1=ASSUME "(?n:num. REP_integer M = SUC n,0)/\
          (?n:num. SND(REP_integer M),FST(REP_integer M) = SUC n,0)" in
 let st2=
 (SELECT_RULE(CONJUNCT1 st1))and_then
 (\thm.(PURE_ONCE_REWRITE_RULE
       [(PURE_ONCE_REWRITE_RULE[FST](AP_TERM "FST:num#num->num" thm));
        (PURE_ONCE_REWRITE_RULE[SND](AP_TERM "SND:num#num->num" thm))]
       (CONJUNCT2 st1))) and_then
 SELECT_RULE and_then
 (\thm.(PURE_ONCE_REWRITE_RULE[SND](AP_TERM "SND:num#num->num" thm)))
 and_then
 (FALSITY_INTRO (SPEC "@n':num. REP_integer M = SUC n',0" NOT_SUC))
 and_then
 (\thm.(NEG_DISCH (hd(hyp thm)) thm)) 
 in
 (ACCEPT_TAC st2)))) in

%part2 = |- ~(POS M /\ NEG M)%

let part3 = prove("~((POS M)/\(M=INT 0))",
((PURE_REWRITE_TAC [INT_DEF; POS_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
 (PURE_ONCE_REWRITE_TAC[thm7]) THEN
(let st1=ASSUME "((?n:num. REP_integer M = SUC n,0) /\ 
                  (REP_integer M = 0,0))" in
 let st2=
 (SELECT_RULE(CONJUNCT1 st1))and_then
 (\thm.(PURE_ONCE_REWRITE_RULE
       [(PURE_ONCE_REWRITE_RULE[FST](AP_TERM "FST:num#num->num" thm))]
       (PURE_ONCE_REWRITE_RULE[FST]
        (AP_TERM "FST:num#num->num" (CONJUNCT2 st1))))) and_then
 (FALSITY_INTRO (SPEC "@n:num. REP_integer M = SUC n,0" NOT_SUC))
 and_then
 (\thm.(NEG_DISCH (hd(hyp thm)) thm)) 
 in
 (ACCEPT_TAC st2)))) in

%part3 = |- ~(POS M /\ (M = INT 0))%

let part4 = prove("~((NEG M)/\(M=INT 0))",
((PURE_REWRITE_TAC [INT_DEF; POS_DEF; NEG_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM thm4)]) THEN
 (PURE_ONCE_REWRITE_TAC[thm7;thm11]) THEN
(let st1=ASSUME "(?n:num. SND(REP_integer M),FST(REP_integer M) = SUC n,0)
                 /\(REP_integer M = 0,0)" in
 let st2=
 (SELECT_RULE(CONJUNCT1 st1)) and_then
 (\thm.(PURE_ONCE_REWRITE_RULE
       [(PURE_ONCE_REWRITE_RULE[FST](AP_TERM "FST:num#num->num" thm))]
        (PURE_ONCE_REWRITE_RULE[SND]
        (AP_TERM "SND:num#num->num" (CONJUNCT2 st1)))  )) and_then
 (FALSITY_INTRO
  (SPEC "@n:num. SND(REP_integer M),FST(REP_integer M) = SUC n,0" NOT_SUC))
 and_then
 (\thm.(NEG_DISCH (hd(hyp thm)) thm)) 
 in
 (ACCEPT_TAC st2)))) in

%part4 = |- ~(NEG M /\ (M = INT 0))%

GEN_TAC THEN
(REPEAT CONJ_TAC) THENL
[(ACCEPT_TAC part1);(ACCEPT_TAC part2);
 (ACCEPT_TAC part3);(ACCEPT_TAC part4)]));;

%TRICHOTOMY = 
 |- !M:integer.
     (POS M \/ NEG M \/ (M = INT 0)) /\
     ~(POS M /\ NEG M) /\
     ~(POS M /\ (M = INT 0)) /\
     ~(NEG M /\ (M = INT 0))             %


let NON_NEG_INT_IS_NUM = prove_thm(`NON_NEG_INT_IS_NUM`,
"!N.(~(NEG N)) = (?n. N=(INT n))",
(GEN_TAC THEN
 EQ_TAC THEN
 DISCH_TAC THENL
 [((DISJ_CASES_TAC
    ((REWRITE_RULE[(ASSUME "~ NEG N")](CONJUNCT1(SPEC "N:integer" TRICHOTOMY)))
     and_then
     (\thm.(SUBS[(REWR_CONV POS_DEF (fst(dest_disj(concl thm))))]thm)) ))
   THENL
   [((EXISTS_TAC "SUC(@n.N = (INT(SUC n)))") THEN
     (ASSUM_LIST (ACCEPT_TAC o SELECT_RULE o hd)));
    ((EXISTS_TAC "0") THEN
     (FIRST_ASSUM ACCEPT_TAC))]); 
  ((DISJ_CASES_TAC (SPEC "@n.N=INT n" num_CASES)) THENL
   [(ASSUM_LIST(ACCEPT_TAC o
    (\thml.(let thm=(SUBS[(hd thml)](SELECT_RULE((hd o tl)thml))) in
      (REWRITE_RULE[thm]
       (CONJUNCT2(CONJUNCT2(CONJUNCT2 (SPEC "N:integer" TRICHOTOMY)))))and_then
      (SUBS[(SYM thm)])) ) ));
    (ASSUM_LIST(ACCEPT_TAC o
    (\thml.(
      (SUBS[(SELECT_RULE(hd thml))](SELECT_RULE((hd o tl)thml)))and_then
      (EXISTS ("?n.N=INT(SUC n)","(@n.(@n'.N=INT n')=SUC n)"))and_then
      (PURE_ONCE_REWRITE_RULE [(SYM (SPEC_ALL POS_DEF))]) and_then
      (\thm.REWRITE_RULE[thm](CONJUNCT1(CONJUNCT2
       (SPEC "N:integer" TRICHOTOMY))))
    ) ) ))])]));;

%NON_NEG_INT_IS_NUM = |- !N. ~NEG N = (?n. N = INT n)%


let INT_CASES = prove_thm (`INT_CASES`,
"!P.(!m. P(INT m)) /\ (!m. P(neg (INT m))) ==> (!M. P M)",
((REPEAT STRIP_TAC) THEN (ASM_CASES_TAC "NEG M") THENL
 [((POP_ASSUM \thm.(STRIP_ASSUME_TAC (REWRITE_RULE[NEG_DEF;POS_DEF]thm))) THEN
   (POP_ASSUM \thm.(ASSUME_TAC (REWRITE_RULE[PLUS_INV_INV_LEMMA]
    (AP_TERM "neg" thm)))) THEN
   (ASM_REWRITE_TAC[]));
  ((POP_ASSUM \thm. (STRIP_ASSUME_TAC
    (REWRITE_RULE [NON_NEG_INT_IS_NUM] thm))) THEN
   (ASM_REWRITE_TAC[]))]));;

% INT_CASES = |- !P. (!m. P(INT m)) /\ (!m. P(neg(INT m))) ==> (!M. P M) %


let BELOW_DEF=new_infix_definition (`BELOW_DEF`,
 "below M N = POS(N minus M)");;

%BELOW_DEF = |- !M N. M below N = POS(N minus M)%


let NUM_LESS_IS_INT_BELOW = prove_thm (`NUM_LESS_IS_INT_BELOW`,
"!m n. (m < n) = ((INT m) below (INT n))",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[INT_DEF;BELOW_DEF;POS_DEF;MINUS_DEF]) THEN
 (PURE_REWRITE_TAC[(SYM thm4);thm9;thm11;thm7]) THEN
 (PURE_REWRITE_TAC[FST;SND]) THEN
 (PURE_ONCE_REWRITE_TAC
  [(CONJUNCT1 ADD_CLAUSES);(CONJUNCT1(CONJUNCT2 ADD_CLAUSES))]) THEN
 NEW_COND_CASES_TAC THEN
 (ASM_REWRITE_TAC[]) THENL
[((EXISTS_TAC "@n'. n-m = SUC n'") THEN 
(let st1=
 (SUBS[(SYM(SPECL["n:num";"m:num"]SUB_EQ_0))]
  (SPECL["m:num";"n:num"]NOT_LESS)) and_then
 (\thm.REWRITE_RULE[NOT_CLAUSES](AP_TERM (rand(rator(concl(NOT_DEF))))thm))
 and_then
 (\thm.PURE_ONCE_REWRITE_RULE[thm](ASSUME "m<n")) and_then
 (MP(DISJ_IMP(SPEC "n-m" num_CASES))) and_then
 SELECT_RULE in
 (SUBST_TAC[(SYM st1)]))THEN
REFL_TAC);
(let st1=
 (ASSUME "(?n':num. 0,m - n = SUC n',0)")and_then
 SELECT_RULE and_then
 (\thm.SYM(PURE_ONCE_REWRITE_RULE[FST](AP_TERM "FST:num#num->num" thm)))
 and_then
 (FALSITY_INTRO (SPEC "@n':num. 0,m - n = SUC n',0" NOT_SUC)) and_then
 (\thm.(NEG_DISCH (hd(hyp thm)) thm)) in
 (ACCEPT_TAC st1))]));;

%NUM_LESS_IS_INT_BELOW = |- !m:num n:num. m < n = (INT m) below (INT n)%

let ANTISYM = prove_thm(`ANTISYM`, "!M.~(M below M)",
(GEN_TAC THEN
 (PURE_ONCE_REWRITE_TAC[BELOW_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[MINUS_DEF]) THEN
 (SUBST1_TAC (CONJUNCT2 (SPEC "M:integer" PLUS_INV_LEMMA))) THEN
 (ACCEPT_TAC(REWRITE_RULE[]
  (CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC "INT 0" TRICHOTOMY))))))));;

%ANTISYM = |- !M:integer. ~M below M%

let TRANSIT = prove_thm(`TRANSIT`,
"!M N P. ((M below N) /\ (N below P)) ==> (M below P)",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[BELOW_DEF;MINUS_DEF;POS_DEF]) THEN
 STRIP_TAC THEN
 (EXISTS_TAC "n' + SUC n") THEN
 (PURE_ONCE_REWRITE_TAC[(SYM(SPEC_ALL(CONJUNCT2 ADD)))]) THEN
 (POP_ASSUM_LIST
  (\thl. (itlist $THEN (map (\thm .(ASSUME_TAC (SYM thm))) thl) ALL_TAC))) THEN
 (ASM_REWRITE_TAC[(SYM(SPECL ["SUC n'";"SUC n"] NUM_ADD_IS_INT_ADD))]) THEN
 (PURE_ONCE_REWRITE_TAC [ASSOC_PLUS]) THEN
 (SUBST1_TAC(SYM(SPECL["P:integer";"neg N";"N:integer"]ASSOC_PLUS))) THEN
 (SUBST1_TAC(CONJUNCT1(SPEC "N:integer" PLUS_INV_LEMMA))) THEN
 (SUBST1_TAC(SPEC "P:integer" (CONJUNCT1(CONJUNCT2(PLUS_ID_LEMMA))))) THEN
 REFL_TAC));;

%TRANSIT = 
 |- !M:integer N:integer P:integer. M below N /\ N below P ==> M below P%


let COMPAR = prove_thm(`COMPAR`,
"!M N.(M below N)\/(N below M)\/(M=N)",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC[BELOW_DEF;MINUS_DEF]) THEN
 (NEW_SUBST1_TAC (SYM (SPEC "M plus (neg N)" PLUS_INV_INV_LEMMA))) THEN
 (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL NEG_DEF))]) THEN
 (PURE_REWRITE_TAC
   [(SYM (SPEC_ALL PLUS_DIST_INV_LEMMA));PLUS_INV_INV_LEMMA]) THEN
 (DISJ_CASES_TAC (CONJUNCT1 (SPEC "N plus (neg M)" TRICHOTOMY))) THENL
  [ALL_TAC;(POP_ASSUM DISJ_CASES_TAC)] THEN
 (ASM_REWRITE_TAC []) THEN
 (DISJ2_TAC THEN DISJ2_TAC THEN
 (ACCEPT_TAC (SYM (UNDISCH (PURE_ONCE_REWRITE_RULE [PLUS_INV_INV_LEMMA]
   (SPECL ["neg M";"N:integer"] PLUS_UNIQUE_INV))))))));;


%COMPAR = |- !M:integer N:integer. M below N \/ N below M \/ (M = N)%


let DOUBLE_INF = prove_thm(`DOUBLE_INF`,
"!M.(?N.N below M)/\(?P.M below P)",
(GEN_TAC THEN
 (PURE_REWRITE_TAC[BELOW_DEF;MINUS_DEF;POS_DEF]) THEN
 CONJ_TAC THENL
 [((EXISTS_TAC "M plus (neg(INT 1))") THEN
   (PURE_REWRITE_TAC[neg_PLUS_DISTRIB;ASSOC_PLUS;PLUS_INV_INV_LEMMA;
     (CONJUNCT2(SPEC_ALL PLUS_INV_LEMMA));
     (SPEC_ALL (CONJUNCT1 PLUS_ID_LEMMA))]) THEN
   (EXISTS_TAC "0") THEN
   AP_TERM_TAC THEN
   (ACCEPT_TAC(PURE_ONCE_REWRITE_RULE[(CONJUNCT1 ADD_CLAUSES)]
                (SYM(SPEC "0" ADD1)))));
  ((EXISTS_TAC "(INT 1)plus M") THEN
   (PURE_REWRITE_TAC[(SYM(SPEC_ALL ASSOC_PLUS));
     (CONJUNCT2(SPEC_ALL PLUS_INV_LEMMA));
     (SPEC_ALL (CONJUNCT1 (CONJUNCT2 PLUS_ID_LEMMA)))]) THEN
   (EXISTS_TAC "0") THEN
   AP_TERM_TAC THEN
   (ACCEPT_TAC(PURE_ONCE_REWRITE_RULE[(CONJUNCT1 ADD_CLAUSES)]
                (SYM(SPEC "0" ADD1)))))]));;

%DOUBLE_INF = 
 |- !M:integer. (?N:integer. N below M) /\ (?P:integer. M below P)%


let PLUS_BELOW_TRANSL = prove_thm (`PLUS_BELOW_TRANSL`,
"!M N P .((M below N) = ((M plus P) below (N plus P)))",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC [BELOW_DEF; MINUS_DEF; POS_DEF]) THEN
 (NEW_SUBST1_TAC (SYM
   (SPECL ["P:integer";"M:integer"] PLUS_DIST_INV_LEMMA))) THEN
 (PURE_ONCE_REWRITE_TAC [PLUS_GROUP_ASSOC]) THEN
 (NEW_SUBST1_TAC (SPECL ["P:integer";"neg P";"neg M"] ASSOC_PLUS)) THEN
 (REWRITE_TAC [PLUS_INV_LEMMA;PLUS_ID_LEMMA])));;

%PLUS_BELOW_TRANSL =
 |- !M:integer N:integer P:integer. M below N = (M plus P) below (N plus P)%


let neg_REV_BELOW = prove_thm(`neg_REV_BELOW`,
"!M N. (neg M) below (neg N) = N below M",
((REPEAT GEN_TAC) THEN
 (PURE_REWRITE_TAC [BELOW_DEF; POS_DEF; MINUS_DEF]) THEN
 (PURE_ONCE_REWRITE_TAC[PLUS_INV_INV_LEMMA]) THEN
 (NEW_SUBST1_TAC(SPECL ["(neg N)";"M:integer"]COMM_PLUS)) THEN
 REFL_TAC));;

%neg_REV_BELOW = |- !M N. (neg M) below (neg N) = N below M%


%WELL_ORDER =
 |- !S1. (?m. S1 m) ==> (?m. S1 m /\ (!n. n < m ==> ~S1 n))%

% --------------------------------------------------------------------- %
% At this point, the following very complicated proof of DISCRETE fails	%
% in HOL version 12.  So just load in the version 11resolution tools.	%
% [TFM 91.01.28]							%
% --------------------------------------------------------------------- %

loadt `compat11`;;

let DISCRETE =prove_thm(`DISCRETE`,
"!S1. (?M. S1 M) ==>
  ((?K1.!N.((N below K1) ==> ~ S1 N)) ==> 
    (?M1. S1 M1 /\ (!N1.(N1 below M1) ==> ~ S1 N1))) /\
  ((?K1.!N.((K1 below N) ==> ~ S1 N)) ==> 
    (?M1. S1 M1 /\ (!N1.(M1 below N1) ==> ~ S1 N1)))",
((REV_SUPPOSE_TAC "!S1. (?M. S1 M) ==>((?K1.!N.((N below K1) ==> ~ S1 N)) ==> 
     (?M1. S1 M1 /\ (!N1.(N1 below M1) ==> ~ S1 N1)))") THENL
 [((REPEAT STRIP_TAC) THEN
   (EXISTS_TAC "(INT (@m. S1((INT m) plus K1) /\
     (!n. n < m ==> ~S1((INT n) plus K1)))) plus K1") THEN
   (SUPPOSE_TAC "?m.((S1:integer -> bool) ((INT m) plus K1))") THENL
   [(let st1 = (SELECT_RULE (UNDISCH (NORMALIZE []
       (SPEC "\x.((S1:integer -> bool) ((INT x) plus K1))" WELL_ORDER)))) in
     (CONJ_TAC THENL [(ACCEPT_TAC (CONJUNCT1 st1));ALL_TAC]) THEN
     GEN_TAC THEN
     (((DISJ_CASES_TAC (SPECL ["N1:integer";"K1:integer"] COMPAR)) THENL
        [ALL_TAC; (POP_ASSUM DISJ_CASES_TAC)]) THENL
       [(RES_TAC THEN  STRIP_TAC THEN (FIRST_ASSUM ACCEPT_TAC));
        (NEW_SUBST1_TAC 
          ((PURE_REWRITE_RULE [BELOW_DEF; POS_DEF; MINUS_DEF]
               (ASSUME "K1 below N1")) and_then
            SELECT_RULE and_then
            ((NORMALIZE []) o (AP_TERM "\x.(x plus K1)")) and_then
            (PURE_REWRITE_RULE
                 [PLUS_GROUP_ASSOC;PLUS_INV_LEMMA;PLUS_ID_LEMMA])));
         (NEW_SUBST1_TAC
           (TRANS
             (ASSUME "N1:integer = K1")
            (SYM (SPEC "K1:integer" (CONJUNCT1 PLUS_ID_LEMMA)))))]) THEN
     (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL (PLUS_BELOW_TRANSL)))]) THEN
     (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL (NUM_LESS_IS_INT_BELOW)))]) THEN
     (MATCH_ACCEPT_TAC (SPEC "n:num" (CONJUNCT2 st1))));
    (((DISJ_CASES_TAC (SPECL ["M:integer";"K1:integer"] COMPAR)) THENL
        [ALL_TAC; (POP_ASSUM DISJ_CASES_TAC)]) THENL
      [RES_THEN MP_TAC THEN ASM_REWRITE_TAC[];
     % WW 26 Jan 94 The above line used to read RES_TAC; %
       ((EXISTS_TAC "SUC(@n . M plus (neg K1) = INT(SUC n))") THEN
        (NEW_SUBST1_TAC 
          ((PURE_REWRITE_RULE [BELOW_DEF; POS_DEF; MINUS_DEF]
               (ASSUME "K1 below M")) and_then
            SELECT_RULE and_then
            ((NORMALIZE []) o (AP_TERM "\x.(x plus K1)")) and_then
            (PURE_REWRITE_RULE
                 [PLUS_GROUP_ASSOC;PLUS_INV_LEMMA;PLUS_ID_LEMMA]) and_then
            SYM)) THEN
        (FIRST_ASSUM ACCEPT_TAC));
       ((EXISTS_TAC "0") THEN
        (PURE_ONCE_REWRITE_TAC [(CONJUNCT1 PLUS_ID_LEMMA)]) THEN
        (NEW_SUBST1_TAC (SYM (ASSUME "M:integer = K1"))) THEN
        (FIRST_ASSUM ACCEPT_TAC))])]);
  (GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [RES_TAC;
    (let st2 = (ASSUME "!S1. (?M. S1 M) ==> (?K1. !N. N below K1 ==>
       ~S1 N) ==> (?M1. S1 M1 /\ (!N1. N1 below M1 ==> ~S1 N1))") and_then
       ((NORMALIZE []) o (SPEC "\x. ((S1:integer -> bool) (neg x))")) and_then
       (PURE_ONCE_REWRITE_RULE [(SYM(SPEC_ALL neg_REV_BELOW))]) and_then
       UNDISCH_ALL and_then
       SELECT_RULE in
     STRIP_TAC THEN
     (EXISTS_TAC "neg(@M1. S1(neg M1) /\
                  (!N1. (neg M1) below (neg N1) ==> ~S1(neg N1)))") THEN
     ((SUPPOSE_TAC "?M. (S1:integer -> bool) (neg M)") THENL
      [(SUPPOSE_TAC "?K1. !N. (neg K1) below (neg N) ==> ~S1(neg N)");
       ALL_TAC]) THENL
      [(CONJ_TAC THENL
        [(ACCEPT_TAC (CONJUNCT1 st2));
         (GEN_TAC THEN
          (ACCEPT_TAC (PURE_ONCE_REWRITE_RULE [PLUS_INV_INV_LEMMA]
            (SPEC "neg N1" (CONJUNCT2 st2)))))]);
       ((EXISTS_TAC "neg K1") THEN
        GEN_TAC THEN
        (PURE_ONCE_REWRITE_TAC [PLUS_INV_INV_LEMMA]) THEN
        (ACCEPT_TAC (SPEC "neg N" (ASSUME "!N. K1 below N ==> ~S1 N"))));
       ((EXISTS_TAC "neg (@M. (S1:integer -> bool) M)") THEN
        (PURE_ONCE_REWRITE_TAC [PLUS_INV_INV_LEMMA]) THEN
        (ACCEPT_TAC (SELECT_RULE (ASSUME "?M:integer. S1 M"))))])])]));;

%DISCRETE = 
|- !S1.
    (?M. S1 M) ==>
    ((?K1. !N. N below K1 ==> ~S1 N) ==>
     (?M1. S1 M1 /\ (!N1. N1 below M1 ==> ~S1 N1))) /\
    ((?K1. !N. K1 below N ==> ~S1 N) ==>
     (?M1. S1 M1 /\ (!N1. M1 below N1 ==> ~S1 N1))) %


loadf `integer_tac`;;

% The following theorems were added on 23 July 1989, by E.L.Gunter
  POS_MULT_PRES_BELOW
    |- !M N P. POS M ==> (N below P = (M times N) below (M times P))
  NEG_MULT_REV_BELOW
    |- !M N P. NEG M ==> (N below P = (M times P) below (M times N))
  POS_IS_ZERO_BELOW  |- !N. POS N = (INT 0) below N
  NEG_IS_BELOW_ZERO  |- !N. NEG N = N below (INT 0)
  neg_ONE_ONE  |- !x y. (neg x = neg y) = (x = y)
  neg_ZERO  |- neg(INT 0) = INT 0
  INT_INTEGRAL_DOMAIN
    |- !x y. (x times y = INT 0) ==> (x = INT 0) \/ (y = INT 0)
  TIMES_LEFT_CANCELLATION
    |- !x y z. ~(x = INT 0) ==> (x times y = x times z) ==> (y = z)
  TIMES_RIGHT_CANCELLATION
    |- !x y z. ~(x = INT 0) ==> (y times x = z times x) ==> (y = z)
%


let POS_MULT_PRES_BELOW = prove_thm (`POS_MULT_PRES_BELOW`,
 "!M N P. POS M ==> ((N below P) = ((M times N) below (M times P)))",
((REPEAT STRIP_TAC) THEN
 (POP_ASSUM (\thm.(STRIP_ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE[POS_DEF] thm)))) THEN
 (POP_ASSUM (\thm.(PURE_ONCE_REWRITE_TAC[thm]))) THEN
 (PURE_REWRITE_TAC [BELOW_DEF; MINUS_DEF]) THEN
 (PURE_REWRITE_TAC
  [(SYM (SPEC_ALL (CONJUNCT1 TIMES_neg)));
   (SYM (SPEC_ALL LEFT_PLUS_DISTRIB))]) THEN
 (PURE_ONCE_REWRITE_TAC [POS_DEF]) THEN
 EQ_TAC THEN (REPEAT STRIP_TAC) THENL
 [((FIRST_ASSUM NEW_SUBST1_TAC) THEN
   (REWRITE_TAC [NUM_MULT_IS_INT_MULT;MULT;ADD_CLAUSES]) THEN
   (EXISTS_TAC "(n * (SUC n')) + n'") THEN REFL_TAC);
  ((PURE_ONCE_REWRITE_TAC[(SYM (SPEC_ALL POS_DEF))]) THEN
   ((DISJ_CASES_TAC (CONJUNCT1 (SPEC "P plus (neg N)" TRICHOTOMY))) THENL
    [(FIRST_ASSUM ACCEPT_TAC); (POP_ASSUM DISJ_CASES_TAC)]) THENL
   [((POP_ASSUM \thm. (STRIP_ASSUME_TAC
     (PURE_REWRITE_RULE [NEG_DEF;POS_DEF] thm))) THEN
     (POP_ASSUM \thm1. (POP_ASSUM \thm2.
      (CONTR_TAC ((PURE_REWRITE_RULE
        [(PURE_ONCE_REWRITE_RULE [PLUS_INV_INV_LEMMA] (AP_TERM "neg" thm1));
         TIMES_neg;NUM_MULT_IS_INT_MULT]
        thm2) and_then
        (AP_TERM "$plus (INT((SUC n) * (SUC n'')))") and_then
        (REWRITE_RULE
          [PLUS_INV_LEMMA;NUM_ADD_IS_INT_ADD;ADD_CLAUSES; INT_ONE_ONE;
           (PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] NOT_SUC)]))))));
    (POP_ASSUM \thm1. (POP_ASSUM \thm2.
      (CONTR_TAC (REWRITE_RULE [thm1; TIMES_ZERO; INT_ONE_ONE;
           (PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] NOT_SUC)] thm2))))])]));;

%POS_MULT_PRES_BELOW = 
 |- !M N P. POS M ==> (N below P = (M times N) below (M times P))%


let NEG_MULT_REV_BELOW = prove_thm (`NEG_MULT_REV_BELOW`,
"!M N P. NEG M ==> ((N below P) = ((M times P) below (M times N)))",
((REWRITE_TAC [NEG_DEF]) THEN (REPEAT STRIP_TAC) THEN
 (NEW_SUBST1_TAC (SYM (SPEC "M:integer" PLUS_INV_INV_LEMMA))) THEN
 (PURE_REWRITE_TAC [(SPEC "neg M" (CONJUNCT2 TIMES_neg))]) THEN
 (NEW_SUBST1_TAC
   (SPECL ["(neg M) times P";"(neg M) times N"] neg_REV_BELOW)) THEN
 (NEW_MATCH_ACCEPT_TAC (UNDISCH (SPEC_ALL POS_MULT_PRES_BELOW)))));;

%NEG_MULT_REV_BELOW = 
 |- !M N P. NEG M ==> (N below P = (M times P) below (M times N))%


let POS_IS_ZERO_BELOW = prove_thm (`POS_IS_ZERO_BELOW`,
"!N. (POS N) = ((INT 0) below N)",
(GEN_TAC THEN
 (REWRITE_TAC [BELOW_DEF;MINUS_DEF;PLUS_INV_ID_LEMMA;PLUS_ID_LEMMA])));;

%POS_IS_ZERO_BELOW = |- !N. POS N = (INT 0) below N%


let NEG_IS_BELOW_ZERO = prove_thm (`NEG_IS_BELOW_ZERO`,
 "!N. (NEG N) = (N below (INT 0))",
(GEN_TAC THEN
 (PURE_ONCE_REWRITE_TAC [NEG_DEF;(SYM (SPEC_ALL neg_REV_BELOW))]) THEN
 (REWRITE_TAC [PLUS_INV_ID_LEMMA; POS_IS_ZERO_BELOW])));;

%NEG_IS_BELOW_ZERO = |- !N. NEG N = N below (INT 0)%


let neg_ONE_ONE = prove_thm(`neg_ONE_ONE`, "!x y. (neg x = neg y) = (x = y)",
((REPEAT GEN_TAC) THEN
 (SUPPOSE_TAC "!x y. (x = y) ==> (neg x = neg y)") THENL
 [(EQ_TAC THENL
   [(POP_ASSUM \thm.(ACCEPT_TAC
      (PURE_REWRITE_RULE[PLUS_INV_INV_LEMMA] (SPECL ["neg x";"neg y"] thm))));
    (POP_ASSUM \thm.(ACCEPT_TAC (SPEC_ALL thm)))]);
  ((REPEAT STRIP_TAC) THEN
   (POP_ASSUM \thm.(ACCEPT_TAC
     (AP_TERM "neg" thm))))]));;

% neg_ONE_ONE = |- !x y. (neg x = neg y) = (x = y) %


let neg_ZERO = prove_thm (`neg_ZERO`, "neg (INT 0) = (INT 0)",
((PURE_ONCE_REWRITE_TAC [neg_IS_TIMES_neg1]) THEN
 (REWRITE_TAC [TIMES_ZERO])));;

% neg_ZERO = |- neg(INT 0) = INT 0 %


let INT_INTEGRAL_DOMAIN = prove_thm(`INT_INTEGRAL_DOMAIN`,
"!x y. (x times y = (INT 0)) ==> ((x = (INT 0)) \/ (y = (INT 0)))",
(INT_CASES_TAC THENL
 [(INDUCT_TAC THENL
   [(REWRITE_TAC []);
    (INT_CASES_TAC THENL
     [((SUBST_MATCH_TAC ADD1) THEN
       (PURE_REWRITE_TAC
         [(SYM (SPEC_ALL (NUM_ADD_IS_INT_ADD)));
          RIGHT_PLUS_DISTRIB;
          TIMES_IDENTITY]) THEN
       (REWRITE_TAC
         [NUM_MULT_IS_INT_MULT;
          NUM_ADD_IS_INT_ADD;
          INT_ONE_ONE;
          ADD_EQ_0]) THEN
       (REPEAT STRIP_TAC) THEN (ASM_REWRITE_TAC []));
      ((PURE_REWRITE_TAC [TIMES_neg]) THEN
       (PURE_ONCE_REWRITE_TAC [(SYM neg_ZERO)]) THEN
       (PURE_ONCE_REWRITE_TAC [neg_ONE_ONE]) THEN
       (ASM_REWRITE_TAC [neg_ZERO]))])]);
  ((PURE_REWRITE_TAC [TIMES_neg]) THEN
   (PURE_ONCE_REWRITE_TAC [(SYM neg_ZERO)]) THEN
   (PURE_ONCE_REWRITE_TAC [neg_ONE_ONE]) THEN
   (ASM_REWRITE_TAC [neg_ZERO]))]));;

% INT_INTEGRAL_DOMAIN = 
  |- !x y. (x times y = INT 0) ==> (x = INT 0) \/ (y = INT 0) %


let TIMES_LEFT_CANCELLATION = prove_thm(`TIMES_LEFT_CANCELLATION`,
"!x y z. ~(x = (INT 0)) ==> (x times y = x times z) ==> (y = z)",
((REPEAT STRIP_TAC) THEN
 (MP_IMP_TAC (SPECL ["neg z";"y:integer";"z:integer"]
   PLUS_RIGHT_CANCELLATION)) THEN
 (PURE_ONCE_REWRITE_TAC [PLUS_INV_LEMMA]) THEN
  (use_thm 
   (UNDISCH
    (PURE_ONCE_REWRITE_RULE
     [(ONCE_REWRITE_RULE [] (SYM(SPECL["~t1";"t2:bool"] IMP_DISJ_THM)))]
     (UNDISCH (SPECL ["x:integer";"y plus (neg z)"] INT_INTEGRAL_DOMAIN))))
    ACCEPT_TAC) THEN
 (MP_IMP_TAC (SPECL ["x times z";"x times (y plus (neg z))";"INT 0"]
   PLUS_RIGHT_CANCELLATION)) THEN
 (PURE_REWRITE_TAC [PLUS_ID_LEMMA;LEFT_PLUS_DISTRIB;PLUS_GROUP_ASSOC]) THEN
 (PURE_ONCE_REWRITE_TAC [TIMES_neg]) THEN
 (ASM_REWRITE_TAC [PLUS_INV_LEMMA; PLUS_ID_LEMMA])));;

% TIMES_LEFT_CANCELLATION = 
  |- !x y z. ~(x = INT 0) ==> (x times y = x times z) ==> (y = z) %


let TIMES_RIGHT_CANCELLATION = prove_thm(`TIMES_RIGHT_CANCELLATION`,
"!x y z. ~(x = (INT 0)) ==> (y times x = z times x) ==> (y = z)",
((PURE_ONCE_REWRITE_TAC [COMM_TIMES]) THEN
 (ACCEPT_TAC TIMES_LEFT_CANCELLATION)));;

% TIMES_RIGHT_CANCELLATION = 
  |- !x y z. ~(x = INT 0) ==> (y times x = z times x) ==> (y = z) %


% close_theory `integer`;;	close_theory takes void [TFM 90.06.11] %

close_theory();;

