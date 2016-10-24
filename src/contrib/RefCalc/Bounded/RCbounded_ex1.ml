% File: RCbounded_ex1.ml %

% An example backwards data refinement: a simple countdown --- %

let AINIT  = "\(a,x). a<=x";;
let AGUARD = "\(a,x). a<x";;
let ABODY  = "assign (\(a:num,x). (a,x-1))";;

let CINIT  = "\(c:bool,x). 0<x";;
let CGUARD = "\(c,x). c /\ (0<x)";;
let CBODY  = "(assign(\(c:bool,x). (c,x-1))) dch (assign(\(c,x). ((~c),x-1)))";;

% abstract loop:  [ VAR a.a<=x ; DO a<x -> x:=x-1 OD ] %
let ASYS = "block ^AINIT (do ^AGUARD ^ABODY)";;

% concrete loop:  [ VAR c.0<x ; DO c/\(0<x) -> c,x:=?,x-1 OD ] %
let CSYS = "block ^CINIT (do ^CGUARD ^CBODY)";;

% abstraction relation R: (c /\ (0<x) <=> (a<x)) /\ (a<=x) %
let R = "\(a,c,x). (c /\ (0<x) = (a<x)) /\ (a<=x)";;

let t = TAUT "t==>t'==>t'' = t/\t'==>t''";;
let t1 = TAUT "t/\(t'\/t'') = (t/\t')\/(t/\t'')";;
let t2 = TAUT "~t/\t = F";;
let t3 = TAC_PROOF(([],"(~0<x) = (x=0)"),
           LRT[NOT_LESS;LESS_OR_EQ;NOT_LESS_0]);;
let t4 = TAUT "t/\(t\/t') = t";;
let t5 = TAUT "t\/t'==>t'' = (t==>t'') /\ (t'==>t'')";;
let nondass_dch = prove
  ("(nondass P) dch (nondass Q) = nondass (\v:*s1.\v':*s2. P v v' \/ Q v v')",
   FUN_TAC THEN LPRT[dch_DEF;and_DEF;nondass_DEF] THEN FUN_TAC THEN 
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let grd_seq_nondass = prove
 ("(guard b) seq (nondass P) = nondass (\v:*s1.\v':*s2. b v /\ P v v')",
   FUN_TAC THEN LPRT[seq_DEF;guard_DEF;imp_DEF;nondass_DEF] THEN FUN_TAC THEN 
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let finiteR = prove ("finite (\a. ^R(a,k,u))",
  PORT[finite_DEF] THEN PBETA_TAC THEN EXISTS_TAC "\(i:num).i" THEN
  EXISTS_TAC "SUC u" THEN GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
  EXISTS_TAC "a:num" THEN RT[] THEN POP_ASSUM MP_TAC THEN
  PORT[LESS_OR_EQ] THEN STRIP_TAC THEN ART[LESS_SUC_REFL] THEN
  IMP_RES_TAC LESS_SUC);;

goal "^ASYS ref ^CSYS";;
e(MATCH_MP_TAC actsys_bwdref THEN EXISTS_TAC R THEN REPEAT CONJ_TAC);;
%1%e(MATCH_ACCEPT_TAC ucont_assign);;
%2%e(MATCH_MP_TAC ucont_dch THEN LRT[ucont_guard;ucont_assign]);;
%3%e(REPEAT GEN_TAC THEN PBETA_TAC THEN ASM_CASES_TAC "(u=0) \/ k" THENL
     [EXISTS_TAC "0" THEN POP_ASSUM MP_TAC THEN REPEAT STRIP_TAC
      THEN ART[ZERO_LESS_EQ;LESS_REFL]
     ;EXISTS_TAC "u:num" THEN POP_ASSUM (MP_TAC o PORR[DE_MORGAN_THM])
      THEN STRIP_TAC THEN ART[] THEN RT[LESS_OR_EQ;LESS_REFL]
     ]);;
%4%e(MATCH_MP_TAC ucont_dualabst THEN MATCH_ACCEPT_TAC finiteR);;
%5%e(REPEAT GEN_TAC THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN ART[]);;
%6%e(REPEAT GEN_TAC THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN ART[]);;
%7%e(LPORT[assign_eq_nondass;nondass_dch;grd_seq_nondass] THEN PBETA_TAC THEN
     MATCH_MP_TAC nondass_bwdref THEN PBETA_TAC THEN RT[PAIR_EQ] THEN
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC "a':num" THEN UNDISCH_TAC "a'<=u'" THEN ART[] THEN
      UNDISCH_TAC "0<u" THEN CASE_TAC"u:num" num_CASES[LESS_REFL;LESS_0] THEN
      LPORT[SUC_SUB1;LESS_OR_EQ] THEN REPEAT STRIP_TAC THEN 
      IMP_RES_TAC LESS_SUC THEN ART[LESS_SUC_REFL]
     ;EXISTS_TAC "a':num" THEN UNDISCH_TAC "a'<=u'" THEN ART[] THEN
      UNDISCH_TAC "0<u" THEN CASE_TAC"u:num" num_CASES[LESS_REFL;LESS_0] THEN
      LPORT[SUC_SUB1;LESS_OR_EQ] THEN REPEAT STRIP_TAC THEN 
      IMP_RES_TAC LESS_SUC THEN ART[LESS_SUC_REFL]
     ]);;

let thm = top_thm();;
