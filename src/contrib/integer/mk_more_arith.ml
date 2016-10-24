% FILE		: mk_more_arith.ml					%
% DESCRIPTION   : contains some arithmetic theorems useful in		%
%                 developing the integers.				% 
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
%-----------------------------------------------------------------------%

% add_lib_path `group`;; Not needed for HOL88.1.05 (MJCG 14 April, 1989)%

% --------------------------------------------------------------------- %
% Uses the code start_groups.ml from the group library.  But we don't 	%
% load the entire group library, since the theories are not needed here %
% [TFM 91.01.28]							%
% --------------------------------------------------------------------- %

loadf (library_pathname() ^ `/group/start_groups`);;

new_theory `more_arith`;;


let AND_DIST_OR=prove_thm(`AND_DIST_OR`,
"!t1 t2 t3.(t1/\(t2\/t3))=((t1/\t2)\/(t1/\t3))",
((REPEAT GEN_TAC) THEN
 (ASM_CASES_TAC "t1:bool") THEN
 (ASM_REWRITE_TAC[])));;

%AND_DIST_OR = 
 |- !t1:bool t2:bool t3:bool. t1 /\ (t2 \/ t3) = t1 /\ t2 \/ t1 /\ t3%


let ADDL_GREATER = prove_thm (`ADDL_GREATER`,
"!m n p.m<n==>m<(p+n)",
(GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN
 (ASM_REWRITE_TAC (CONJUNCTS ADD_CLAUSES)) THEN
 RES_TAC THEN
 (ASM_REWRITE_TAC[(UNDISCH_ALL(SPECL ["m:num";"(p+n)"] LESS_SUC))])));;

%ADDL_GREATER = |- !m:num n:num p:num. m < n ==> m < (p + n)%


let ADDL_GREATER_EQ = prove_thm (`ADDL_GREATER_EQ`,
"!m n p. m <= n ==> m <= p+n",
((REPEAT GEN_TAC) THEN DISCH_TAC THEN
 (ASSUME_TAC (REWRITE_RULE [(CONJUNCT1(CONJUNCT2 ADD_CLAUSES))]
  (SPECL ["m:num";"0";"n:num";"p:num"] LESS_EQ_LESS_EQ_MONO))) THEN
 (ASSUME_TAC (REWRITE_RULE [(SPECL ["m:num";"n:num"] NOT_LESS)]
  (SPEC "p:num" NOT_LESS_0))) THEN RES_TAC THEN
 (SUBST_TAC [(SPECL ["p:num";"n:num"] ADD_SYM)]) THEN
 (FIRST_ASSUM ACCEPT_TAC)));;

%ADDL_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (p + n)%


let ADDR_GREATER = save_thm(`ADDR_GREATER`,
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER);;

%ADDR_GREATER = |- !m:num n:num p:num. m < n ==> m < (n + p)%


let ADDR_GREATER_EQ = save_thm(`ADDR_GREATER_EQ`,
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER_EQ);;

%ADDR_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (n + p)%


let SUB_LESS_TO_LESS_ADDR = prove_thm(`SUB_LESS_TO_LESS_ADDR`,
"!m n p.((p<=m)==>(((m-p)<n)=(m<(n+p))))",
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL["m-p";"n:num";"p:num"]LESS_MONO_ADD_EQ));
   (UNDISCH_ALL(SPECL["m:num";"p:num"]SUB_ADD))])));;

%SUB_LESS_TO_LESS_ADDR = 
 |- !m:num n:num p:num. p <= m ==> ((m - p) < n = m < (n + p))%


let SUB_LESS_TO_LESS_ADDL = prove_thm(`SUB_LESS_TO_LESS_ADDL`,
"!m n p.((n<=m)==>(((m-n)<p)=(m<(n+p))))",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["m:num";"p:num";"n:num"]SUB_LESS_TO_LESS_ADDR))));;


%SUB_LESS_TO_LESS_ADDL = 
 |- !m:num n:num p:num. n <= m ==> ((m - n) < p = m < (n + p))%

let LESS_SUB_TO_ADDR_LESS = prove_thm(`LESS_SUB_TO_ADDR_LESS`,
"!m n p.((p<=m)==>((n<(m-p))=(n+p)<m))",
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL["n:num";"m-p";"p:num"]LESS_MONO_ADD_EQ));
   (UNDISCH_ALL(SPECL["m:num";"p:num"] SUB_ADD))])));;

%LESS_SUB_TO_ADDR_LESS = 
 |- !m:num n:num p:num. p <= m ==> (n < (m - p) = (n + p) < m)%


let LESS_SUB_TO_ADDL_LESS = prove_thm(`LESS_SUB_TO_ADDL_LESS`,
"!m n p.((n<=m)==>((p<(m-n))=((n+p)<m)))",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["m:num";"p:num";"n:num"]LESS_SUB_TO_ADDR_LESS))));;

%LESS_SUB_TO_ADDL_LESS = 
 |- !m:num n:num p:num. n <= m ==> (p < (m - n) = (n + p) < m)%


let SUB_SAME_EQ_0=prove_thm(`SUB_SAME_EQ_0`, "!m.m-m=0",
(GEN_TAC THEN
 (SUBST1_TAC (SPECL["m:num";"m:num"]SUB_EQ_0)) THEN
 (PURE_ONCE_REWRITE_TAC [LESS_OR_EQ]) THEN
 DISJ2_TAC THEN REFL_TAC));;

%SUB_SAME_EQ_0 = |- !m:num. m - m = 0%


let SUC_SUB = prove_thm (`SUC_SUB`,
"!m n.(((m<n)==>(((SUC m)-n)=0))/\(~(m<n)==>(((SUC m)-n)=SUC(m-n))))",
((REPEAT GEN_TAC) THEN (ASM_CASES_TAC "m<n") THEN
 (ASM_REWRITE_TAC
  [((REWRITE_RULE [COND_DEF] (CONJUNCT2 SUB)) and_then
    CONV_RULE(DEPTH_CONV BETA_CONV))])
THENL
 [((SELECT_TAC "@x.x=0") THEN (EXISTS_TAC "0") THEN REFL_TAC);
  ((SELECT_TAC"@x.x=SUC(m-n)")THEN(EXISTS_TAC"SUC(m-n)")THEN REFL_TAC)]));;

%SUC_SUB = 
 |- !m:num n:num.
     (m < n ==> ((SUC m) - n = 0)) /\
     (~m < n ==> ((SUC m) - n = SUC(m - n)))%


let DOUBLE_SUB = prove_thm (`DOUBLE_SUB`,
"!m n p.((m-n)-p)=(m-(n+p))",
((REPEAT GEN_TAC) THEN (SPEC_TAC ("m:num","m:num")) THEN INDUCT_TAC THENL
 [(REWRITE_TAC [(CONJUNCT1(SUB))]);
  ((ASM_CASES_TAC "m<n") THENL
  [((REWRITE_TAC[(UNDISCH_ALL(CONJUNCT1(SPECL["m:num";"n:num"]SUC_SUB)))])
     THEN (ASSUME_TAC (SPECL ["m:num";"n:num";"p:num"] ADDR_GREATER))
     THEN RES_TAC THEN
     (REWRITE_TAC[(UNDISCH_ALL(CONJUNCT1(SPECL["m:num";"n+p"]SUC_SUB)));
      (CONJUNCT1 SUB)]));
   ((REWRITE_TAC[(UNDISCH_ALL(CONJUNCT2(SPECL["m:num";"n:num"]SUC_SUB)))])
    THEN (ASM_CASES_TAC "m<(n+p)") THENL
    [(REWRITE_TAC[(UNDISCH_ALL(CONJUNCT1(SPECL["m:num";"n+p"]SUC_SUB)))]);
     (REWRITE_TAC[(UNDISCH_ALL(CONJUNCT2(SPECL["m:num";"n+p"]SUC_SUB)))])]
    THENL (let thm1 =TAC_PROOF
     ((["~m<n"],"(m < (n + p) ==> ((SUC(m - n)) - p = 0)) /\
     (~m < (n + p) ==> ((SUC(m - n)) - p = SUC((m - n) - p)))"),
     ((SUBST1_TAC (SPECL ["n:num";"p:num"] ADD_SYM)) THEN
      (ACCEPT_TAC
       (REWRITE_RULE
       [(SYM(REWRITE_RULE
        [((REWRITE_RULE [(SYM (SPECL ["m:num";"n:num"] NOT_LESS))]
          (SPECL ["m:num";"n:num"] SUB_ADD))and_then UNDISCH_ALL)]
        (SPECL["m-n";"p:num";"n:num"] LESS_MONO_ADD_EQ)))]
      (SPECL["m-n";"p:num"]SUC_SUB))))) in
    [(ASM_REWRITE_TAC[(UNDISCH_ALL(CONJUNCT1(thm1)))]);
     (ASM_REWRITE_TAC[(UNDISCH_ALL(CONJUNCT2(thm1)))])]))])]));;

%DOUBLE_SUB = |- !m:num n:num p:num. (m - n) - p = m - (n + p)%


let SIMP1=prove_thm (`SIMP1`,
"!m n p.((p <= n) ==> (m+(n-p)=(m+n)-p))",
((REPEAT GEN_TAC) THEN (SPEC_TAC ("m:num", "m:num")) THEN INDUCT_TAC THENL
 [(REWRITE_TAC [(CONJUNCT1 ADD)]);
  ((REWRITE_TAC [(CONJUNCT2 ADD)]) THEN
   DISCH_TAC THEN
   (ASSUME_TAC (SPECL ["p:num";"n:num";"m:num"] ADDL_GREATER_EQ)) THEN
   (ASSUME_TAC (snd(EQ_IMP_RULE(SPECL ["m+n";"p:num"] NOT_LESS)))) THEN
   RES_TAC THEN RES_TAC THEN
   (ASM_REWRITE_TAC [(UNDISCH_ALL(CONJUNCT2(SPECL["m+n";"p:num"]SUC_SUB)))])
  )]));;

%SIMP1 = |- !m:num n:num p:num. p <= n ==> (m + (n - p) = (m + n) - p)%


let SIMP2=prove_thm (`SIMP2`,
"!m n p. p <= m ==> ((m-p)+n = (m+n)-p)",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["n:num";"m:num";"p:num"]SIMP1))));;

%SIMP2 = |- !m:num n:num p:num. p <= m ==> ((m - p) + n = (m + n) - p)%


let SIMP3=prove_thm (`SIMP3`,
"!m n p.((n<=p)==>((m-(p-n))=((m+n)-p)))",
((REPEAT GEN_TAC) THEN (SPEC_TAC ("m:num","m:num")) THEN INDUCT_TAC THENL
[(DISCH_TAC THEN (CONV_TAC SYM_CONV) THEN
  (ASM_REWRITE_TAC[(CONJUNCT1 ADD);(CONJUNCT1 SUB);(SPEC_ALL SUB_EQ_0)]));
 (DISCH_TAC THEN RES_TAC THEN
  (REWRITE_TAC[(CONJUNCT2 ADD);(CONJUNCT2 SUB)]) THEN
  (ASM_REWRITE_TAC[(UNDISCH_ALL(SPECL["p:num";"m:num";"n:num"]
    LESS_SUB_TO_ADDR_LESS))]) )]));;

%SIMP3 = |- !m:num n:num p:num. n <= p ==> (m - (p - n) = (m + n) - p)%


% Moved to main system by RJB on 92.10.08 %
%let LEFT_SUB_DISTRIB = save_thm (`LEFT_SUB_DISTRIB`,%
%((SPECL["n:num";"p:num";"m:num"] RIGHT_SUB_DISTRIB) and_then%
% (PURE_ONCE_REWRITE_RULE[MULT_SYM]) and_then%
% (GENL["m:num";"n:num";"p:num"])));;%

%LEFT_SUB_DISTRIB = 
 |- !m:num n:num p:num. m * (n - p) = (m * n) - (m * p)%


let GEN_INDUCTION = prove_thm(`GEN_INDUCTION`,
"!P.(P 0 /\(!n.(!m.(m<n) ==> P m) ==> P n)) ==> !n.P n",
(GEN_TAC THEN 
 DISCH_TAC THEN
 GEN_TAC THEN
 (ACCEPT_TAC (
  let st1=TAC_PROOF((["P 0/\(!n.(!m.(m<n) ==> P m) ==> P n)"],
   "!n.(!m.(m<n) ==> P m)"),
  (INDUCT_TAC THEN
   GEN_TAC THENL
  [(REWRITE_TAC[NOT_LESS_0]);
   ((PURE_ONCE_REWRITE_TAC[LESS_THM]) THEN
    DISCH_TAC THEN
    (ASSUM_LIST (DISJ_CASES_TAC o hd)) THENL
    [((PURE_ONCE_REWRITE_TAC[(ASSUME "m = (n:num)")]) THEN
      (ASSUM_LIST(ACCEPT_TAC o(\thl.MP
       (SPEC "n:num" ((CONJUNCT2 o hd o tl o tl o tl) thl))
       ((hd o tl o tl)thl)))));
     (ASSUM_LIST(ACCEPT_TAC o (\thl.MP
      (SPEC "m:num" ((hd o tl o tl)thl)) (hd thl) )))])])) in
 ((SPEC "SUC n" st1) and_then (SPEC "n:num") and_then
  (\thm. MP thm (SPEC "n:num" LESS_SUC_REFL))) ))));;

%GEN_INDUCTION = 
 |- !P:num -> bool.
     (P:num -> bool) 0 /\
     (!n:num.
       (!m:num. m < n ==> (P:num -> bool) m) ==> (P:num -> bool) n) ==>
     (!n:num. (P:num -> bool) n)%

%GEN_INDUCTION =
 |- !P. P 0 /\ (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)%


% compilet `num_tac`;;   No point in compiling this here. [TFM 91.01.28] %

loadt `num_tac.ml`;;	 % load instead %

let WELL_ORDER = prove_thm(`WELL_ORDER`,
"!S1.(?m.S1 m)==>(?m.(S1 m)/\(!n.(n<m)==>~(S1 n)))",
(
let st1=TAC_PROOF(([],
 "!p.(?m.(m<=p)/\(S1 m))==>(?m.(S1 m)/\(!n.(n<m)==>~(S1 n)))"),
(GEN_INDUCT_TAC THEN
 (PURE_ONCE_REWRITE_TAC[LESS_OR_EQ]) THENL
[((REWRITE_TAC[NOT_LESS_0]) THEN
  DISCH_TAC THEN
  (EXISTS_TAC "0") THEN
  (REWRITE_TAC[NOT_LESS_0]) THEN
  (ASSUM_LIST
   (ACCEPT_TAC o
   (\thm.(SUBS[(CONJUNCT1(SELECT_RULE thm))](CONJUNCT2(SELECT_RULE thm))))o
   hd)) );
 ((ASM_CASES_TAC "?m. m < p /\ S1 m") THEN
  (PURE_ONCE_REWRITE_TAC[(PURE_ONCE_REWRITE_RULE[CONJ_SYM]AND_DIST_OR)]) THEN
  DISCH_TAC THENL
  [(ASSUM_LIST (ACCEPT_TAC o (\thml.
    (let thm1= (SELECT_RULE o hd o tl)thml in
     let thm2= ((SPEC "(@m.m<p /\ S1 m)") o hd o tl o tl)thml in
     let thm3=TAC_PROOF(([],"(?m'.m'<= (@m. m < p /\ S1 m) /\ S1 m')"),
     ((EXISTS_TAC "(@m.m<p /\ S1 m)") THEN
      (REWRITE_TAC[LESS_OR_EQ;(CONJUNCT2 thm1)]))) in
     (MP (MP thm2 (CONJUNCT1 thm1))thm3) ))));
   ((EXISTS_TAC "p:num") THEN
    (ASSUM_LIST (\thml.
     (let thm1=(EQ_MP (NOT_EXISTS_CONV(concl((hd o tl)thml)))
                 ((hd o tl)thml)) in
      let thm2= (\thm.(SUBS[(CONJUNCT1(SELECT_RULE thm))]
                (CONJUNCT2(SELECT_RULE thm))))(REWRITE_RULE[thm1](hd thml)) in
      let thm3= (PURE_REWRITE_RULE[DE_MORGAN_THM;(SYM(SPEC_ALL IMP_DISJ_THM))]
                (SPEC "n:num" thm1)) in
      REWRITE_TAC[thm2;thm3]))) )])])) in

 GEN_TAC THEN
 DISCH_TAC THEN
 (ASSUM_LIST (ACCEPT_TAC o (\thml.
  (let thm1 = SELECT_RULE (hd thml) in
   let thm2 = SPEC "@m:num. S1 m" st1 in
   let thm3=TAC_PROOF(([],"(?m. m <= (@m. S1 m) /\ S1 m)"),
    ((EXISTS_TAC "(@m:num. S1 m)") THEN
     (REWRITE_TAC[LESS_OR_EQ;thm1]))) in
   (MP thm2 thm3)) ))) ));;

%WELL_ORDER = 
|- !S1:num -> bool.
    (?m:num. (S1:num -> bool) m) ==>
    (?m:num.
      (S1:num -> bool) m /\ (!n:num. n < m ==> ~(S1:num -> bool) n))%

% close_theory `more_arith`;;	close_theory takes void [TFM 90.06.11] %

close_theory();;




