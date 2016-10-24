%---------------------------------------------------------------%
% word arithmetic based on mapping between word and natural 	%
% numbers--- mainly addition	    				%
%---------------------------------------------------------------%

%<
let EXP_1 = PROVE("!n. 1 EXP n = 1",
    INDUCT_TAC THEN ASM_REWRITE_TAC[EXP;MULT_LEFT_1]);;

let LESS_EQ_EXP_SUC = PROVE(
    "!n b x. (x <= b) ==> (x *(b EXP n)) <= (b EXP (SUC n))",
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[EXP]
    THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
    THEN MATCH_ACCEPT_TAC LESS_MONO_MULT1);;

let LEMMA1 = PROVE(
    "!f b. (!x. f x < b) ==> 
     !n. !w1 w2:(*)word::PWORDLEN n.
     ((NVAL f b w1) + (NVAL f b w2)) < (2 *(b EXP n))",
    REPEAT STRIP_TAC THEN REPEAT(RESQ_GEN_TAC THEN DISCH_TAC)
    THEN PURE_ONCE_REWRITE_TAC[TIMES2] THEN MATCH_MP_TAC LESS_LESS_MONO
    THEN IMP_RES_THEN RESQ_IMP_RES_TAC NVAL_MAX THEN CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC);;

% |- !b f.    2 <= b ==>
    (!x. (f x) < b) ==>
    (!n. !w1 w2 :: PWORDLEN n.
       ((NVAL f b w2) + (NVAL f b w1)) < (b EXP (SUC n))) %
let ADD_MAX =
    let P =  "PWORDLEN n:(*)word->bool" in
    let th = MATCH_MP LESS_LESS_EQ_TRANS
     (CONJ (RESQ_SPEC_ALL(SPEC_ALL(UNDISCH_ALL(SPEC_ALL LEMMA1))))
           (MATCH_MP LESS_EQ_EXP_SUC (ASSUME "2 <= b"))) in
    GEN_ALL (DISCH_ALL (GEN "n:num"
    (itlist (\v t.RESQ_GEN (v, P) t) ["w1:(*)word"; "w2:(*)word"] th)));;
>%

% --------------------------------------------------------------------- %
% GEN_WADD Fbitval Fbitrep n w1 w2 c					%
% --------------------------------------------------------------------- %


let x = "\(fv:*->num) (fr:num->*) (r:num) (c:*). WORD[c]";;

let f = "\fun n (fv:*->num) (fr:num->*) r c.
    	let sum (a,b,c) = fr(((fv a) + (fv b) + (fv c)) MOD r) in
        let carry (a,b,c) = fr(((fv a) + (fv b) + (fv c)) DIV r) in
   WCAT((fun fv fr r (carry ((BIT (m-(SUC n)) w1), (BIT (m-(SUC n)) w2), c))),
        WORD[sum ((BIT (m-(SUC n)) w1), (BIT (m-(SUC n)) w2), c)])";;

% |- ?fn.
    !m.
     !w1 w2 :: PWORDLEN m.
      (fn m w1 w2 0 = (\fv fr r c. WORD[c])) /\
      (!n.
        fn m w1 w2(SUC n) =
        (\fv fr r c.
          let sum (a,b,c') = fr(((fv a) + ((fv b) + (fv c'))) MOD r)
          in
           let carry (a,b,c') = fr(((fv a) + ((fv b) + (fv c'))) DIV r)
           in
            WCAT (fn m w1 w2 n fv fr r
             (carry(BIT(m - (SUC n))w1,BIT(m - (SUC n))w2,c)),
             WORD[sum(BIT(m - (SUC n))w1,BIT(m - (SUC n))w2,c)])))
%

let defthm = 
    let P1 = "PWORDLEN m (w1:(*)word)" and
    	P2 = "PWORDLEN m (w2:(*)word)" in
    CONV_RULE (SKOLEM_CONV THENC (DEPTH_CONV BETA_CONV) THENC
      (ONCE_DEPTH_CONV FORALL_IMP_CONV) THENC
      (DEPTH_CONV IMP_RES_FORALL_CONV)) (GEN_ALL 
    (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) (DISCH_ALL
    (itlist ADD_ASSUM[P2;P1] (EXISTENCE(ISPECL[x;f]num_Axiom))))));;

% |- !m.
    !w1 w2 :: PWORDLEN m.
     (GEN_WADD m w1 w2 0 = (\fv fr r c. WORD[c])) /\
     (!n.
       GEN_WADD m w1 w2(SUC n) =
       (\fv fr r c.
         let sum (a,b,c') = fr(((fv a) + ((fv b) + (fv c'))) MOD r)
         in
          let carry (a,b,c') = fr(((fv a) + ((fv b) + (fv c'))) DIV r)
          in
           WCAT
           (GEN_WADD m w1 w2 n fv fr r
            (carry(BIT(m - (SUC n))w1,BIT(m - (SUC n))w2,c)),
            WORD[sum(BIT(m - (SUC n))w1,BIT(m - (SUC n))w2,c)])))
 "GEN_WADD :num ->
      ((*)word ->
       ((*)word ->
        (num ->
         ((* -> num) -> ((num -> *) -> (num -> (* -> (*)word)))))))"
%

let GEN_WADD_DEF =
    new_specification `GEN_WADD_DEF` [`constant`,`GEN_WADD`] defthm;;

let GEN_BOOL_WADD_DEF = new_definition(`GEN_BOOL_WADD_DEF`,
    "GEN_BOOL_WADD n m w1 w2 c = GEN_WADD m w1 w2 n BV VB 2 c");;




    "!m n. !w1 w2:(*)word::PWORDLEN n. (n <= m) ==>
     !r c fr fv. (!x:*. ((fv x) < r) /\ (fr(fv x) = x)) ==>
    (WORDLEN (GEN_WADD n w1 w2 m fv fr r c) =  SUC m)"
    INDUCT_TAC THEN GEN_TAC THEN REPEAT (RESQ_GEN_TAC THEN DISCH_TAC)
    THEN REPEAT STRIP_TAC THENL[

    COND_REWRITE1_TAC dthm1
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[WORDLEN_DEF;LENGTH];
    
    INDUCT_TAC THENL[
       REPEAT (RESQ_GEN_TAC THEN DISCH_TAC) THEN REPEAT STRIP_TAC 
       THEN RESQ_RES_TAC THEN ASSUME_TAC (SPEC_ALL LESS_EQ_0_lem) THEN RES_TAC
       THEN COND_REWRITE1_TAC dthm2
       THEN PURE_ONCE_REWRITE_TAC[LET_DEF]
       THEN CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV))
       THEN PURE_ONCE_REWRITE_TAC[GSYM PWORDLEN]

       THEN PURE_ONCE_ASM_REWRITE_TAC[]

let LESS_EQ_0_lem = PROVE("!m. 0 <= m",
    INDUCT_TAC THEN REWRITE_TAC[LESS_OR_EQ;LESS_0]);;


let PWORDLEN_SUC_WCAT = prove_thm(`PWORDLEN_SUC_WCAT`,
    "!n x. !w:(*)word. PWORDLEN n w ==> PWORDLEN (SUC n) (WCAT (w,WORD[x]))",
    let lem = CONV_RULE ((DEPTH_CONV RESQ_FORALL_CONV)
       THENC (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)) WORDLEN_WCAT in
    REPEAT GEN_TAC THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[ADD1]
    THEN IMP_RES_THEN MATCH_MP_TAC lem
    THEN CONV_TAC ((RATOR_CONV o RAND_CONV) num_CONV)
    THEN REWRITE_TAC[PWORDLEN_DEF;LENGTH]);;

    "!m n. !w1 w2:(*)word::PWORDLEN n. (n <= m) ==>
     !r fr fv. (!x:*. ((fv x) < r) /\ (fr(fv x) = x)) ==>
     (NVAL fv r (GEN_WADD n w1 w2 m fv fr r c) =
      ((NVAL fv r w1) + (NVAL fv r w2) + (fv c)))"
    let dthm1, dthm2 = 
    	let th1 = ((CONJ_PAIR o RESQ_SPEC_ALL o SPEC_ALL) GEN_WADD_DEF) in
        let fn = \th.(GEN_ALL o DISCH_ALL) th in
    	(fn # fn) th1 in
    INDUCT_TAC THEN GEN_TAC THEN REPEAT (RESQ_GEN_TAC THEN DISCH_TAC)
    THEN REPEAT STRIP_TAC THENL[

    COND_REWRITE1_TAC dthm1 THEN IMP_RES_THEN SUBST_ALL_TAC LESS_EQ_0_EQ
    THEN RESQ_IMP_RES_TAC NVAL_WORDLEN_0
    THEN PURE_ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN PURE_REWRITE_TAC[ADD_CLAUSES] THEN MATCH_ACCEPT_TAC NVAL1;

    COND_REWRITE1_TAC dthm2 THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    	    THEN PURE_ONCE_REWRITE_TAC[SUB_EQUAL_0]
    THEN PURE_ONCE_REWRITE_TAC[LET_DEF]
    THEN CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV))
