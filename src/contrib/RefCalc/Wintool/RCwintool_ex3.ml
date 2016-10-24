% File: winRC_keys.ml

  Use of the window inference tool

  Specification: "Produce N distinct numerical keys in a list"

  Final program: l:=[];
                 VAR c=0;
                  DO len(l) < N -> c,l:=c+1,c::l OD
                 END

%

% disable conjecture printing %
conj_print false;;

% state abbreviations %
let aty = ":num->bool";;
let cty = ":num";;
let sty = ":(num)list";;

% the specification %
let SPECIF = "nondass \l:^sty. \l':^sty.
     (LENGTH l' = N) /\
     (!j k. j<k /\ k<N ==> ~(EL j l' = EL k l'))";;

% Set up the initial specification %
BEGIN_STACK 
  `keys` 
  "(refines)
   (^SPECIF)"
  []
  [];;


% First refinement: implement by a loop %

% components of the loop block %
let initp = "\l':^sty. l' = []";;
let init = "nondass \l:^sty.^initp";;
let ainit = "\(a:^aty,l:^sty).a = \n.F";;
let agrd = "\(a:^aty,l:^sty). LENGTH l < N";;
let abody = "nondass \(a:^aty,l:^sty)(a',l').
      ?m. (l' = CONS m l) /\ ~ a m /\ (!n. a' n = a n \/ (n=m))";;

% invariant and bound function %
let inv = "\(a:^aty,l:^sty).
    (LENGTH l <= N) /\
    (!j k. j<k /\ k<(LENGTH l) ==> ~(EL j l = EL k l)) /\
    (!n. a n = ?k. k<LENGTH l /\ (n = EL k l))";;
let t = "\(a:^aty,l:^sty).N - (LENGTH l)";;

% Do the implementation (adds 3 proof obligations) %
SPEC_TO_LOOP_WIN initp ainit agrd abody inv t;;


% Prove verification conditions for first refinement %

% invariant initially established %
ESTABLISH (hd(hyp(WIN_THM())));;
goal (focus (TOP_WIN()));;
e(PORT[implies_DEF] THEN PBETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  ART[LENGTH;ZERO_LESS_EQ;NOT_LESS_0]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

% postcondition holds when leaving loop %
ESTABLISH (hd(hyp(WIN_THM())));;
goal (focus (TOP_WIN()));;
e(LPORT[implies_DEF;and_DEF;not_DEF;LESS_OR_EQ] THEN PBETA_TAC THEN 
  GEN_TAC THEN STRIP_TAC THEN ART[] THENL
  [RES_TAC
  ;POP_ASSUM (\t.ALL_TAC) THEN POP_ASSUM MP_TAC THEN ART[]
  ]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

% body preserves invariant and decreases termination function %
ESTABLISH (hd(hyp(WIN_THM())));;
let th0 = TAUT "~(t/\t') = t ==> ~t'";;
let th1 = mk_thm([],"!l:(*)list. EL(LENGTH l)(CONS x l) = x");;
let th2 = mk_thm([],"!l:(*)list. j < LENGTH l ==> (EL j(CONS x l) = EL j l)");;
let th3 = mk_thm([],"m < n ==> (n - SUC m) < n - m");;
goal (focus (TOP_WIN()));;
e(GEN_TAC THEN nondass_correct_TAC[] THEN P_PGEN_TAC "a:^aty,l:^sty" THEN
  PRT[and_DEF] THEN PBETA_TAC THEN RT[] THEN STRIP_TAC THEN 
  P_PGEN_TAC "a':^aty,l':^sty" THEN RT[] THEN STRIP_TAC THEN ART[LENGTH] THEN
  REPEAT CONJ_TAC THENL
  [IMP_RES_TAC LESS_OR
  ;PORT[LESS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC "j<k" THEN ART[th1] THEN
    DISCH_THEN (\t.PORT[MATCH_MP th2 t] THEN ASSUME_TAC t) THEN
    UNDISCH_TAC "~(a:^aty)m" THEN POART[] THEN
    CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN PORT[th0] THEN
    DISCH_TAC THEN PORT[EQ_SYM_EQ] THEN RES_TAC
   ;IMP_RES_TAC LESS_TRANS THEN IMP_RES_TAC th2 THEN ART[] THEN RES_TAC
   ]
  ;GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC "k:num" THEN ART[LESS_THM] THEN
    IMP_RES_TAC th2 THEN ART[]
   ;EXISTS_TAC "LENGTH(l:^sty)" THEN ART[LESS_SUC_REFL;th1]
   ;POP_ASSUM SUBST1_TAC THEN POP_ASSUM MP_TAC THEN PORT[LESS_THM] THEN
    REPEAT STRIP_TAC THEN ART[th1] THEN DISJ1_TAC THEN 
    EXISTS_TAC "k:num" THEN ART[] THEN IMP_RES_TAC th2 THEN ART[]
   ]
  ;EVERY_ASSUM(\t.PORT[PORR[EQ_SYM_EQ]t]) THEN IMP_RES_TAC th3
  ]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

% first refinement theorem proved %
WIN_THM();;


% Second refinement: do data refinement of loop %

% abstraction relation used %
let absrel = "\(a,k,l:^sty). (!n. a n ==> n < k)";;

% do data refinement of the block %
OPEN_WIN[RAND];;
BLOCK_DR_WIN absrel;;

% rewrite initialisation, calculational style %
OPEN_WIN [RATOR;RAND];;
REWRITE_WIN[abst_DEF];;
PURE_ONCE_REWRITE_WIN[CONJ_SYM];;
CONVERT_WIN (DEPTH_CONV PBETA_CONV);;
CONVERT_WIN (DEPTH_CONV EX_1PT_CONV);;
CONVERT_WIN (DEPTH_CONV BETA_CONV);;
let thm = prove("(\(k:*,u:**). T) = true",
     PORT[true_DEF] THEN CONV_TAC FUN_EQ_CONV THEN PBETA_TAC THEN RT[]);;
REWRITE_WIN[thm];;
CLOSE_WIN();;

% data refinement of iteration (adds a proof obligation) %
OPEN_WIN[RAND];;
DO_DR_WIN();;

% rewrite guard %
OPEN_WIN[RATOR;RAND];;
REWRITE_WIN[abst_DEF];;
CONVERT_WIN(DEPTH_CONV PBETA_CONV);;
CONVERT_WIN(DEPTH_CONV EXISTS_AND_CONV);;
let th = prove("?a. !n. a n ==> n < c",
  EXISTS_TAC "\n:num.F" THEN BETA_TAC THEN RT[]);;
REWRITE_WIN[th];;
CLOSE_WIN();;

% data refinement of iteration body (adds 1 proof obligation) %
OPEN_WIN[RAND];;
NONDASS_DR_WIN "\(k,l)(k',l'). (k < k') /\ (l' = CONS k l)";; 
CLOSE_WIN();;

% close windows opened earlier %
CLOSE_WIN();;
CLOSE_WIN();;


% Prove verification conditions for second refinement %

% nondass simulation condition %
ESTABLISH (hd(hyp(WIN_THM())));;
goal (focus (TOP_WIN()));;
e(REPEAT STRIP_TAC THEN ART[CONS_11] THEN 
  EXISTS_TAC "\n:num. a n \/ (n=k)" THEN BETA_TAC THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN IMP_RES_TAC LESS_TRANS
  ;EXISTS_TAC "k:num" THEN RT[] THEN DISCH_TAC THEN RES_TAC THEN
   ASSUME_TAC LESS_REFL THEN RES_TAC
  ]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

% guard condition for iteration %
ESTABLISH (hd(hyp(WIN_THM())));;
goal (focus (TOP_WIN()));;
e(REPEAT STRIP_TAC THEN ART[]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

% Look at new theorem %
WIN_THM();;


% Last refinement step: make the whole thing deteministic %

% Make initial nondass into assign (adds 1 proof obligation) %
OPEN_WIN[RATOR;RAND];;
C_MATCH_TRANSFORM_WIN (ISPEC"\l:(num)list.([]:(num)list)" nondass_to_assign);;
CLOSE_WIN();;

% Make initialisation of block deterministic %
OPEN_WIN[RAND;RATOR;RAND];;
let th1 = prove("!p:^pred. p implies true",PRED_TAUT_TAC);;
TRANSFORM_WIN (ISPEC "\(k,l:(num)list). k=0" th1);;
CLOSE_WIN();;

% Make nondass of loop body into assign (adds 1 proof obligation) %
OPEN_WIN[RAND;RAND;RAND];;
C_MATCH_TRANSFORM_WIN (ISPEC "\(k,l).(SUC k,CONS k l)" nondass_to_assign);;
CLOSE_WIN();;


% Prove remaining proof obligations %

% obligation from initialisation %
ESTABLISH (hd(hyp(WIN_THM())));;
REWRITE_WIN[LESS_SUC_REFL];;
CLOSE_WIN();;

% obligation from loop body %
ESTABLISH (hd(hyp(WIN_THM())));;
REWRITE_WIN[];;
CLOSE_WIN();;


% Finished: %
% final refinement result :
|- ((assign(\l. [])) seq
    (block (\(c,u). c = 0)
           (do (\(c,u).(LENGTH u) < N)
               (assign(\(c,l). (SUC c,CONS c l))))))
   refines
   (nondass (\l l'.(LENGTH l'=N) /\ (!j k. j<k /\ k<N ==> ~(EL j l'=EL k l'))))
%
WIN_THM();;
END_STACK `keys` ;;
