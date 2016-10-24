% HOL version of the multiplier example from the LCF_LSM paper.
  Load into HOL after first doing:

   del prims.th
   del MULT_IMP.th
   del MULT_VER.th
 %

% Modified to load unwinding rules. (TFM 88.04.20)			%
% Modified to load library unwind.  (MJCG 27 march 1989)		%

loadf `unwind`;;

timer true;;

set_flag(`compile_on_the_fly`, true);;

new_theory `prims`;;

new_proof_file`prims.prf`;;

let time = ":num";;

let sig = ":^time -> bool"
and bus = ":^time -> num";;

begin_proof`prims`;;

map
 new_definition
 [`MUX`      , "MUX(switch,i1:^bus,i2:^bus,out) =
                !x:^time. out x = (switch x => i1 x | i2 x)";
  `REG`      , "REG(i:^bus,out) = 
                !x:^time. out(x+1) = i x";
  `FLIPFLOP` , "FLIPFLOP(i:^sig,out) = 
                !x:^time. out(x+1) = i x";
  `DEC`      , "DEC(i,out) = 
                !x:^time. out x = (i x - 1)";
  `ADDER`    , "ADDER(i1,i2,out) =
                !x:^time. out x = (i1 x + i2 x)";
  `ZERO_TEST`, "ZERO_TEST(i,out) =
                !x:^time. out x = (i x = 0)";
  `OR_GATE`  , "OR_GATE(i1,i2,out) =
                !x:^time. out x = (i1 x \/ i2 x)";
  `ZERO`     , "ZERO(out) =
                !x:^time. out x = 0"];;

end_proof();;
close_proof_file();;

close_theory();;

new_theory `MULT_IMP`;;

new_parent`prims`;;

new_proof_file`MULT_IMP.prf`;;
begin_proof`MULT_IMP`;;

new_definition
 (`MULT_IMP`,
  "MULT_IMP(i1,i2,o1,o2,done) =
    ?b1 b2 b3 b4 l1 l2 l3 l4 l5 l6 l7 l8 l9.
       MUX(done,l8,l7,l6) /\
       REG(l6,o2)         /\
       ADDER(l8,o2,l7)    /\
       DEC(i1,l5)         /\
       MUX(done,l5,l3,l4) /\
       MUX(done,i1,l2,l1) /\
       REG(l1,o1)         /\
       DEC(o1,l2)         /\
       DEC(l2,l3)         /\
       ZERO(l9)           /\
       MUX(b4,l9,i2,l8)   /\
       ZERO_TEST(i1,b4)   /\
       ZERO_TEST(l4,b1)   /\
       ZERO_TEST(i2,b2)   /\
       OR_GATE(b1,b2,b3)  /\
       FLIPFLOP(b3,done)");;

end_proof();;
close_proof_file();;

close_theory();;

new_theory`MULT_VER`;;

new_parent `MULT_IMP`;;
new_parent `MULT_FUN`;;
new_parent `NEXT`;;

new_proof_file`MULT_VER.prf`;;
begin_proof`prims`;;
let prims =
 map
  (definition `prims`)
     [`MUX`;`REG`;`FLIPFLOP`;`DEC`;`ADDER`;`ZERO_TEST`;`ZERO`;`OR_GATE`];;

let MULT_IMP = definition `MULT_IMP` `MULT_IMP`;;

let MULT_IMP_UNFOLD = 
 save_thm(`MULT_IMP_UNFOLD`, UNFOLD_RULE prims MULT_IMP);;

let MULT_IMP_UNWIND = 
 save_thm(`MULT_IMP_UNWIND`, UNWINDF_RULE MULT_IMP_UNFOLD);;

let MULT_IMP_PRUNE = 
 save_thm(`MULT_IMP_PRUNE`, PRUNEF_RULE MULT_IMP_UNWIND);;

let MULT_IMP_EXPAND = save_thm(`MULT_IMP_EXPAND`, EXPANDF prims MULT_IMP);;

let MULT_FUN_T = theorem `MULT_FUN` `MULT_FUN_T`
and MULT_FUN_F = theorem `MULT_FUN` `MULT_FUN_F`;;
end_proof();;

let COND_ADD_LEMMA =
 prove_thm
  (`COND_ADD_LEMMA`,
   "(b => m | n) + p = (b => m + p | n + p)",
   COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]);;

let MULT_FUN_EXPANDED_DEF =
 prove_thm
  (`MULT_FUN_EXPANDED_DEF`,
   "!i1 i2 m n t.
     MULT_FUN((i1,i2),m,n,t) =
      (t =>
       (m,n,t) |
       MULT_FUN
        ((i1, i2),
         (t => ((i1 = 0) => 0 | i2) | ((i1 = 0) => 0 | i2) + m),
         (t => i1 | n - 1),
         (((t => i1 - 1 | (n - 1) - 1) = 0) \/ (i2 = 0))))",
    REPEAT GEN_TAC
     THEN ASM_CASES_TAC "t:bool"
     THEN ASM_REWRITE_TAC
           [MULT_FUN_T;MULT_FUN_F;COND_ADD_LEMMA;ADD_CLAUSES]);;

begin_proof`G_FUN`;;
let G_FUN = 
 new_definition
  (`G_FUN`,
   "!i1 i2 m n t.
     G_FUN((i1,i2),(m,n,t)) =
      ((t => ((i1 = 0) => 0 | i2) | ((i1 = 0) => 0 | i2) + m),
       (t => i1 | n - 1),
       (((t => i1 - 1 | (n - 1) - 1) = 0) \/ (i2 = 0)))");;
end_proof();;

begin_proof`NEXT_MULT_LEMMA1`;;
let NEXT_MULT_LEMMA1 =
 save_thm
  (`NEXT_MULT_LEMMA1`,
    let NEXT_THM = theorem `NEXT` `NEXT_THM` in
   REWRITE_RULE
    []
    (CONV_RULE
     (DEPTH_CONV BETA_CONV)
     (SPECL
      ["MULT_FUN";
       "\x:num#num#bool.SND(SND x)";
       "G_FUN";
       "done:num->bool";
       "\x. ((i1:num->num) x, (i2:num->num) x)";
       "\x. ((o2:num->num) x, (o1:num->num) x, (done:num->bool) x)"]
      (INST_TYPE[":num#num",":*";":num#num#bool",":**"]NEXT_THM))));;
end_proof();;

let NEXT_MULT_LEMMA2 =
 prove_thm
  (`NEXT_MULT_LEMMA2`,
   "MULT_IMP(i1,i2,o1,o2,done) ==>
    (!x.
      o2(x + 1),o1(x + 1),done(x + 1) =
      G_FUN((i1 x,i2 x),o2 x,o1 x,done x))",
    let MULT_IMP_EXPAND = theorem `MULT_VER` `MULT_IMP_EXPAND` in
   REWRITE_TAC[MULT_IMP_EXPAND]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[G_FUN]);;

begin_proof`G_FUN_LEMMA`;;
let G_FUN_LEMMA =
 save_thm
  (`G_FUN_LEMMA`,
   PURE_REWRITE_RULE
    [PAIR]
    (SPECL
     ["FST(a:num#num)";
      "SND(a:num#num)";
      "FST(b:num#num#bool)";
      "FST(SND(b:num#num#bool))";
      "SND(SND(b:num#num#bool))"]
     G_FUN));;
end_proof();;

begin_proof`NEXT_MULT_LEMMA3`;;
let NEXT_MULT_LEMMA3 =
 save_thm
  (`NEXT_MULT_LEMMA3`,
   PURE_REWRITE_RULE
    [PAIR;SYM G_FUN_LEMMA]
    (SPECL
     ["FST(a:num#num)";
      "SND(a:num#num)";
      "FST(b:num#num#bool)";
      "FST(SND(b:num#num#bool))";
      "SND(SND(b:num#num#bool))"]
     MULT_FUN_EXPANDED_DEF));;
end_proof();;

begin_proof`NEXT_MULT_LEMMA4`;;
let NEXT_MULT_LEMMA4 =
 save_thm
  (`NEXT_MULT_LEMMA4`,
   DISCH_ALL
    (REWRITE_RULE
     [UNDISCH NEXT_MULT_LEMMA2;SYM NEXT_MULT_LEMMA3]
     NEXT_MULT_LEMMA1));;
end_proof();;


let MULT_FUN_LEMMA2 =
 prove_thm
  (`MULT_FUN_LEMMA2`,
   "(done:^sig) x ==>
     (MULT_FUN((i1 x,i2 x),G_FUN((i1 x,i2 x),o2 x,o1 x,done x)) =
      (i1 x * i2 x, ((((i1 x - 1) = 0) \/ (i2 x = 0)) => i1 x | 1), T))",
    let MULT_FUN_LEMMA1 = theorem `MULT_FUN` `MULT_FUN_LEMMA` in
   DISCH_TAC
    THEN ASM_REWRITE_TAC[MULT_FUN_LEMMA1;G_FUN]);;

let PAIR_SPLIT =
 prove_thm
  (`PAIR_SPLIT`,
   "!x1:*.!y1:**.!x2 y2.
     ((x1,y1) = (x2,y2)) = (x1 = x2) /\ (y1 = y2)",
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN ASSUME_TAC
          (REWRITE_RULE
            []
            (AP_TERM "FST:*#**->*"  (ASSUME "(x1:*,y1:**) = (x2,y2)")))
    THEN ASSUME_TAC
          (REWRITE_RULE
            []
            (AP_TERM "SND:*#**->**"  (ASSUME "(x1:*,y1:**) = (x2,y2)")))
    THEN ASM_REWRITE_TAC[]);;


let MULT_CORRECTNESS =
 prove_thm
  (`MULT_CORRECTNESS`,
   "MULT_IMP(i1,i2,o1,o2,done)        /\
    NEXT(x,x + d)done                 /\
    STABLE(x,x + d)(\x'. i1 x',i2 x') /\
    done x                            ==>
    (o2(x + d) = (i1 x) * (i2 x))",
    let NEXT_MULT_LEMMA4 = theorem `MULT_VER` `NEXT_MULT_LEMMA4`
    and MULT_FUN_LEMMA2  = theorem `MULT_VER` `MULT_FUN_LEMMA2`
    and PAIR_SPLIT       = theorem `MULT_VER` `PAIR_SPLIT` in
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC NEXT_MULT_LEMMA4
    THEN ASSUME_TAC (UNDISCH MULT_FUN_LEMMA2)
    THEN IMP_RES_TAC EQ_TRANS
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL PAIR_SPLIT))));;

close_proof_file();;

quit();;
