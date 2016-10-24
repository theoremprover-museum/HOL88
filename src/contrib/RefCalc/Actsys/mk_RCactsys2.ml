% File: mk_RCactsys2.ml
   Action systems: theorems
%


% --- auxiliary facts --- %

let EVERY2 = prove
 ("(!(P:*->**->bool). EVERY2 P [] [] = T) /\
   (!(P:*->**->bool) x xl y yl.
        EVERY2 P (CONS x xl) (CONS y yl) = P x y /\ EVERY2 P xl yl)",
  REWRITE_TAC[EVERY2_DEF;HD;TL]);;

let EVERY2_MAP = prove
 ("!l1 l2 P (f:*1->*3) (g:*2->*4). (LENGTH l1 = LENGTH l2)
   ==> (EVERY2 P (MAP f l1) (MAP g l2) = EVERY2 (\x y. P (f x) (g y)) l1 l2)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LRT[MAP;EVERY2_DEF]
  ;REPEAT GEN_TAC THEN CASE_TAC "l2:(*2)list" list_CASES [LENGTH;NOT_SUC] THEN
   LPORT[INV_SUC_EQ;MAP;EVERY2] THEN DISCH_TAC THEN RES_TAC THEN
   BETA_TAC THEN ART[]
  ]);;

let if2_reduce = prove
  ("if2(g1,(c1:^ptrans12))(g2,c2) =
    (assert (g1 or g2)) seq (((guard g1) seq c1) dch ((guard g2) seq c2))",
   FUN_TAC THEN LPORT[if2_DEF;seq_DEF;dch_DEF;seq_DEF;guard_DEF;assert_DEF]
   THEN REFL_TAC);;

let lif_reduce =
 let thm1 = prove
  ("!al:^actlist. ldch (MAP (\(g,c). (guard g) seq c) al)
    = (guard(lguard al)) seq (ldch (MAP (\(g,c). (guard g) seq c) al))",
   INDUCT_THEN list_INDUCT ASSUME_TAC THENL
   [LPORT[MAP;lguard_DEF;ldch_DEF] THEN FUN_TAC THEN
    LPORT[seq_DEF;guard_DEF;magic_DEF] THEN PRED_TAUT_TAC
   ;P_PGEN_TAC "(g,c):^action" THEN LPORT[MAP;lguard_DEF;ldch_DEF] THEN
    PBETA_TAC THEN RT[] THEN POP_ASSUM SUBST1_TAC THEN
    FUN_TAC THEN RT[seq_DEF;dch_DEF;guard_DEF] THEN PRED_TAUT_TAC
   ]) in
 prove
  ("!(al:^actlist). lif al = (assert (lguard al)) seq
         (ldch (MAP (\(g,c). (guard g) seq c) al))",
   INDUCT_THEN list_INDUCT ASSUME_TAC THENL
   [LPORT[MAP;lif_DEF;lguard_DEF;ldch_DEF] THEN FUN_TAC THEN
    LPORT[seq_DEF;assert_DEF;magic_DEF;abort_DEF] THEN PRED_TAUT_TAC
   ;P_PGEN_TAC "(g,c):^action" THEN LPORT[lif_DEF;lguard_DEF;MAP;ldch_DEF] THEN
    PBETA_TAC THEN RT[] THEN PORT[if2_reduce] THEN
    POP_ASSUM SUBST1_TAC THEN PORT[thm1] THEN
    FUN_TAC THEN RT[seq_DEF;dch_DEF;assert_DEF;guard_DEF] THEN PRED_TAUT_TAC
   ]);;

% --- healthiness properties of actsys-commands --- %

let mono_magic = prove
 ("monotonic (magic:^ptrans12)",
  LPORT[monotonic_DEF;magic_DEF;implies_DEF] THEN RT[]);;

let mono_guard = prove
 ("!g:^pred. monotonic (guard g)",
  LPORT[monotonic_DEF;guard_DEF;implies_DEF;imp_DEF] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;

let mono_if2 = prove
 ("!g1 (c1:^ptrans12) g2 c2.
       monotonic c1 /\ monotonic c2 ==> monotonic (if2(g1,c1)(g2,c2))",
  LRT[monotonic_DEF;if2_DEF;implies_DEF;imp_DEF;and_DEF;or_DEF;not_DEF] THEN
  SUPER_TAC);;

let mono_lif = prove
 ("!al:^actlist. EVERY monotonic (MAP SND al) ==> monotonic (lif al)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
  ART[MAP;EVERY_DEF;lif_DEF;mono_abort] THEN
  P_PGEN_TAC "g:^pred,c:^ptrans" THEN RT[] THEN STRIP_TAC THEN
  MATCH_MP_TAC mono_if2 THEN RES_TAC THEN ART[]);;

let mono_ldo = prove
 ("!al:^actlist. EVERY monotonic (MAP SND al) ==> monotonic (ldo al)",
  REPEAT STRIP_TAC THEN PORT[ldo_DEF] THEN MATCH_MP_TAC mono_do THEN
  IMP_RES_TAC mono_lif);;


% --- correctness of actsys-commands --- %

let correct_if2 = prove
 ("!p g1 (c1:^ptrans12) g2 c2 q.
    correct (g1 andd p) c1 q /\ correct (g2 andd p) c2 q
     ==> correct ((g1 or g2) andd p) (if2(g1,c1)(g2,c2)) q",
  LPRT[correct_DEF;if2_DEF;implies_DEF;imp_DEF;and_DEF;or_DEF;not_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;

let correct_ldo = 
 let thm1 = prove
      ("(p1:^pred)andd p2 andd p3 = p2 andd p1 andd p3",PRED_TAUT_TAC) in
 prove
  ("!(al:^actlist) inv t p q.
        EVERY monotonic (MAP SND al) /\
        p implies inv /\
        ((not (lguard al)) andd inv) implies q /\
        EVERY (\(g,c). !x. correct (inv andd (g andd (\s. t s = x)))
                                   c
                                   (inv andd (\s. (t s) < x)))al
        ==> correct p(ldo al)q",
   REPEAT STRIP_TAC THEN PORT[ldo_DEF] THEN MATCH_MP_TAC correct_do THEN
   EXISTS_TAC "inv:^pred" THEN EXISTS_TAC "t:^state->num" THEN ART[] THEN
   CONJ_TAC THENL
   [IMP_RES_TAC mono_lif
   ;POP_ASSUM MP_TAC THEN SPEC_TAC("al:^actlist","al:^actlist") THEN
    INDUCT_THEN list_INDUCT ASSUME_TAC THENL
    [LRT[EVERY_DEF;lguard_DEF;lif_DEF;correct_DEF;abort_DEF] THEN PRED_TAUT_TAC
    ;LRT[EVERY_DEF;lguard_DEF;lif_DEF] THEN
     P_PGEN_TAC "g:^pred,c:^ptrans" THEN PBETA_TAC THEN RT[] THEN
     STRIP_TAC THEN RES_TAC THEN GEN_TAC THEN PORT[thm1] THEN
     MATCH_MP_TAC correct_if2 THEN PORT[thm1] THEN ART[]
   ]]);;

let correct_ldo_wellf = 
 let thm1 = prove
      ("(p1:^pred)andd p2 andd p3 = p2 andd p1 andd p3",PRED_TAUT_TAC) in
 prove
  ("!(al:^actlist) inv (po:*->*->bool) t p q.
        EVERY monotonic (MAP SND al) /\
        wellf po /\
        p implies inv /\
        ((not (lguard al)) andd inv) implies q /\
        EVERY (\(g,c). !x. correct (inv andd (g andd (\s. t s = x)))
                                   c
                                   (inv andd (\s. po (t s) x)))al
        ==> correct p(ldo al)q",
   REPEAT STRIP_TAC THEN PORT[ldo_DEF] THEN MATCH_MP_TAC correct_do_wellf THEN
   EXISTS_TAC "po:*->*->bool" THEN EXISTS_TAC "inv:^pred" THEN 
   EXISTS_TAC "t:^state->*" THEN ART[] THEN
   CONJ_TAC THENL
   [IMP_RES_TAC mono_lif
   ;POP_ASSUM MP_TAC THEN SPEC_TAC("al:^actlist","al:^actlist") THEN
    INDUCT_THEN list_INDUCT ASSUME_TAC THENL
    [LRT[EVERY_DEF;lguard_DEF;lif_DEF;correct_DEF;abort_DEF] THEN PRED_TAUT_TAC
    ;LRT[EVERY_DEF;lguard_DEF;lif_DEF] THEN
     P_PGEN_TAC "g:^pred,c:^ptrans" THEN PBETA_TAC THEN RT[] THEN
     STRIP_TAC THEN RES_TAC THEN GEN_TAC THEN PORT[thm1] THEN
     MATCH_MP_TAC correct_if2 THEN PORT[thm1] THEN ART[]
   ]]);;


% --- data refinement of actsys-commands --- %

let dch_dataref = prove
  ("dataref (r:^arel) c1 c1' /\ dataref r c2 c2' ==>
        dataref r (c1 dch c2) (c1' dch c2')",
   LPORT[dataref_DEF;ref_DEF;seq_DEF;dch_DEF;abst_DEF;implies_DEF;and_DEF] THEN
   PBETA_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "a:*a" THEN ART[]
   ;FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "a:*a" THEN ART[]
   ]);;

let magic_dataref = prove
 ("dataref (r:^arel) magic magic",
  LRT[dataref_DEF;ref_DEF;seq_DEF;magic_DEF] THEN PRED_TAUT_TAC);;

let th1 = prove
 ("dataref (r:^arel) c magic",
  LRT[dataref_DEF;ref_DEF;seq_DEF;magic_DEF] THEN PRED_TAUT_TAC);;
let ldch_dataref = prove
  ("!cl' cl (r:^arel).
     (LENGTH cl = LENGTH cl') /\ EVERY2 (\c c'. dataref (r:^arel) c c') cl cl'
       ==> dataref r (ldch cl) (ldch cl')",
   INDUCT_THEN list_INDUCT ASSUME_TAC THENL
   [LRT[ldch_DEF;th1]
   ;REPEAT GEN_TAC THEN 
    CASE_TAC "cl:(^aptrans)list" list_CASES [LENGTH;GSYM NOT_SUC] THEN
    LPORT[INV_SUC_EQ;EVERY2;ldch_DEF] THEN BETA_TAC THEN
    STRIP_TAC THEN RES_TAC THEN MATCH_MP_TAC dch_dataref THEN ART[]
   ]);;

let assert_dataref = prove
 ("(!a k u. (r:^arel)(a,k,u) /\ g(a,u) ==> g'(k,u))
        ==> dataref r (assert g) (assert g')",
  LPORT[dataref_DEF;ref_DEF;seq_DEF;abst_DEF;assert_DEF;and_DEF;implies_DEF]
  THEN BETA_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN PBETA_TAC THEN 
  STRIP_TAC THEN CONJ_TAC THENL
  [ASSUM_LIST(\l.MATCH_MP_TAC
     (RR[](SPECL["a:*a";"FST(v:*c#*s)";"SND(v:*c#*s)"](el 4 l)))) THEN ART[]
  ;EXISTS_TAC "a:*a" THEN ART[]
  ]);;

let guard_dataref = prove
  ("(!a k u. r(a,k,u) /\ b'(k,u) ==> b(a,u))
        ==> dataref (r:^arel) (guard b) (guard b')",
   LPORT[dataref_DEF;ref_DEF;seq_DEF;guard_DEF;implies_DEF;abst_DEF;
         imp_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN 
   EXISTS_TAC "a:*a" THEN ART[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "FST(u:*c#*s)" THEN ART[]);;

let if2_dataref = 
 let thm1 = prove
 ("(guard g) seq (c:^ptrans12) = (guard g) seq (guard g) seq c",
  FUN_TAC THEN LPRT[seq_DEF;guard_DEF] THEN PRED_TAUT_TAC) in
 prove
  ("!g1 c1 g2 c2 (r:^arel). monotonic c1' /\ monotonic c2'
      /\ dataref r c1 ((guard g1')seq c1') /\ dataref r c2 ((guard g2')seq c2')
      /\ (!a k u. r(a,k,u) /\ g1'(k,u) ==> g1(a,u))
      /\ (!a k u. r(a,k,u) /\ g2'(k,u) ==> g2(a,u))
      /\ (!a k u. r(a,k,u) /\ (g1(a,u) \/ g2(a,u)) ==> g1'(k,u) \/ g2'(k,u))
      ==> dataref r (if2(g1,c1)(g2,c2)) (if2(g1',c1')(g2',c2'))",
   REPEAT STRIP_TAC THEN PORT[if2_reduce] THEN
   MATCH_MP_TAC seq_dataref THEN RT[mono_assert] THEN CONJ_TAC THENL
   [MATCH_MP_TAC assert_dataref THEN PORT[or_DEF] THEN BETA_TAC
    THEN POP_ASSUM ACCEPT_TAC
   ;MATCH_MP_TAC dch_dataref THEN CONJ_TAC THENL
    [CONV_TAC(RAND_CONV(PURE_ONCE_REWRITE_CONV[thm1])) THEN
     MATCH_MP_TAC seq_dataref THEN ART[mono_guard] THEN
     MATCH_MP_TAC guard_dataref THEN FIRST_ASSUM MATCH_ACCEPT_TAC
    ;CONV_TAC(RAND_CONV(PURE_ONCE_REWRITE_CONV[thm1])) THEN
     MATCH_MP_TAC seq_dataref THEN ART[mono_guard] THEN
     MATCH_MP_TAC guard_dataref THEN FIRST_ASSUM MATCH_ACCEPT_TAC
   ]]);;

let lemma = 
 let thm1 = prove
  ("(guard g) seq (c:^ptrans12) = (guard g) seq (guard g) seq c",
   FUN_TAC THEN LPRT[seq_DEF;guard_DEF] THEN PRED_TAUT_TAC) in
 prove
 ("!al al' (r:^arel). (LENGTH al=LENGTH al')
    /\ EVERY2 (\(g,c)(g',c'). dataref r c((guard g') seq c')) al al'
    /\ EVERY2 (\(g,c)(g',c'). (!a k u. r(a,k,u) /\ g'(k,u) ==> g(a,u))) al al'
    ==> EVERY2 (\(g,c)(g',c').
                dataref r ((guard g) seq c) ((guard g') seq c')) al al'",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   CASE_TAC "al':^cactlist" list_CASES [LENGTH;GSYM NOT_SUC;MAP;EVERY2]
  ;P_PGEN_TAC "(g,c):^aaction" THEN REPEAT GEN_TAC THEN
   CASE_TAC "al':^cactlist" list_CASES [LENGTH;NOT_SUC;MAP;EVERY2] THEN
   SPEC_TAC("h:^caction","h:^caction") THEN P_PGEN_TAC"(g',c'):^caction" THEN
   PBETA_TAC THEN RT[INV_SUC_EQ] THEN STRIP_TAC THEN RES_TAC THEN ART[] THEN
   CONV_TAC(RAND_CONV(PURE_ONCE_REWRITE_CONV[thm1])) THEN
   MATCH_MP_TAC seq_dataref THEN ART[mono_guard] THEN
   MATCH_MP_TAC guard_dataref THEN FIRST_ASSUM MATCH_ACCEPT_TAC
  ]);;
let lif_dataref = prove
  ("!al' al (r:^arel). EVERY monotonic (MAP SND al') /\ (LENGTH al=LENGTH al')
     /\ EVERY2 (\(g,c)(g',c'). dataref r c((guard g') seq c')) al al'
     /\ EVERY2 (\(g,c)(g',c'). (!a k u. r(a,k,u) /\ g'(k,u) ==> g(a,u))) al al'
     /\ (!a k u. r(a,k,u) /\ (lguard al)(a,u) ==> (lguard al')(k,u))
     ==> dataref r (lif al) (lif al')",
   REPEAT STRIP_TAC THEN PORT[lif_reduce] THEN
   MATCH_MP_TAC seq_dataref THEN RT[mono_assert] THEN CONJ_TAC THENL
   [MATCH_MP_TAC assert_dataref THEN FIRST_ASSUM ACCEPT_TAC
   ;MATCH_MP_TAC ldch_dataref THEN ART[LENGTH_MAP] THEN
    IMP_RES_TAC (INST_TYPE[aptrans,":*3";cptrans,":*4"]EVERY2_MAP) THEN
    POP_ASSUM MATCH_MP_TAC THEN PBETA_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV(PALPHA_CONV"(g,c):^aaction")) THEN
    CONV_TAC(ONCE_DEPTH_CONV(PALPHA_CONV"(g',c'):^caction")) THEN
    RT[] THEN MATCH_MP_TAC lemma THEN ART[]
   ]);;

let ldo_dataref = prove
  ("!al' al (r:^arel). EVERY monotonic (MAP SND al') /\ (LENGTH al=LENGTH al')
     /\ EVERY2 (\(g,c)(g',c'). dataref r c ((guard g') seq c')) al al'
     /\ EVERY2 (\(g,c)(g',c'). !a k u. r(a,k,u) /\ g'(k,u) ==> g(a,u)) al al'
     /\ (!a k u. r(a,k,u) /\ (lguard al)(a,u) ==> (lguard al')(k,u))
     ==> dataref r (ldo al) (ldo al')",
   REPEAT STRIP_TAC THEN PORT[ldo_DEF] THEN
   MATCH_MP_TAC do_dataref THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC mono_lif THEN ART[]
   ;MATCH_MP_TAC lif_dataref THEN ART[]
   ;REPEAT STRIP_TAC THEN EQ_TAC THEN RES_TAC THEN
    ASSUM_LIST(\l.MP_TAC(el 4 l) THEN MP_TAC(el 6 l)) THEN 
    SPEC_TAC("al':^cactlist","al':^cactlist") THEN
    SPEC_TAC("al:^aactlist","al:^aactlist") THEN
    INDUCT_THEN list_INDUCT ASSUME_TAC THENL
    [GEN_TAC THEN CASE_TAC "al'':^cactlist" list_CASES 
                   [LENGTH;lguard_DEF;GSYM NOT_SUC;EVERY2] THEN
     PORT[false_DEF] THEN BETA_TAC THEN RT[]
    ;REPEAT GEN_TAC THEN CASE_TAC "al''':^cactlist" list_CASES 
                   [LENGTH;lguard_DEF;NOT_SUC;EVERY2] THEN
     LRT[INV_SUC_EQ;or_DEF] THEN PBETA_TAC THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
   ]]);;

let actsys_dataref = prove
  ("!p p' al al' (r:^arel). (LENGTH al = LENGTH al')
     /\ EVERY monotonic (MAP SND al')
     /\ (!k u. p'(k,u) ==> ?a. r(a,k,u) /\ p(a,u))
     /\ EVERY2 (\(g,c)(g',c'). dataref r c ((guard g') seq c')) al al'
     /\ EVERY2 (\(g,c)(g',c'). (!a k u. r(a,k,u) /\ g'(k,u) ==> g(a,u))) al al'
     /\ (!a k u. r(a,k,u) /\ (lguard al)(a,u) ==> (lguard al')(k,u))
     ==> (block p (ldo al)) ref (block p' (ldo al'))",
   REPEAT STRIP_TAC THEN MATCH_MP_TAC block_dataref THEN
   EXISTS_TAC "r:^arel" THEN ART[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC mono_ldo THEN FIRST_ASSUM ACCEPT_TAC
   ;MATCH_MP_TAC ldo_dataref THEN ART[]
   ]);;

save_thm(`EVERY2`,EVERY2);;
save_thm(`EVERY2_MAP`,EVERY2_MAP);;
save_thm(`if2_reduce`,if2_reduce);;
save_thm(`lif_reduce`,lif_reduce);;
save_thm(`mono_magic`,mono_magic);;
save_thm(`mono_guard`,mono_guard);;
save_thm(`mono_if2`,mono_if2);;
save_thm(`mono_lif`,mono_lif);;
save_thm(`mono_ldo`,mono_ldo);;
save_thm(`correct_if2`,correct_if2);;
save_thm(`correct_ldo`,correct_ldo);;
save_thm(`correct_ldo_wellf`,correct_ldo_wellf);;
save_thm(`abort_dataref`,abort_dataref);;
save_thm(`magic_dataref`,magic_dataref);;
save_thm(`ldch_dataref`,ldch_dataref);;
save_thm(`assert_dataref`,assert_dataref);;
save_thm(`dch_dataref`,dch_dataref);;
save_thm(`lif_dataref`,lif_dataref);;
save_thm(`ldo_dataref`,ldo_dataref);;
save_thm(`actsys_dataref`,actsys_dataref);;
