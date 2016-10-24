% File: mk_RCwintool2.ml

  Ordinary refinement rules intended for use in window inference
%


% --- Refinement equivalences used for rewriting --- %



let th0 = prove("t==>t'==>t'' = t/\t'==>t''",TAUT_TAC);;
let th1 = CONV_RULE(REDEPTH_CONV RIGHT_AND_EXISTS_CONV) correct_do;;
let th2 = CONV_RULE(REDEPTH_CONV LEFT_IMP_EXISTS_CONV) th1;;
let th3 = PORR[th0] impl_nondass;;
let spec_to_loop = prove
 ("!p0 q g (c:^eptrans) inv t p.
       monotonic c 
   ==> (\(x,u). p0 u /\ q(x,u)) implies inv
   ==> ((not g) andd inv) implies (\(x,u). p u)
   ==> (!x.correct (inv andd (g andd (\s.t s=x))) c (inv andd (\s.(t s)<x)))
   ==> ((nondass \u u'. p0 u') seq (block q (do g c )))
       refines (nondass \u:*s. \u':*s. p u')",
  REPEAT STRIP_TAC THEN ASSUM_LIST(\[t1;t2;t3;t4].
    ASSUME_TAC(MATCH_MP th2 (CONJ t4(CONJ t3(CONJ t2 t1))))) THEN
  PORT[refines_DEF] THEN MATCH_MP_TAC th3 THEN CONJ_TAC THENL
  [MATCH_MP_TAC mono_seq THEN RT[mono_nondass] THEN
   MATCH_MP_TAC mono_block THEN RT[mono_nondass] THEN
   MATCH_MP_TAC mono_do THEN ART[]
  ;GEN_TAC THEN POP_ASSUM MP_TAC THEN PORT[correct_DEF] THEN BETA_TAC THEN
   LPORT[seq_DEF;block_DEF;nondass_DEF;implies_DEF] THEN PBETA_TAC THEN
   STRIP_TAC THEN CONV_TAC FORALL_1PT_CONV THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ART[]
  ]);;


% --- refinement rules for assertions --- %

% Add assertion (general rule) %
let add_assert = prove
 ("!p. !c:^ptrans12. conjunctive c /\  (c p = true)
          ==> (c seq (assert p)) refines c",
  REPEAT STRIP_TAC THEN IMP_RES_TAC conj_biconj THEN 
  REPEAT (POP_ASSUM MP_TAC) THEN LPORT[biconjunctive_DEF;refines_DEF;ref_DEF;
     seq_DEF;assert_DEF] THEN REPEAT STRIP_TAC THEN ART[] THEN PRED_TAUT_TAC);;

% Add guard into conditional %
let guard_into_cond1 = prove
  ("cond g (c:^ptrans12) c' = cond g ((assert g) seq c) c'",
   FUN_TAC THEN LPRT[cond_DEF;seq_DEF;assert_DEF] THEN PRED_TAUT_TAC);;
let guard_into_cond2 = prove
  ("cond g (c:^ptrans12) c' = cond g c ((assert(not g)) seq c')",
   FUN_TAC THEN LPRT[cond_DEF;seq_DEF;assert_DEF] THEN PRED_TAUT_TAC);;

% Add guard into iteration body %
let guard_into_do = prove
  ("do g (c:^cptrans) = do g ((assert g)seq c)",
   LPORT[do_DEF;SYM seq_assoc] THEN
   CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV[guard_into_cond1])) THEN
   REFL_TAC);;

% Remove assertion %
let remove_assert_left = prove
 ("!p. !c:^ptrans12. c refines ((assert p) seq c)",
  REPEAT GEN_TAC THEN LPORT[refines_DEF;ref_DEF;seq_DEF;assert_DEF] THEN 
  PRED_TAUT_TAC);;
let remove_assert_right = prove
 ("!p. !c:^ptrans12. monotonic c ==> c refines (c seq (assert p))",
  LPORT[monotonic_DEF;refines_DEF;ref_DEF;seq_DEF;assert_DEF] THEN 
  REPEAT STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN PRED_TAUT_TAC);;

% Moving between assign and nondass %
let nondass_to_assign = prove
 ("!e:*s1->*s2. !p. (!u. p u (e u)) ==> (assign e) refines (nondass p)",
  LPORT[refines_DEF;ref_DEF;assign_DEF;nondass_DEF;implies_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN ART[]);;

save_thm(`spec_to_loop`,spec_to_loop);;
save_thm(`guard_into_cond1`,guard_into_cond1);;
save_thm(`guard_into_cond2`,guard_into_cond2);;
save_thm(`guard_into_do`,guard_into_do);;
save_thm(`add_assert`,add_assert);;
save_thm(`remove_assert_left`,remove_assert_left);;
save_thm(`remove_assert_right`,remove_assert_right);;
save_thm(`nondass_to_assign`,nondass_to_assign);;
