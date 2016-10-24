(*============================================================================*)
(*        FILE: rstc.sml                                                      *)
(*                                                                            *)
(* DESCRIPTION: Collection of theorems about (all combinations of) reflexive, *)
(*              symmetric and transitive closure of binary relations.         *)
(*                                                                            *)
(*      AUTHOR: John Harrison                                                 *)
(*              University of Cambridge Computer Laboratory                   *)
(*              New Museums Site                                              *)
(*              Pembroke Street                                               *)
(*              Cambridge CB2 3QG                                             *)
(*              England.                                                      *)
(*              jrh@cl.cam.ac.uk                                              *)
(*                                                                            *)
(*        DATE: 27th May 1993                                                 *)
(*                                                                            *)
(*  TRANSLATED: John Harrison, 31st May 1993                                  *)
(*============================================================================*)

new_theory "RSTC";

load_library{lib=find_library "ind_def",theory="-"};

open Inductive_def;;

(*----------------------------------------------------------------------------*)
(* For compatibility                                                          *)
(*----------------------------------------------------------------------------*)

fun W f x = f x x;

fun GEN_REWRITE_CONV cnv l1 l2 :conv = cnv
  (FIRST_CONV(map REWR_CONV (l1@l2)));

fun GEN_REWRITE_RULE cnv l1 l2 = CONV_RULE(GEN_REWRITE_CONV cnv l1 l2);

fun GEN_REWRITE_TAC cnv l1 l2 = CONV_TAC(GEN_REWRITE_CONV cnv l1 l2);

val prove_thm = store_thm;

exception Unchanged;

fun CHANGED_TAC tac gl =
  let val (sg,just) = tac gl in
      if sg = [gl] then raise Unchanged
      else (sg,just)
  end;

(*----------------------------------------------------------------------------*)
(* Useful oddments                                                            *)
(*----------------------------------------------------------------------------*)

val LAND_CONV = RATOR_CONV o RAND_CONV;

val TAUT_CONV =
  let fun vl w t = type_of t = (==`:bool`==) andalso
  can (find_term is_var) t andalso free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C (curry op THEN) (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o
   sort free_in o
    W(find_terms o vl) o snd)) end;

fun ANTE_RES_THEN ttac th = FIRST_ASSUM(ttac o C MATCH_MP th);

val RULE_INDUCT_TAC = C W STRIP_ASSUME_TAC o RULE_INDUCT_THEN;

(*----------------------------------------------------------------------------*)
(* Little lemmas about equivalent forms of symmetry and transitivity.         *)
(*----------------------------------------------------------------------------*)

val SYM_ALT = prove_thm("SYM_ALT",
  (--`!R:'a->'a->bool. (!x y. R x y ==> R y x) = (!x y. R x y = R y x)`--),
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC,
    FIRST_ASSUM(fn th =>  GEN_REWRITE_TAC I [] [th])] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val TRANS_ALT = prove_thm("TRANS_ALT",
  (--`!(R:'a->'a->bool) (S:'a->'a->bool) U.
        (!x z. (?y. R x y /\ S y z) ==> U x z) =
        (!x y z. R x y /\ S y z ==> U x z)`--),
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Reflexive closure                                                          *)
(*----------------------------------------------------------------------------*)

val {desc = RC_CLAUSES,induction_thm = RC_INDUCT} =
  let val RC = (--`RC:('a->'a->bool)->('a->'a->bool)`--)
  and R = (--`R:'a->'a->bool`--) in
  new_inductive_definition
   {name="RC",
    fixity=Prefix,
    patt=((--`^RC ^R x y`--),[(--`^R`--)]),
    rules=[
     {hypotheses=[(--`^R x y`--)],
      side_conditions=[],
      conclusion=(--`^RC ^R x y`--)},
     {hypotheses=[],
      side_conditions=[],
      conclusion=(--`^RC ^R x x`--)}]} end;

val RC_INC = prove_thm("RC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> RC R x y`--),
  REWRITE_TAC RC_CLAUSES);

val RC_REFL = prove_thm("RC_REFL",
  (--`!(R:'a->'a->bool) x. RC R x x`--),
  REWRITE_TAC RC_CLAUSES);

val RC_CASES = prove_thm("RC_CASES",
  (--`!(R:'a->'a->bool) x y. RC R x y = R x y \/ (x = y)`--),
  GEN_TAC THEN REWRITE_TAC[derive_cases_thm (RC_CLAUSES,RC_INDUCT)] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[]);

val RC_INDUCT = prove_thm("RC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) ==>
            (!x y. RC R x y ==> P x y)`--),
  MATCH_ACCEPT_TAC RC_INDUCT);

val RC_MONO = prove_thm("RC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
            (!x y. RC R x y ==> RC S x y)`--),
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val RC_CLOSED = prove_thm("RC_CLOSED",
  (--`!R:'a->'a->bool. (RC R = R) = !x. R x x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC RC_REFL,
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[RC_CASES] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);

val RC_IDEMP = prove_thm("RC_IDEMP",
  (--`!R:'a->'a->bool. RC(RC R) = RC R`--),
  REWRITE_TAC[RC_CLOSED, RC_REFL]);

val RC_SYM = prove_thm("RC_SYM",
  (--`!R:'a->'a->bool.
        (!x y. R x y ==> R y x) ==> (!x y. RC R x y ==> RC R y x)`--),
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val RC_TRANS = prove_thm("RC_TRANS",
  (--`!R:'a->'a->bool.
        (!x z. (?y. R x y /\ R y z) ==> R x z) ==>
        (!x z. (?y. RC R x y /\ RC R y z) ==> RC R x z)`--),
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);

(*----------------------------------------------------------------------------*)
(* Symmetric closure                                                          *)
(*----------------------------------------------------------------------------*)

val {desc = SC_CLAUSES,induction_thm = SC_INDUCT} =
  let val SC = (--`SC:('a->'a->bool)->('a->'a->bool)`--)
  and R = (--`R:'a->'a->bool`--) in
  new_inductive_definition
   {name="SC",
    fixity=Prefix,
    patt=((--`^SC ^R x y`--),[(--`^R`--)]),
    rules=[
     {hypotheses=[(--`^R x y`--)],
      side_conditions=[],
      conclusion=(--`^SC ^R x y`--)},
     {hypotheses=[(--`^SC ^R x y`--)],
      side_conditions=[],
      conclusion=(--`^SC ^R y x`--)}]} end;

val SC_INC = prove_thm("SC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> SC R x y`--),
  REWRITE_TAC SC_CLAUSES);

val SC_SYM = prove_thm("SC_SYM",
  (--`!(R:'a->'a->bool) x y. SC R x y ==> SC R y x`--),
  REWRITE_TAC SC_CLAUSES);

val SC_CASES = prove_thm("SC_CASES",
  (--`!R:'a->'a->bool. SC(R) x y = R x y \/ R y x`--),
  GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC SC_INDUCT THEN
    ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_REWRITE_TAC[],
    DISCH_THEN DISJ_CASES_TAC THENL
     [ALL_TAC, MATCH_MP_TAC SC_SYM] THEN
    MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]]);

val SC_INDUCT = prove_thm("SC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) ==>
            (!x y. SC R x y ==> P x y)`--),
  MATCH_ACCEPT_TAC SC_INDUCT);

val SC_MONO = prove_thm("SC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. SC R x y ==> SC S x y)`--),
  REWRITE_TAC[SC_CASES] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC[]);

val SC_CLOSED = prove_thm("SC_CLOSED",
  (--`!R:'a->'a->bool. (SC R = R) = !x y. R x y ==> R y x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SC_SYM,
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[SC_CASES] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SC_IDEMP = prove_thm("SC_IDEMP",
  (--`!R:'a->'a->bool. SC(SC R) = SC R`--),
  REWRITE_TAC[SC_CLOSED, SC_SYM]);

val SC_REFL = prove_thm("SC_REFL",
  (--`!R:'a->'a->bool. (!x. R x x) ==> (!x. SC R x x)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SC_CASES] THEN
  ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Transitive closure                                                         *)
(*----------------------------------------------------------------------------*)

val {desc = TC_CLAUSES,induction_thm = TC_INDUCT} =
  let val TC = (--`TC:('a->'a->bool)->('a->'a->bool)`--)
  and R = (--`R:'a->'a->bool`--) in
  new_inductive_definition
   {name="TC",
    fixity=Prefix,
    patt=((--`^TC ^R x y`--),[(--`^R`--)]),
    rules=[
     {hypotheses=[(--`^R x y`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x y`--)},
     {hypotheses=[(--`^TC ^R x y`--), (--`^TC ^R y z`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x z`--)}]} end;

val TC_INC = prove_thm("TC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> TC R x y`--),
  REWRITE_TAC TC_CLAUSES);

val TC_TRANS = prove_thm("TC_TRANS",
  (--`!(R:'a->'a->bool) x z. (?y. TC R x y /\ TC R y z) ==> TC R x z`--),
  REWRITE_TAC TC_CLAUSES);

val TC_CASES = prove_thm("TC_CASES",
  (--`!(R:'a->'a->bool) x z. TC R x z = R x z \/ (?y. TC R x y /\ TC R y z)`--),
  MATCH_ACCEPT_TAC (derive_cases_thm (TC_CLAUSES,TC_INDUCT)));

val TC_INDUCT = prove_thm("TC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)`--),
  MATCH_ACCEPT_TAC TC_INDUCT);

val TC_MONO = prove_thm("TC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. TC R x y ==> TC S x y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC,
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--)] THEN
  ASM_REWRITE_TAC[]);

val TC_CLOSED = prove_thm("TC_CLOSED",
  (--`!R:'a->'a->bool. (TC R = R) = !x z. (?y. R x y /\ R y z) ==> R x z`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC TC_TRANS,
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN EQ_TAC THENL
     [RULE_INDUCT_TAC TC_INDUCT THEN FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
      MATCH_ACCEPT_TAC TC_INC]]);

val TC_IDEMP = prove_thm("TC_IDEMP",
  (--`!R:'a->'a->bool. TC(TC R) = TC R`--),
  REWRITE_TAC[TC_CLOSED, TC_TRANS]);

val TC_REFL = prove_thm("TC_REFL",
  (--`!R:'a->'a->bool. (!x. R x x) ==> (!x. TC R x x)`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[]);

val TC_SYM = prove_thm("TC_SYM",
  (--`!R:'a->'a->bool. (!x y. R x y ==> R y x) ==> (!x y. TC R x y ==> TC R y x)`--),
  GEN_TAC THEN DISCH_TAC THEN RULE_INDUCT_TAC TC_INDUCT THENL
   [MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC,
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--) THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Commutativity properties of the three basic closure operations             *)
(*----------------------------------------------------------------------------*)

val RC_SC = prove_thm("RC_SC",
  (--`!R:'a->'a->bool. RC(SC R) = SC(RC R)`--),
  GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`x:'a`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`y:'a`--) THEN
  REWRITE_TAC[RC_CASES, SC_CASES] THEN
  SUBST1_TAC(ISPECL [(--`x:'a`--), (--`y:'a`--)] EQ_SYM_EQ) THEN
  ASM_CASES_TAC (--`y:'a = x`--) THEN ASM_REWRITE_TAC[]);

val SC_RC = prove_thm("SC_RC",
  (--`!R:'a->'a->bool. SC(RC R) = RC(SC R)`--),
  MATCH_ACCEPT_TAC(GSYM RC_SC));

val RC_TC = prove_thm("RC_TC",
  (--`!R:'a->'a->bool. RC(TC R) = TC(RC R)`--),
  GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`x:'a`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`y:'a`--) THEN EQ_TAC THENL
   [RULE_INDUCT_TAC RC_INDUCT THENL
     [POP_ASSUM MP_TAC THEN MATCH_MP_TAC TC_MONO THEN
      MATCH_ACCEPT_TAC RC_INC,
      MATCH_MP_TAC TC_REFL THEN MATCH_ACCEPT_TAC RC_REFL],
    RULE_INDUCT_TAC TC_INDUCT THENL
     [POP_ASSUM MP_TAC THEN MATCH_MP_TAC RC_MONO THEN
      MATCH_ACCEPT_TAC TC_INC,
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      MATCH_MP_TAC(REWRITE_RULE[TRANS_ALT] RC_TRANS) THEN
      MATCH_ACCEPT_TAC(REWRITE_RULE[TRANS_ALT] TC_TRANS)]]);

val TC_RC = prove_thm("TC_RC",
  (--`!R:'a->'a->bool. TC(RC R) = RC(TC R)`--),
  MATCH_ACCEPT_TAC(GSYM RC_TC));

val TC_SC = prove_thm("TC_SC",
  (--`!(R:'a->'a->bool) x y. SC(TC R) x y ==> TC(SC R) x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SC_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC SC_INC,
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[SC_CASES],
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--) THEN
      ASM_REWRITE_TAC[]]]);

val SC_TC = prove_thm("SC_TC",
  (--`!(R:'a->'a->bool) x y. SC(TC R) x y ==> TC(SC R) x y`--),
  MATCH_ACCEPT_TAC TC_SC);

(*----------------------------------------------------------------------------*)
(* Useful to have "left" and "right" recursive versions of transitivity       *)
(*----------------------------------------------------------------------------*)


val {desc = TCL_CLAUSES,induction_thm = TCL_INDUCT} =
  let val TC = (--`TCL:('a->'a->bool)->('a->'a->bool)`--)
  and R = (--`R:'a->'a->bool`--) in
  new_inductive_definition
   {name="TCL",
    fixity=Prefix,
    patt=((--`^TC ^R x y`--),[(--`^R`--)]),
    rules=[
     {hypotheses=[(--`^R x y`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x y`--)},
     {hypotheses=[(--`^TC ^R x y`--), (--`^R y z`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x z`--)}]} end;

val {desc = TCR_CLAUSES,induction_thm = TCR_INDUCT} =
  let val TC = (--`TCR:('a->'a->bool)->('a->'a->bool)`--)
  and R = (--`R:'a->'a->bool`--) in
  new_inductive_definition
   {name="TCR",
    fixity=Prefix,
    patt=((--`^TC ^R x y`--),[(--`^R`--)]),
    rules=[
     {hypotheses=[(--`^R x y`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x y`--)},
     {hypotheses=[(--`^R x y`--), (--`^TC ^R y z`--)],
      side_conditions=[],
      conclusion=(--`^TC ^R x z`--)}]} end;

(*----------------------------------------------------------------------------*)
(* Prove them both equivalent to TC.                                          *)
(*----------------------------------------------------------------------------*)

val TCL_TRANS = prove_thm("TCL_TRANS",
  (--`!(R:'a->'a->bool) x y z. TCL R x y /\ TCL R y z ==> TCL R x z`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV (--`a /\ b ==> c = b ==> a ==> c`--)] THEN
  DISCH_TAC THEN SPEC_TAC((--`x:'a`--),(--`x:'a`--)) THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC((--`z:'a`--),(--`z:'a`--)) THEN
  SPEC_TAC((--`y:'a`--),(--`y:'a`--)) THEN RULE_INDUCT_TAC TCL_INDUCT THENL
   [X_GEN_TAC (--`z:'a`--) THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCL_CLAUSES) THEN
    EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCL_CLAUSES) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val TCL_TC = prove_thm("TCL_TC",
  (--`TCL:('a->'a->bool)->('a->'a->bool) = TC`--),
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`R:'a->'a->bool`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`x:'a`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`y:'a`--) THEN
  EQ_TAC THENL
   [RULE_INDUCT_TAC TCL_INDUCT THENL
     [MATCH_MP_TAC TC_INC,
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--)] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TC_INC,
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC (el 1 TCL_CLAUSES),
      MATCH_MP_TAC TCL_TRANS THEN EXISTS_TAC (--`y:'a`--)]] THEN
  ASM_REWRITE_TAC[]);

val TCR_TRANS = prove_thm("TCR_TRANS",
  (--`!(R:'a->'a->bool) x y z. TCR R x y /\ TCR R y z ==> TCR R x z`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV (--`a /\ b ==> c = a ==> b ==> c`--)] THEN
  DISCH_TAC THEN SPEC_TAC((--`z:'a`--),(--`z:'a`--)) THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC((--`y:'a`--),(--`y:'a`--)) THEN
  SPEC_TAC((--`x:'a`--),(--`x:'a`--)) THEN RULE_INDUCT_TAC TCR_INDUCT THENL
   [X_GEN_TAC (--`z:'a`--) THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCR_CLAUSES) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[],
    X_GEN_TAC (--`w:'a`--) THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCR_CLAUSES) THEN
    EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val TCR_TC = prove_thm("TCR_TC",
  (--`TCR:('a->'a->bool)->('a->'a->bool) = TC`--),
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`R:'a->'a->bool`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`x:'a`--) THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC (--`y:'a`--) THEN
  EQ_TAC THENL
   [RULE_INDUCT_TAC TCR_INDUCT THENL
     [MATCH_MP_TAC TC_INC,
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--)] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TC_INC,
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC (el 1 TCR_CLAUSES),
      MATCH_MP_TAC TCR_TRANS THEN EXISTS_TAC (--`y:'a`--)]] THEN
  ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Really we just want these theorems, then we can forget TCL and TCR         *)
(*----------------------------------------------------------------------------*)

val TC_TRANS_L = prove_thm("TC_TRANS_L",
  (--`!(R:'a->'a->bool) x z. (?y. TC R x y /\ R y z) ==> TC R x z`--),
  REWRITE_TAC[GSYM TCL_TC] THEN REWRITE_TAC TCL_CLAUSES);

val TC_TRANS_R = prove_thm("TC_TRANS_R",
  (--`!(R:'a->'a->bool) x z. (?y. R x y /\ TC R y z) ==> TC R x z`--),
  REWRITE_TAC[GSYM TCR_TC] THEN REWRITE_TAC TCR_CLAUSES);

val TC_INDUCT_L = prove_thm("TC_INDUCT_L",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. P x y /\ R y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)`--),
  REWRITE_TAC[GSYM TCL_TC] THEN MATCH_ACCEPT_TAC TCL_INDUCT);

val TC_INDUCT_R = prove_thm("TC_INDUCT_R",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)`--),
  REWRITE_TAC[GSYM TCR_TC] THEN MATCH_ACCEPT_TAC TCR_INDUCT);

val TC_CASES_L = prove_thm("TC_CASES_L",
  (--`!(R:'a->'a->bool) x z. TC R x z = R x z \/ (?y. TC R x y /\ R y z)`--),
  REWRITE_TAC[GSYM TCL_TC] THEN
  MATCH_ACCEPT_TAC (derive_cases_thm (TCL_CLAUSES,TCL_INDUCT)));

val TC_CASES_R = prove_thm("TC_CASES_R",
  (--`!(R:'a->'a->bool) x z. TC R x z = R x z \/ (?y. R x y /\ TC R y z)`--),
  REWRITE_TAC[GSYM TCR_TC] THEN
  MATCH_ACCEPT_TAC (derive_cases_thm (TCR_CLAUSES,TCR_INDUCT)));

(*----------------------------------------------------------------------------*)
(* Reflexive symmetric closure                                                *)
(*----------------------------------------------------------------------------*)

val RSC = new_definition("RSC",
  (--`!R:'a->'a->bool. RSC(R) = RC(SC R)`--));

val RSC_INC = prove_thm("RSC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> RSC R x y`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[RSC] THEN
  MATCH_MP_TAC RC_INC THEN MATCH_MP_TAC SC_INC THEN
  ASM_REWRITE_TAC[]);

val RSC_REFL = prove_thm("RSC_REFL",
  (--`!(R:'a->'a->bool) x. RSC R x x`--),
  REWRITE_TAC[RSC, RC_REFL]);

val RSC_SYM = prove_thm("RSC_SYM",
  (--`!(R:'a->'a->bool) x y. RSC R x y ==> RSC R y x`--),
  REWRITE_TAC[RSC, RC_SC, SC_SYM]);

val RSC_CASES = prove_thm("RSC_CASES",
  (--`!(R:'a->'a->bool) x y. RSC R x y = (x = y) \/ R x y \/ R y x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC, RC_CASES, SC_CASES] THEN
  CONV_TAC(AC_CONV(DISJ_ASSOC,DISJ_SYM)));

val RSC_INDUCT = prove_thm("RSC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) ==>
                !x y. RSC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RSC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`SC(R:'a->'a->bool) x y`--) THEN
  RULE_INDUCT_TAC SC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC));

val RSC_MONO = prove_thm("RSC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSC R x y ==> RSC S x y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RSC] THEN
  MATCH_MP_TAC RC_MONO THEN MATCH_MP_TAC SC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val RSC_CLOSED = prove_thm("RSC_CLOSED",
  (--`!R:'a->'a->bool. (RSC R = R) = (!x. R x x) /\ (!x y. R x y ==> R y x)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RSC_REFL, RSC_SYM],
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[RSC_CASES] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val RSC_IDEMP = prove_thm("RSC_IDEMP",
  (--`!R:'a->'a->bool. RSC(RSC R) = RSC R`--),
  REWRITE_TAC[RSC_CLOSED, RSC_REFL, RSC_SYM]);

(*----------------------------------------------------------------------------*)
(* Reflexive transitive closure                                               *)
(*----------------------------------------------------------------------------*)

val RTC = new_definition("RTC",
  (--`!R:'a->'a->bool. RTC(R) = RC(TC R)`--));

val RTC_INC = prove_thm("RTC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> RTC R x y`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_INC THEN MATCH_MP_TAC TC_INC THEN
  ASM_REWRITE_TAC[]);

val RTC_REFL = prove_thm("RTC_REFL",
  (--`!(R:'a->'a->bool) x. RTC R x x`--),
  REWRITE_TAC[RTC, RC_REFL]);

val RTC_TRANS = prove_thm("RTC_TRANS",
  (--`!(R:'a->'a->bool) x z. (?y. RTC R x y /\ RTC R y z) ==> RTC R x z`--),
  REWRITE_TAC[RTC, RC_TC, TC_TRANS]);

val RTC_TRANS_L = prove_thm("RTC_TRANS_L",
  (--`!(R:'a->'a->bool) x z. (?y. RTC R x y /\ R y z) ==> RTC R x z`--),
  REWRITE_TAC[RTC, RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC (--`y:'a`--) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RC_INC THEN
  ASM_REWRITE_TAC[]);

val RTC_TRANS_R = prove_thm("RTC_TRANS_R",
  (--`!(R:'a->'a->bool) x z. (?y. R x y /\ RTC R y z) ==> RTC R x z`--),
  REWRITE_TAC[RTC, RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC (--`y:'a`--) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RC_INC THEN
  ASM_REWRITE_TAC[]);

val RTC_CASES = prove_thm("RTC_CASES",
  (--`!(R:'a->'a->bool) x z. RTC R x z = (x = z) \/ ?y. RTC R x y /\ RTC R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC, RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN EXISTS_TAC (--`x:'a`--),
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--),
    DISJ1_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[]);

val RTC_CASES_L = prove_thm("RTC_CASES_L",
  (--`!(R:'a->'a->bool) x z. RTC R x z = (x = z) \/ ?y. RTC R x y /\ R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC, RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_L]) THENL
     [DISJ2_TAC THEN EXISTS_TAC (--`x:'a`--),
      FIRST_ASSUM(X_CHOOSE_TAC (--`y:'a`--)) THEN DISJ2_TAC THEN EXISTS_TAC (--`y:'a`--)],
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC (--`y:'a`--),
    DISJ1_TAC THEN MATCH_MP_TAC TC_INC] THEN
  ASM_REWRITE_TAC[]);

val RTC_CASES_R = prove_thm("RTC_CASES_R",
  (--`!(R:'a->'a->bool) x z. RTC R x z = (x = z) \/ ?y. R x y /\ RTC R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC, RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_R]) THENL
     [DISJ2_TAC THEN EXISTS_TAC (--`z:'a`--),
      FIRST_ASSUM(X_CHOOSE_TAC (--`y:'a`--)) THEN DISJ2_TAC THEN EXISTS_TAC (--`y:'a`--)],
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC (--`y:'a`--),
    DISJ1_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[]);

val RTC_INDUCT = prove_thm("RTC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`TC(R:'a->'a->bool) x y`--) THEN
  RULE_INDUCT_TAC TC_INDUCT THEN
  FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN TRY(EXISTS_TAC (--`y:'a`--)) THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));

val RTC_INDUCT_L = prove_thm("RTC_INDUCT_L",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. P x y /\ R y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`TC(R:'a->'a->bool) x y`--) THEN
  RULE_INDUCT_TAC TC_INDUCT_L THEN
  FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN TRY(EXISTS_TAC (--`y:'a`--)) THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));

val RTC_INDUCT_R = prove_thm("RTC_INDUCT_R",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`TC(R:'a->'a->bool) x y`--) THEN
  RULE_INDUCT_TAC TC_INDUCT_R THEN
  FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN TRY(EXISTS_TAC (--`y:'a`--)) THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));

val RTC_MONO = prove_thm("RTC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RTC R x y ==> RTC S x y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_MONO THEN MATCH_MP_TAC TC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val RTC_CLOSED = prove_thm("RTC_CLOSED",
  (--`!R:'a->'a->bool. (RTC R = R) = (!x. R x x) /\
                                (!x z. (?y. R x y /\ R y z) ==> R x z)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RTC_REFL, RTC_TRANS],
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[RTC_INC] THEN
    RULE_INDUCT_TAC RTC_INDUCT THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (--`y:'a`--) THEN
    ASM_REWRITE_TAC[]]);

val RTC_IDEMP = prove_thm("RTC_IDEMP",
  (--`!R:'a->'a->bool. RTC(RTC R) = RTC R`--),
  REWRITE_TAC[RTC_CLOSED, RTC_REFL, RTC_TRANS]);

val RTC_SYM = prove_thm("RTC_SYM",
  (--`!R:'a->'a->bool. (!x y. R x y ==> R y x) ==> (!x y. RTC R x y ==> RTC R y x)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_SYM THEN MATCH_MP_TAC TC_SYM THEN ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Symmetric transitive closure                                               *)
(*----------------------------------------------------------------------------*)

val STC = new_definition("STC",
  (--`!R:'a->'a->bool. STC(R) = TC(SC R)`--));

val STC_INC = prove_thm("STC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> STC R x y`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_INC THEN MATCH_MP_TAC SC_INC THEN
  ASM_REWRITE_TAC[]);

val STC_SYM = prove_thm("STC_SYM",
  (--`!(R:'a->'a->bool) x y. STC R x y ==> STC R y x`--),
  GEN_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_SYM THEN REWRITE_TAC[SC_SYM]);

val STC_TRANS = prove_thm("STC_TRANS",
  (--`!(R:'a->'a->bool) x z. (?y. STC R x y /\ STC R y z) ==> STC R x z`--),
  REWRITE_TAC[STC, TC_TRANS]);

val STC_TRANS_L = prove_thm("STC_TRANS_L",
  (--`!(R:'a->'a->bool) x z. (?y. STC R x y /\ R y z) ==> STC R x z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]);

val STC_TRANS_R = prove_thm("STC_TRANS_R",
  (--`!(R:'a->'a->bool) x z. (?y. R x y /\ STC R y z) ==> STC R x z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]);

val STC_CASES = prove_thm("STC_CASES",
  (--`!(R:'a->'a->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. STC R x y /\ STC R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  SUBGOAL_THEN (--`TC(SC(R:'a->'a->bool)) z x = TC(SC R) x z`--) SUBST1_TAC THENL
   [SPEC_TAC((--`x:'a`--),(--`x:'a`--)) THEN SPEC_TAC((--`z:'a`--),(--`z:'a`--)) THEN
    REWRITE_TAC[GSYM SYM_ALT] THEN MATCH_MP_TAC TC_SYM THEN
    MATCH_ACCEPT_TAC SC_SYM,
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]
  THENL
   [MATCH_MP_TAC TC_INC THEN MATCH_MP_TAC SC_INC,
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC (--`y:'a`--)] THEN
  ASM_REWRITE_TAC[]);

val STC_CASES_L = prove_thm("STC_CASES_L",
  (--`!(R:'a->'a->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. STC R x y /\ R y z`--),
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THENL
   [MATCH_MP_TAC STC_TRANS THEN EXISTS_TAC (--`y:'a`--) THEN
    CONJ_TAC THEN MATCH_MP_TAC STC_SYM,
    MATCH_MP_TAC STC_SYM THEN MATCH_MP_TAC STC_TRANS_L THEN
    EXISTS_TAC (--`y:'a`--)] THEN
  ASM_REWRITE_TAC[]);

val STC_CASES_R = prove_thm("STC_CASES_R",
  (--`!(R:'a->'a->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. R x y /\ STC R y z`--),
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THENL
   [MATCH_MP_TAC STC_TRANS THEN EXISTS_TAC (--`y:'a`--) THEN
    CONJ_TAC THEN MATCH_MP_TAC STC_SYM,
    MATCH_MP_TAC STC_SYM THEN MATCH_MP_TAC STC_TRANS_R THEN
    EXISTS_TAC (--`y:'a`--)] THEN
  ASM_REWRITE_TAC[]);

val STC_INDUCT = prove_thm("STC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. STC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[STC] THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [UNDISCH_TAC (--`SC(R:'a->'a->bool) x y`--) THEN REWRITE_TAC[SC_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(ANTE_RES_THEN ACCEPT_TAC),
    FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN EXISTS_TAC (--`y:'a`--)) THEN
    ASM_REWRITE_TAC[]]);

val STC_MONO = prove_thm("STC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. STC R x y ==> STC S x y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_MP_TAC SC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val STC_CLOSED = prove_thm("STC_CLOSED",
  (--`!R:'a->'a->bool. (STC R = R) = (!x y. R x y ==> R y x) /\
                                (!x z. (?y. R x y /\ R y z) ==> R x z)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STC_SYM, STC_TRANS],
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[STC_INC] THEN
    RULE_INDUCT_TAC STC_INDUCT THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC),
      FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN EXISTS_TAC (--`y:'a`--)) THEN
      ASM_REWRITE_TAC[]]]);

val STC_IDEMP = prove_thm("STC_IDEMP",
  (--`!R:'a->'a->bool. STC(STC R) = STC R`--),
  REWRITE_TAC[STC_CLOSED, STC_SYM, STC_TRANS]);

val STC_REFL = prove_thm("STC_REFL",
  (--`!R:'a->'a->bool. (!x. R x x) ==> !x. STC R x x`--),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STC_INC THEN ASM_REWRITE_TAC[]);

(*----------------------------------------------------------------------------*)
(* Reflexive symmetric transitive closure (smallest equivalence relation)     *)
(*----------------------------------------------------------------------------*)

val RSTC = new_definition("RSTC",
  (--`!R:'a->'a->bool. RSTC(R) = RC(TC(SC R))`--));

val RSTC_INC = prove_thm("RSTC_INC",
  (--`!(R:'a->'a->bool) x y. R x y ==> RSTC R x y`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_INC, TC_INC, SC_INC] THEN
  ASM_REWRITE_TAC[]);

val RSTC_REFL = prove_thm("RSTC_REFL",
  (--`!(R:'a->'a->bool) x. RSTC R x x`--),
  REWRITE_TAC[RSTC, RC_REFL]);

val RSTC_SYM = prove_thm("RSTC_SYM",
  (--`!(R:'a->'a->bool) x y. RSTC R x y ==> RSTC R y x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_SYM, TC_SYM] THEN
  REWRITE_TAC[SC_SYM]);

val RSTC_TRANS = prove_thm("RSTC_TRANS",
  (--`!(R:'a->'a->bool) x z. (?y. RSTC R x y /\ RSTC R y z) ==> RSTC R x z`--),
  REWRITE_TAC[RSTC, RC_TC, TC_TRANS]);

val RSTC_TRANS_L = prove_thm("RSTC_TRANS_L",
  (--`!(R:'a->'a->bool) x z. (?y. RSTC R x y /\ R y z) ==> RSTC R x z`--),
  REWRITE_TAC[RSTC, RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC (--`y:'a`--) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY MATCH_MP_TAC [RC_INC, SC_INC] THEN
  ASM_REWRITE_TAC[]);

val RSTC_TRANS_R = prove_thm("RSTC_TRANS_R",
  (--`!(R:'a->'a->bool) x z. (?y. R x y /\ RSTC R y z) ==> RSTC R x z`--),
  REWRITE_TAC[RSTC, RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC (--`y:'a`--) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY MATCH_MP_TAC [RC_INC, SC_INC] THEN
  ASM_REWRITE_TAC[]);

val RSTC_CASES = prove_thm("RSTC_CASES",
  (--`!(R:'a->'a->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ RSTC R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC, RC_TC, RC_SC] THEN
  REWRITE_TAC[GSYM STC] THEN
  GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [RC_CASES] THEN
  CONV_TAC(AC_CONV(DISJ_ASSOC,DISJ_SYM)));

val RSTC_CASES_L = prove_thm("RSTC_CASES_L",
  (--`!(R:'a->'a->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC, RC_CASES, GSYM STC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [STC_CASES_L] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC, DISJ1_TAC] THEN REPEAT DISJ2_TAC THEN
  EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[]);

val RSTC_CASES_R = prove_thm("RSTC_CASES_R",
  (--`!(R:'a->'a->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. R x y /\ RSTC R y z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC, RC_CASES, GSYM STC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [STC_CASES_R] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC, DISJ1_TAC,
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
  REPEAT DISJ2_TAC THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[]);

val RSTC_INDUCT = prove_thm("RSTC_INDUCT",
  (--`!(R:'a->'a->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. RSTC R x y ==> P x y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RSTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`TC(SC(R:'a->'a->bool)) x y`--) THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [UNDISCH_TAC (--`SC(R:'a->'a->bool) x y`--) THEN REWRITE_TAC[SC_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(ANTE_RES_THEN ACCEPT_TAC),
    FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN EXISTS_TAC (--`y:'a`--)) THEN
    ASM_REWRITE_TAC[]]);

val RSTC_MONO = prove_thm("RSTC_MONO",
  (--`!(R:'a->'a->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSTC R x y ==> RSTC S x y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_MONO, TC_MONO, SC_MONO] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);

val RSTC_CLOSED = prove_thm("RSTC_CLOSED",
  (--`!R:'a->'a->bool. (RSTC R = R) = (!x. R x x) /\
                                 (!x y. R x y ==> R y x) /\
                                 (!x z. (?y. R x y /\ R y z) ==> R x z)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[RSTC_REFL, RSTC_SYM, RSTC_TRANS],
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[RSTC_INC] THEN
    RULE_INDUCT_TAC RSTC_INDUCT THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC),
      FIRST_ASSUM(fn th =>  MATCH_MP_TAC th THEN EXISTS_TAC (--`y:'a`--)) THEN
      ASM_REWRITE_TAC[]]]);

val RSTC_IDEMP = prove_thm("RSTC_IDEMP",
  (--`!R:'a->'a->bool. RSTC(RSTC R) = RSTC R`--),
  REWRITE_TAC[RSTC_CLOSED, RSTC_REFL, RSTC_SYM, RSTC_TRANS]);

(*----------------------------------------------------------------------------*)
(* Finally, we prove the inclusion properties for composite closures          *)
(*----------------------------------------------------------------------------*)

val RSC_INC_RC = prove_thm("RSC_INC_RC",
  (--`!R:'a->'a->bool. !x y. RC R x y ==> RSC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC, RC_SC, SC_INC]);

val RSC_INC_SC = prove_thm("RSC_INC_SC",
  (--`!R:'a->'a->bool. !x y. SC R x y ==> RSC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC, RC_INC]);

val RTC_INC_RC = prove_thm("RTC_INC_RC",
  (--`!R:'a->'a->bool. !x y. RC R x y ==> RTC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC, RC_TC, TC_INC]);

val RTC_INC_TC = prove_thm("RTC_INC_TC",
  (--`!R:'a->'a->bool. !x y. TC R x y ==> RTC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC, RC_INC]);

val STC_INC_SC = prove_thm("STC_INC_SC",
  (--`!R:'a->'a->bool. !x y. SC R x y ==> STC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[STC, TC_INC]);

val STC_INC_TC = prove_thm("STC_INC_TC",
  (--`!R:'a->'a->bool. !x y. TC R x y ==> STC R x y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC SC_INC);

val RSTC_INC_RC = prove_thm("RSTC_INC_RC",
  (--`!R:'a->'a->bool. !x y. RC R x y ==> RSTC R x y`--),
  REWRITE_TAC[RSTC, RC_TC, RC_SC, GSYM STC, STC_INC]);

val RSTC_INC_SC = prove_thm("RSTC_INC_SC",
  (--`!R:'a->'a->bool. !x y. SC R x y ==> RSTC R x y`--),
  REWRITE_TAC[RSTC, GSYM RTC, RTC_INC]);

val RSTC_INC_TC = prove_thm("RSTC_INC_TC",
  (--`!R:'a->'a->bool. !x y. TC R x y ==> RSTC R x y`--),
  GEN_TAC THEN REWRITE_TAC[RSTC, RC_TC, GSYM RSC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC RSC_INC);

val RSTC_INC_RSC = prove_thm("RSTC_INC_RSC",
  (--`!R:'a->'a->bool. !x y. RSC R x y ==> RSTC R x y`--),
  REWRITE_TAC[RSC, RSTC, RC_TC, TC_INC]);

val RSTC_INC_RTC = prove_thm("RSTC_INC_RTC",
  (--`!R:'a->'a->bool. !x y. RTC R x y ==> RSTC R x y`--),
  GEN_TAC THEN REWRITE_TAC[GSYM RTC, RSTC] THEN MATCH_MP_TAC RTC_MONO THEN
  MATCH_ACCEPT_TAC SC_INC);

val RSTC_INC_STC = prove_thm("RSTC_INC_STC",
  (--`!R:'a->'a->bool. !x y. STC R x y ==> RSTC R x y`--),
  GEN_TAC THEN REWRITE_TAC[GSYM STC, RSTC, RC_INC]);

close_theory();

export_theory();
