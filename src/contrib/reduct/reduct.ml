%============================================================================%
%        FILE: reduct.ml                                                     %
%                                                                            %
% DESCRIPTION: General "reduction" properties of binary relations, such as   %
%              normalization, confluence etc. Theorems about the relations   %
%              between them, e.g. Newman's Lemma.                            %
%                                                                            %
%      AUTHOR: John Harrison                                                 %
%              University of Cambridge Computer Laboratory                   %
%              New Museums Site                                              %
%              Pembroke Street                                               %
%              Cambridge CB2 3QG                                             %
%              England.                                                      %
%                                                                            %
%        DATE: 29th May 1993                                                 %
%============================================================================%

timer true;;

can unlink `REDUCT.th`;;

new_theory `REDUCT`;;

load_library `ind_defs`;;

map hide_constant [`I`; `K`; `S`];;

%----------------------------------------------------------------------------%
% Useful oddments                                                            %
%----------------------------------------------------------------------------%

let LAND_CONV = RATOR_CONV o RAND_CONV;;

let TAUT_CONV =
  let val w t = type_of t = ":bool" & can (find_term is_var) t & free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C $THEN (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o sort (uncurry free_in) o
    W(find_terms o val) o snd));;

let ANTE_RES_THEN ttac th = FIRST_ASSUM(ttac o C MATCH_MP th);;

let RULE_INDUCT_TAC = C W STRIP_ASSUME_TAC o RULE_INDUCT_THEN;;

let autoload_all_theory thy =
  do map (\s. autoload_theory(`definition`,thy,fst s)) (definitions thy);
     map (\s. autoload_theory(`theorem`,thy,fst s)) (theorems thy);;

%----------------------------------------------------------------------------%
% We use the RSTC theory a great deal                                        %
%----------------------------------------------------------------------------%

new_parent `RSTC`;;

autoload_all_theory `RSTC`;;

%----------------------------------------------------------------------------%
% Useful lemmas: essentially equivalent forms of wellfoundedness             %
%----------------------------------------------------------------------------%

let SEQ_EXISTS_IMP = prove_thm(`SEQ_EXISTS_IMP`,
  "!R (P:*->bool). (?x. P x) /\ (!x. P x ==> ?y. P y /\ R x y) ==>
        ?seq. (!n. P(seq n)) /\ (!n. R (seq n) (seq (SUC n)))",
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL ["x:*"; "\(s:*) (n:num). @y. P y /\ (R:*->*->bool) s y"]
    num_Axiom) THEN DISCH_THEN(MP_TAC o EXISTENCE) THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN "seq:num->*" STRIP_ASSUME_TAC) THEN
  EXISTS_TAC "seq:num->*" THEN
  SUBGOAL_THEN "!n. P(seq (SUC n)) /\ (R:*->*->bool) (seq n) (seq(SUC n))"
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[]; FIRST_ASSUM(\th. REWRITE_TAC[SPEC "SUC n" th])] THEN
    BETA_TAC THEN CONV_TAC SELECT_CONV THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN X_GEN_TAC "n:num" THEN
    STRUCT_CASES_TAC(SPEC "n:num" num_CASES) THEN ASM_REWRITE_TAC[]]);;

let SEQ_EXISTS = prove_thm(`SEQ_EXISTS`,
  "!R. (?P:*->bool. (?x. P x) /\ (!x. P x ==> ?y. P y /\ R x y)) =
       (?seq. !n. R (seq n) (seq (SUC n)))",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (X_CHOOSE_TAC "seq:num->*" o
      MATCH_MP SEQ_EXISTS_IMP)) THEN EXISTS_TAC "seq:num->*" THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC "seq:num->*") THEN
    EXISTS_TAC "\x:*. ?n:num. x = seq(n)" THEN
    BETA_TAC THEN REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC ["seq 0 :*"; "0"] THEN REFL_TAC;
      X_GEN_TAC "x:*" THEN DISCH_THEN(X_CHOOSE_TAC "n:num") THEN
      EXISTS_TAC "seq(SUC n):*" THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC "SUC n" THEN REFL_TAC]]);;

%----------------------------------------------------------------------------%
% Normality of a term w.r.t. a reduction relation                            %
%----------------------------------------------------------------------------%

let NORMAL = new_definition(`NORMAL`,
  "NORMAL(R:*->*->bool) x = ~?y. R x y");;

%----------------------------------------------------------------------------%
% Full Church-Rosser property.                                               %
%                                                                            %
% Note that we deviate from most term rewriting literature which call this   %
% the "diamond property" and calls a relation "Church-Rosser" iff its RTC    %
% has the diamond property. But this seems simpler and more natural.         %
%----------------------------------------------------------------------------%

let CR = new_definition(`CR`,
  "CR(R:*->*->bool) =
    !x y1 y2. R x y1 /\ R x y2 ==> ?z. R y1 z /\ R y2 z");;

%----------------------------------------------------------------------------%
% Weak Church-Rosser property, i.e. the rejoining may take several steps.    %
%----------------------------------------------------------------------------%

let WCR = new_definition(`WCR`,
  "WCR(R:*->*->bool) = !x y1 y2. R x y1 /\ R x y2 ==>
                                 ?z. RTC R y1 z /\ RTC R y2 z");;

%----------------------------------------------------------------------------%
% (Weak) normalization: every term has a normal form.                        %
%----------------------------------------------------------------------------%

let WN = new_definition(`WN`,
  "WN(R:*->*->bool) = !x. ?y. RTC R x y /\ NORMAL(R) y");;

%----------------------------------------------------------------------------%
% Strong normalization: every reduction sequence terminates (aka Noetherian) %
%----------------------------------------------------------------------------%

let SN = new_definition(`SN`,
  "SN(R:*->*->bool) = ~?seq. !n. R (seq n) (seq (SUC n))");;

%----------------------------------------------------------------------------%
% Alternative "preservation" form of SN definition which is more useful.     %
%----------------------------------------------------------------------------%

let SN_PRESERVE = prove_thm(`SN_PRESERVE`,
  "!R:*->*->bool. SN(R) = !P. (!x. P x ==> ?y. P y /\ R x y) ==> ~?x. P x",
  GEN_TAC THEN REWRITE_TAC[SN; TAUT_CONV "(a ==> ~b) = ~(b /\ a)"] THEN
  GEN_REWRITE_TAC I [] [TAUT_CONV "(~a = b) = (a = ~b)"] THEN
  CONV_TAC(RAND_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[SEQ_EXISTS]);;

%----------------------------------------------------------------------------%
% "Noetherian induction" for strongly normalizing relation                   %
%----------------------------------------------------------------------------%

let SN_NOETHERIAN = prove_thm(`SN_NOETHERIAN`,
  "!R:*->*->bool. SN(R) = !P. (!x. (!y. R x y ==> P y) ==> P x) ==> !x. P x",
  GEN_TAC THEN REWRITE_TAC[SN_PRESERVE] THEN
  CONV_TAC((LAND_CONV o RAND_CONV o ABS_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    CONTRAPOS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT_CONV "a ==> b = b \/ ~a"; DE_MORGAN_THM] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC "P:*->bool" THEN
  POP_ASSUM(MP_TAC o SPEC "\x:*. ~(P x)") THEN BETA_TAC THEN
  REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Normality is preserved by transitive closure                               %
%----------------------------------------------------------------------------%

let NORMAL_TC = prove_thm(`NORMAL_TC`,
  "!R:*->*->bool. NORMAL(TC R) x = NORMAL(R) x",
  GEN_TAC THEN REWRITE_TAC[NORMAL] THEN
  AP_TERM_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC "y:*") THENL
   [POP_ASSUM(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_R]) THENL
     [EXISTS_TAC "y:*";
      POP_ASSUM(X_CHOOSE_TAC "z:*") THEN EXISTS_TAC "z:*"];
    EXISTS_TAC "y:*" THEN MATCH_MP_TAC TC_INC] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Hence so is normalization                                                  %
%----------------------------------------------------------------------------%

let WN_TC = prove_thm(`WN_TC`,
  "!R:*->*->bool. WN(TC R) = WN R",
  REWRITE_TAC[WN; NORMAL_TC; RTC; TC_IDEMP]);;

%----------------------------------------------------------------------------%
% Strong normalization is too in fact.                                       %
%----------------------------------------------------------------------------%

let SN_TC = prove_thm(`SN_TC`,
  "!R:*->*->bool. SN(TC R) = SN R",
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[SN] THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC "seq:num->*") THEN
    EXISTS_TAC "seq:num->*" THEN GEN_TAC THEN
    MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [] [SN] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC "seq:num->*") THEN
    REWRITE_TAC[SN_PRESERVE] THEN DISCH_THEN(MP_TAC o
      SPEC "\x:*. ?n:num. RTC R (seq n) x /\ RTC R x (seq (SUC n))") THEN
    BETA_TAC THEN REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ALL_TAC;
      MAP_EVERY EXISTS_TAC ["seq(0):*"; "0"] THEN
      REWRITE_TAC[RTC_REFL] THEN REWRITE_TAC[RTC] THEN
      MATCH_MP_TAC RC_INC THEN ASM_REWRITE_TAC[]] THEN
    X_GEN_TAC "x:*" THEN
    DISCH_THEN(X_CHOOSE_THEN "n:num" STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC "RTC R x (seq(SUC n):*)" THEN DISCH_THEN
    (REPEAT_TCL DISJ_CASES_THEN MP_TAC o ONCE_REWRITE_RULE[RTC_CASES_L]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM(MP_TAC o SPEC "SUC n") THEN
      DISCH_THEN(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_R]) THENL
       [EXISTS_TAC "seq(SUC(SUC n)):*" THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC "SUC n" THEN ASM_REWRITE_TAC[RTC_REFL] THEN
        MATCH_MP_TAC RTC_INC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
        EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC "SUC n" THEN CONJ_TAC THENL
         [MATCH_MP_TAC RTC_INC;
          REWRITE_TAC[RTC] THEN MATCH_MP_TAC RC_INC] THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN "y:*" STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC "RTC(R:*->*->bool) x y" THEN
      DISCH_THEN(DISJ_CASES_TAC o ONCE_REWRITE_RULE[RTC_CASES_R]) THENL
       [EXISTS_TAC "seq(SUC n):*" THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC "n:num" THEN REWRITE_TAC[RTC_REFL] THEN
        ASM_REWRITE_TAC[RTC; RC_CASES];
        FIRST_ASSUM(X_CHOOSE_THEN "z:*" STRIP_ASSUME_TAC) THEN
        EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC "n:num" THEN CONJ_TAC THENL
         [MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC "x:*";
          MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC "y:*"] THEN
        ASM_REWRITE_TAC[]]]]);;

%----------------------------------------------------------------------------%
% Strong normalization implies normalization                                 %
%----------------------------------------------------------------------------%

let SN_WN = prove_thm(`SN_WN`,
  "!R:*->*->bool. SN(R) ==> WN(R)",
  GEN_TAC THEN REWRITE_TAC[SN_PRESERVE; WN] THEN
  DISCH_THEN(MP_TAC o SPEC "\x:*. ~?y. RTC R x y /\ NORMAL R y") THEN
  BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC "x:*" THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV) THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC "x:*") THEN
  REWRITE_TAC[RTC_REFL] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NORMAL]) THEN
  DISCH_THEN(X_CHOOSE_TAC "y:*") THEN
  EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC "z:*" THEN STRIP_TAC THEN
  SUBGOAL_THEN "RTC R x z /\ NORMAL(R:*->*->bool) z" MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC "y:*"; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

%----------------------------------------------------------------------------%
% Reflexive closure preserves Church-Rosser property (pretty trivial)        %
%----------------------------------------------------------------------------%

let RC_CR = prove_thm(`RC_CR`,
  "!R:*->*->bool. CR(R) ==> CR(RC R)",
  GEN_TAC THEN REWRITE_TAC[CR; RC_CASES] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL ["x:*"; "y1:*"; "y2:*"]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC "z:*") THEN
    EXISTS_TAC "z:*"; EXISTS_TAC "y1:*"; EXISTS_TAC "y2:*";
    EXISTS_TAC "x:*"] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% The strip lemma leads us halfway to the fact that transitive         x     %
% closure preserves the Church-Rosser property. It's no harder        / \    %
% to prove it for two separate reduction relations. This then        /   y2  %
% allows us to prove the desired theorem simply by using the        /    /   %
% strip lemma twice with a bit of conjunct-swapping.               y1   /    %
%                                                                    \ /     %
% The diagram on the right shows the use of the variables.            z      %
%----------------------------------------------------------------------------%

let STRIP_LEMMA = prove_thm(`STRIP_LEMMA`,
  "!R S. (!x y1 y2.    R x y1 /\ S x y2 ==> ?z:*. S y1 z /\    R y2 z) ==>
         (!x y1 y2. TC R x y1 /\ S x y2 ==> ?z:*. S y1 z /\ TC R y2 z)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT_CONV "a /\ b ==> c = a ==> (b ==> c)"] THEN
  CONV_TAC(ONCE_DEPTH_CONV FORALL_IMP_CONV) THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o CONJ(ASSUME "(R:*->*->bool) x y")) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN "z:*" STRIP_ASSUME_TAC) THEN
    EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN "w:*" STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC "(S:*->*->bool) y w" THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN "v:*" STRIP_ASSUME_TAC) THEN
    EXISTS_TAC "v:*" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TC_TRANS THEN
    EXISTS_TAC "w:*" THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Transitive closure preserves Church-Rosser property.                       %
%----------------------------------------------------------------------------%

let TC_CR = prove_thm(`TC_CR`,
  "!R:*->*->bool. CR(R) ==> CR(TC R)",
  GEN_TAC THEN REWRITE_TAC[CR] THEN DISCH_TAC THEN
  MATCH_MP_TAC STRIP_LEMMA THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC STRIP_LEMMA THEN POP_ASSUM MATCH_ACCEPT_TAC);;

%----------------------------------------------------------------------------%
% Reflexive transitive closure preserves Church-Rosser property.             %
%----------------------------------------------------------------------------%

let RTC_CR = prove_thm(`RTC_CR`,
  "!R:*->*->bool. CR(R) ==> CR(RTC R)",
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_CR THEN MATCH_MP_TAC TC_CR THEN
  POP_ASSUM ACCEPT_TAC);;

%----------------------------------------------------------------------------%
% Equivalent "Church-Rosser" property for the equivalence relation.          %
%----------------------------------------------------------------------------%

let STC_CR = prove_thm(`STC_CR`,
  "!R:*->*->bool. CR(RTC R) =
        !x y. RSTC R x y ==> ?z:*. RTC R x z /\ RTC R y z",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN RULE_INDUCT_TAC RSTC_INDUCT THENL
     [EXISTS_TAC "y:*" THEN REWRITE_TAC[RTC_REFL] THEN
      MATCH_MP_TAC RTC_INC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC "x:*" THEN EXISTS_TAC "x:*" THEN
      REWRITE_TAC[RTC_REFL];
      EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPECL ["y:*"; "z':*"; "z'':*"] o
        REWRITE_RULE[CR]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN "w:*" STRIP_ASSUME_TAC) THEN
      EXISTS_TAC "w:*" THEN CONJ_TAC THEN MATCH_MP_TAC RTC_TRANS THENL
       [EXISTS_TAC "z':*"; EXISTS_TAC "z'':*"] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[CR] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC ["x:*"; "y1:*"; "y2:*"] THEN
    STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC RSTC_TRANS THEN EXISTS_TAC "x:*" THEN
    CONJ_TAC THENL [MATCH_MP_TAC RSTC_SYM; ALL_TAC] THEN
    MATCH_MP_TAC RSTC_INC_RTC THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Under normalization, Church-Rosser is equivalent to uniqueness of NF       %
%----------------------------------------------------------------------------%

let NORM_CR = prove_thm(`NORM_CR`,
  "!R:*->*->bool. WN(R) ==>
     (CR(RTC R) = (!x y1 y2. RTC R x y1 /\ NORMAL(R) y1 /\
                             RTC R x y2 /\ NORMAL(R) y2 ==> (y1 = y2)))",
  GEN_TAC THEN REWRITE_TAC[WN] THEN DISCH_TAC THEN EQ_TAC THEN
  REWRITE_TAC[CR] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC ["x:*"; "y1:*"; "y2:*"] THEN STRIP_TAC THENL
   [SUBGOAL_THEN "?z. RTC (R:*->*->bool) y1 z /\ RTC R y2 z" MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "x:*" THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN "z:*" MP_TAC) THEN
      REWRITE_TAC[RTC; RC_CASES] THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM NORMAL_TC]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORMAL]) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NOT_EXISTS_CONV)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REFL_TAC];
    FIRST_ASSUM(X_CHOOSE_THEN "z1:*" STRIP_ASSUME_TAC o SPEC "y1:*") THEN
    FIRST_ASSUM(X_CHOOSE_THEN "z2:*" STRIP_ASSUME_TAC o SPEC "y2:*") THEN
    EXISTS_TAC "z1:*" THEN
    SUBGOAL_THEN "z1:* = z2" (\th. ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "x:*" THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC RTC_TRANS THENL
     [EXISTS_TAC "y1:*"; EXISTS_TAC "y2:*"] THEN
    ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Normalizing and Church-Rosser iff every term has a unique normal form      %
%----------------------------------------------------------------------------%

let CR_NORM = prove_thm(`CR_NORM`,
  "!R:*->*->bool. WN(R) /\ CR(RTC R) = !x. ?!y. RTC R x y /\ NORMAL(R) y",
  GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV FORALL_AND_CONV) THEN
  REWRITE_TAC[GSYM WN; TAUT_CONV "(a /\ b = a /\ c) = a ==> (b = c)"] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP NORM_CR) THEN
  REWRITE_TAC[CONJ_ASSOC]);;

%----------------------------------------------------------------------------%
% Newman's lemma: weak Church-Rosser plus                   x                %
% strong normalization implies full Church-                / \               %
% Rosser. By the above (and SN ==> WN) it                 z1 z2              %
% is sufficient to show normal forms are                 / | | \             %
% unique. We use the Noetherian induction               /  \ /  \            %
% form of SN, so we need only prove that if            /    z    \           %
% some term has multiple normal forms, so             /     |     \          %
% does a "successor". See the diagram on the         /      |      \         %
% right for the use of variables.                   y1      w       y2       %
%----------------------------------------------------------------------------%

let NEWMAN_LEMMA = prove_thm(`NEWMAN_LEMMA`,
  "!R:*->*->bool. SN(R) /\ WCR(R) ==> CR(RTC R)",
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP SN_WN) THEN
  FIRST_ASSUM(\th. REWRITE_TAC[MATCH_MP NORM_CR th]) THEN
  GEN_REWRITE_TAC I [] [TAUT_CONV "x = ~~x"] THEN
  CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  MP_TAC(SPEC "R:*->*->bool" SN_PRESERVE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN BETA_TAC THEN
  GEN_TAC THEN REWRITE_TAC[NORMAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN STRIP_TAC THEN
  MP_TAC(ASSUME "RTC (R:*->*->bool) x y1") THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[RTC_CASES_R]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THENL
   [UNDISCH_TAC "RTC(R:*->*->bool) x y2" THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN
    FIRST_ASSUM(\th. REWRITE_TAC[CONV_RULE(RAND_CONV SYM_CONV) th]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN "z1:*" STRIP_ASSUME_TAC)] THEN
  MP_TAC(ASSUME "RTC (R:*->*->bool) x y2") THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[RTC_CASES_R]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THENL
   [UNDISCH_TAC "RTC(R:*->*->bool) x y1" THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN
    FIRST_ASSUM(\th. REWRITE_TAC[CONV_RULE(RAND_CONV SYM_CONV) th]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN "z2:*" STRIP_ASSUME_TAC)] THEN
  UNDISCH_TAC "WCR(R:*->*->bool)" THEN REWRITE_TAC[WCR] THEN
  DISCH_THEN(MP_TAC o SPECL ["x:*"; "z1:*"; "z2:*"]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN "z:*" STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC "WN(R:*->*->bool)" THEN REWRITE_TAC[WN] THEN
  REWRITE_TAC[NORMAL] THEN CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN "w:*" STRIP_ASSUME_TAC o SPEC "z:*") THEN
  ASM_CASES_TAC "y1:* = w" THENL
   [ALL_TAC;
    EXISTS_TAC "z1:*" THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC ["y1:*"; "w:*"] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RTC_TRANS THEN EXISTS_TAC "z:*" THEN
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC "y2:* = w" THENL
   [ALL_TAC;
    EXISTS_TAC "z2:*" THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC ["y2:*"; "w:*"] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RTC_TRANS THEN EXISTS_TAC "z:*" THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC "~(y1:* = y2)" THEN ASM_REWRITE_TAC[]);;

close_theory();;
