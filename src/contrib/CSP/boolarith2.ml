% Another supplementary theory of Boolean Algebra and Arithmetic        %
% theorems. In fact an extension to boolarith1.th.                      %
%                                                                       %
% FILE          : boolarith2.ml                                         %
% DESCRIPTION   : Extends the boolean and arithmetic built-in theories  %
%                 with some theorems which are needed for mechanizing   %
%                 csp.                                                  %
%                                                                       %
% LOADS LIBRARY : taut                                                  %
% READS FILES   : boolarith1.th                                         %
% WRITES FILES  : boolarith2.th                                         %
%                                                                       %
% AUTHOR        : Albert J Camilleri                                    %
% AFFILIATION   : Hewlett-Packard Laboratories, Bristol                 %
% DATE          : 86.04.04                                              %
% MODIFIED      : 89.07.20                                              %
% REVISED       : 91.10.01                                              %

new_theory `boolarith2`;;

new_parent `boolarith1`;;

% Load the Tautology Checker                                            %

load_library `taut`;;

let F_IMP_EX_F =
save_thm (`F_IMP_EX_F`,
          DISCH "F" (EXISTS ("?t:bool.F","F") (ASSUME "F")));;

let EX_F_IMP_F =
save_thm (`EX_F_IMP_F`,
          DISCH_ALL (SELECT_RULE (ASSUME "?t:bool.F")));;

let F_FROM_EX_F =
save_thm (`F_FROM_EX_F`, IMP_ANTISYM_RULE EX_F_IMP_F F_IMP_EX_F);;

let ID_IMP =
save_thm (`ID_IMP`, TAUT_RULE "! b. b ==> b");;

let CONJ_IMP_TAUT =
save_thm (`CONJ_IMP_TAUT`,
          TAUT_RULE "! a b c. (a ==> b) ==> ((a /\ c) ==> (b /\ c))");;

let CONJ2_IMP_TAUT =
save_thm (`CONJ2_IMP_TAUT`,
          TAUT_RULE "! a b c d.
                            (a ==> b) ==>
                            ((d /\ (a /\ c)) ==> (d /\ (b /\ c)))");;

let CONJ3_IMP_TAUT =
save_thm (`CONJ3_IMP_TAUT`,
          TAUT_RULE "! a b c.
                            (a ==> b) ==>
                            ((c /\ a) ==> (c /\ b))");;

let NOT_LEQ = theorem `boolarith1` `NOT_LEQ`;;

let ADD_SUC_0 =
save_thm (`ADD_SUC_0`,
          (CONV_RULE (DEPTH_CONV num_CONV))
          (REWRITE_RULE [SPECL ["m:num";"1"] ADD_SYM] ADD1));;

let LESS_MONO_MULT' =
    save_thm (`LESS_MONO_MULT'`,
              GEN_ALL
                (SUBS [SPECL ["m:num";"p:num"] MULT_SYM;
                       SPECL ["n:num";"p:num"] MULT_SYM]
                      (SPEC_ALL LESS_MONO_MULT)));;

let LESS_EQ_0_N =
    save_thm (`LESS_EQ_0_N`, REWRITE_RULE [NOT_LESS] NOT_LESS_0);;

let LESS_EQ_MONO_ADD_EQ' =
    save_thm (`LESS_EQ_MONO_ADD_EQ'`,
              GEN_ALL (SYM (SUBS [SPECL ["m:num";"p:num"] ADD_SYM;
                                  SPECL ["n:num";"p:num"] ADD_SYM]
                                 (SPEC_ALL LESS_EQ_MONO_ADD_EQ))));;

let LESS_EQ_MONO_ADD_EQ1 =
    save_thm (`LESS_EQ_MONO_ADD_EQ1`,
              GEN_ALL (REWRITE_RULE [ADD]
                                    (SPECL ["m:num";"0:num";"p:num"]
                                           LESS_EQ_MONO_ADD_EQ)));;

let LESS_EQ_MONO_ADD_EQ2 =
    save_thm (`LESS_EQ_MONO_ADD_EQ2`,
              GEN_ALL (REWRITE_RULE [ADD]
                                    (SPECL ["0:num";"n:num";"p:num"]
                                           LESS_EQ_MONO_ADD_EQ)));;

let LESS_EQ_MONO_ADD_EQ3 =
    save_thm (`LESS_EQ_MONO_ADD_EQ3`,
              GEN_ALL (REWRITE_RULE [ADD;LESS_EQ_0_N]
                                    (SPECL ["0:num";"n:num";"p:num"]
                                           LESS_EQ_MONO_ADD_EQ)));;

let ADD_SYM_ASSOC =
    prove_thm (`ADD_SYM_ASSOC`,
               "! a b c. a + (b + c) = b + (a + c)",
               REPEAT GEN_TAC THEN
               REWRITE_TAC [ADD_ASSOC] THEN
               SUBST_TAC [SPECL ["a:num";"b:num"] ADD_SYM] THEN
               REWRITE_TAC []);;

let NOT_SUC_LEQ_0 =
    prove_thm (`NOT_SUC_LEQ_0`,
               "! n . ~ (SUC n) <= 0",
               REWRITE_TAC[NOT_LEQ;LESS_0]);;

let INV_SUC_LEQ =
    prove_thm (`INV_SUC_LEQ`,
               "! m n . (SUC m <= SUC n) = (m <= n)",
               REWRITE_TAC [LESS_OR_EQ;LESS_MONO_EQ;INV_SUC_EQ]);;

let TWICE =
    prove_thm (`TWICE`,
               "! x . (x + x) = (SUC (SUC 0)) * x",
               REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES]);;

let NOT_SUC_LEQ =
    save_thm (`NOT_SUC_LEQ`,
              NOT_INTRO
               (DISCH_ALL
                 (REWRITE_RULE [NOT_SUC_LEQ_0]
                               (SPEC "0" (ASSUME "(!n m. (SUC m) <= n)")))));;

let LEQ_SPLIT =
    save_thm (`LEQ_SPLIT`,
              let asm_thm = ASSUME "(m + n) <= p"
              in
              DISCH_ALL
               (CONJ
                (MP (SPECL ["n:num";"m+n";"p:num"] LESS_EQ_TRANS)
                    (CONJ (SUBS [SPECL ["n:num";"m:num"] ADD_SYM]
                                (SPECL ["n:num";"m:num"] LESS_EQ_ADD))
                          asm_thm))
                (MP (SPECL ["m:num";"m+n";"p:num"] LESS_EQ_TRANS)
                    (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))));;

close_theory ();;
