% A supplementary theory of Boolean Algebra and Arithmetic theorems.    %
%                                                                       %
% FILE          : boolarith1.ml                                         %
% DESCRIPTION   : Extends the boolean and arithmetic built-in theories  %
%                 with some theorems which are needed for mechanizing   %
%                 csp.                                                  %
%                                                                       %
% LOADS LIBRARY : taut                                                  %
% READS FILES   : None                                                  %
% WRITES FILES  : boolarith1.th                                         %
%                                                                       %
% AUTHOR        : Albert J Camilleri                                    %
% AFFILIATION   : Hewlett-Packard Laboratories, Bristol                 %
% DATE          : 85.11.15                                              %
% MODIFIED      : 89.07.20                                              %
% REVISED       : 91.10.01                                              %

new_theory `boolarith1`;;

% Load the Tautology Checker                                            %

load_library `taut`;;

let NOT_EQ =
    save_thm (`NOT_EQ`,
              TAUT_RULE "!t1 t2. (t1 = t2) = (~t1 = ~t2)");;

let DISJ_ASSOC =
    save_thm (`DISJ_ASSOC`,
              TAUT_RULE "!t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3");;

let LEFT_CONJ_DISTRIB =
    save_thm (`LEFT_CONJ_DISTRIB`,
              TAUT_RULE "!t1 t2 t3:bool.
                           (t1 /\ (t2 \/ t3)) = ((t1 /\ t2) \/ (t1 /\ t3))");;

let RIGHT_CONJ_DISTRIB =
    save_thm (`RIGHT_CONJ_DISTRIB`,
              TAUT_RULE "!t1 t2 t3:bool.
                           ((t2 \/ t3) /\ t1) = ((t2 /\ t1) \/ (t3 /\ t1))");;

let LEFT_DISJ_DISTRIB =
    save_thm (`LEFT_DISJ_DISTRIB`,
              TAUT_RULE "!t1 t2 t3:bool.
                           (t1 \/ (t2 /\ t3)) = ((t1 \/ t2) /\ (t1 \/ t3))");;

let RIGHT_DISJ_DISTRIB =
    save_thm (`RIGHT_DISJ_DISTRIB`,
              TAUT_RULE "!t1 t2 t3:bool.
                           ((t2 /\ t3) \/ t1) = ((t2 \/ t1) /\ (t3 \/ t1))");;

let LEFT_DISJ_CONJ =
    save_thm (`LEFT_DISJ_CONJ`,
              TAUT_RULE "!a b . a /\ b \/ b = b");;

let GREATER_EQ =
    prove_thm (`GREATER_EQ`,
               "! a b:num. (a >= b) = (b <= a)",
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [GREATER_OR_EQ;LESS_OR_EQ;GREATER] THEN
               SUBST_TAC [(SPECL
                            ["a:num";"b:num"]
                            (INST_TYPE [(":num",":*")] EQ_SYM_EQ))]
               THEN REWRITE_TAC[]);;

let NOT_LEQ =
    prove_thm (`NOT_LEQ`,
               "!a b. (~(a <= b)) = (b < a)",
               REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)]);;

let EQ_LEQ =
    prove_thm (`EQ_LEQ`,
               "! a b : num . (a = b) = ((a <= b) /\ (b <= a))",
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [LESS_OR_EQ;
                            LEFT_CONJ_DISTRIB;
                            RIGHT_CONJ_DISTRIB;
                            LESS_ANTISYM] THEN
               SUBST_TAC [(SPECL
                            ["b:num";"a:num"]
                            (INST_TYPE [(":num",":*")] EQ_SYM_EQ))] THEN
               REWRITE_TAC [INST [("((a:num) = b)","t1:bool");
                                  ("b < a","t2:bool")]
                                 (SPEC_ALL CONJ_SYM);
                            DISJ_ASSOC;
                            SYM (SPEC_ALL RIGHT_CONJ_DISTRIB);
                            LEFT_DISJ_CONJ]);;

let NOT_EQ_LEQ =
    prove_thm (`NOT_EQ_LEQ`,
               "! a b : num . ~(a = b) = ((a < b) \/ (b < a))",
               REPEAT STRIP_TAC THEN
               REWRITE_TAC [INST [("~((a:num) = b)","t1:bool");
                                  ("((a < b) \/ (b < a))","t2:bool")]
                                 (SPEC_ALL NOT_EQ);
                            DE_MORGAN_THM;
                            NOT_LESS] THEN
               SUBST_TAC [SPECL ["b <= a";"a <= b"] CONJ_SYM] THEN
               REWRITE_TAC [EQ_LEQ]);;

let LESS_LESSEQ =
    prove_thm (`LESS_LESSEQ`,
               "!a b. (a < b) = ((a + 1) <= b)",
               REWRITE_TAC [SYM (SPEC_ALL ADD1); LESS_EQ]);;

close_theory();;
