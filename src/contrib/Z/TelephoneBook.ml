
%============================================================================%
% HOL theory to represent the "Telephone Book" from  the paper               %
% "A Simple Demonstration of Balzac" by Rodger Collinson                     %
%============================================================================%

%----------------------------------------------------------------------------%
% First load the ML code to support Z.                                       %
%----------------------------------------------------------------------------%

loadf `SCHEMA`;;

%----------------------------------------------------------------------------%
% Declare a new theory called `TelephoneBook`.                               %
%----------------------------------------------------------------------------%

force_new_theory `TelephoneBook`;;

%----------------------------------------------------------------------------%
% The telphone book                                                          %
%----------------------------------------------------------------------------%

sets `NUMBER SUBSCRIBER`;;

%!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!%
% The following two axioms are NOT assumed in Balzac, since it assumes       %
% ALL basic types are non-empty. This is not standard!                       %
%!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!%

declare_axiom "NUMBER =/= {}";;       

declare_axiom "SUBSCRIBER =/= {}";;

declare
 `TelephoneBook`
 "SCHEMA
   [book :: SUBSCRIBER -+> NUMBER;
    known :: (P SUBSCRIBER);
    free :: (P NUMBER)]
   %---------------------------%
   [known = dom book;
    free = NUMBER DIFF (ran book)]";;

%----------------------------------------------------------------------------%
% A general purpose tactic for proving goals of the form:                    %
%                                                                            %
%    |-? EXISTS [<schema>] true                                              %
%----------------------------------------------------------------------------%

let EXISTS_CONSISTENT_TAC =
 REWRITE_TAC[::;-+>;<->;><;P;SUBSET_DEF;NOT_IN_EMPTY;true_DEF]
  THEN SET_SPEC_TAC
  THEN REWRITE_TAC
        [NOT_IN_EMPTY;dom_EMPTY;ran_EMPTY;DIFF_EMPTY;IN_SING;UNION_EMPTY;
         dom_SING;ran_SING;NOT_IN;IN_DIFF;|->;PAIR_EQ]
  THEN SET_SPEC_TAC
  THEN REPEAT STRIP_TAC
  THEN ((EXISTS_TAC "CHOICE SUBSCRIBER" THEN EXISTS_TAC "CHOICE NUMBER")
        ORELSE ALL_TAC)
  THEN ASM_REWRITE_TAC
        [GSYM CHOICE;Axiom_1;Axiom_2;GSYM |->;RangeAntiResSING;Ap_SING];;

prove_theorem
 (`TelephoneBook_consistent`,
  "EXISTS [TelephoneBook] true",
  EXISTS_TAC "{}:(SUBSCRIBER # NUMBER)set"
   THEN EXISTS_TAC "{}:(SUBSCRIBER)set"
   THEN EXISTS_TAC "NUMBER"
   THEN EXISTS_CONSISTENT_TAC);;

declare
 `Connect`
 "SCHEMA
   [DELTA TelephoneBook;
    subscriber? :: SUBSCRIBER;
    number! :: NUMBER]
   %-------------------------------------------%
   [free =/= {};
    subscriber? NOT_IN known;
    number! IN free;
    book' = book UNION{subscriber? |-> number!}]";;

prove_theorem
 (`Connect_consistent`,
  "EXISTS [Connect] true",
  EXISTS_TAC "{}:(SUBSCRIBER # NUMBER)set"
   THEN EXISTS_TAC "{}:(SUBSCRIBER)set"
   THEN EXISTS_TAC "NUMBER"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER |-> CHOICE NUMBER}"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER}"
   THEN EXISTS_TAC "NUMBER DIFF {CHOICE NUMBER}"
   THEN EXISTS_TAC "CHOICE SUBSCRIBER"
   THEN EXISTS_TAC "CHOICE NUMBER"
   THEN EXISTS_CONSISTENT_TAC);;

prove_theorem
 (`Connect_proof_1`,
  "FORALL [Connect] (known' = known UNION {subscriber?})",
  REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[dom_UNION;dom_SING]);;

prove_theorem
 (`Connect_proof_2`,
  "FORALL [Connect] (free' = free DIFF {number!})",
  REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[ran_UNION;ran_SING;EXTENSION;DIFF_UNION]);;

declare
 `Disconnect`
 "SCHEMA
   [DELTA TelephoneBook;
    number? :: NUMBER]
   %-------------------------%
   [number? IN ran book;
    book' = book +> {number?}]";;

prove_theorem
 (`Disconnect_consistent`,
  "EXISTS [Disconnect] true",
  EXISTS_TAC "{CHOICE SUBSCRIBER |-> CHOICE NUMBER}"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER}"
   THEN EXISTS_TAC "NUMBER DIFF {CHOICE NUMBER}"
   THEN EXISTS_TAC "{}:(SUBSCRIBER # NUMBER)set"
   THEN EXISTS_TAC "{}:(SUBSCRIBER)set"
   THEN EXISTS_TAC "NUMBER"
   THEN EXISTS_TAC "CHOICE NUMBER"
   THEN EXISTS_CONSISTENT_TAC);;

prove_theorem
 (`Disconnect_proof_1`,
  "FORALL 
    [Disconnect] 
    (known' = known DIFF {s | s IN SUBSCRIBER /\ (book s = number?)})",
  REWRITE_TAC[::]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[DIFF_DEF;EXTENSION;+>;|->;dom;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ;IN_SING]
   THEN GEN_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN SMART_ELIMINATE_TAC
   THENL
    [EXISTS_TAC "y':NUMBER"
      THEN ASM_REWRITE_TAC[];
     LITE_IMP_RES_TAC ApFunCor
      THEN POP_ASSUM(ASSUME_TAC o SYM)
      THEN RES_TAC;
     EXISTS_TAC "y:NUMBER"
      THEN EXISTS_TAC "x:SUBSCRIBER"
      THEN EXISTS_TAC "y:NUMBER"
      THEN ASM_REWRITE_TAC[]
      THEN LITE_IMP_RES_TAC ApFunCor
      THEN LITE_IMP_RES_TAC IN_dom_ran
      THEN RW_ASM_THEN ACCEPT_TAC [el 2;el 3] (el 4)]);;

prove_theorem
 (`Disconnect_proof_2`,
  "FORALL 
    [Disconnect] 
    (free' = free UNION {number?})",
  REWRITE_TAC[::]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[DIFF_DEF;EXTENSION;+>;|->;ran;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ;IN_UNION;IN_SING]
   THEN GEN_TAC
   THEN SET_SPEC_TAC
   THEN CONV_TAC(TOP_DEPTH_CONV NOT_EXISTS_CONV)
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN SMART_ELIMINATE_TAC
   THEN ASM_REWRITE_TAC[]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN POP_ASSUM
        (STRIP_ASSUME_TAC                     o 
         CONV_RULE(DEPTH_CONV FORALL_OR_CONV) o
         GEN_ALL                              o
         REWRITE_RULE[DE_MORGAN_THM]          o 
         SPECL["x:SUBSCRIBER";"x:SUBSCRIBER";"x:NUMBER"])
   THEN ASM_REWRITE_TAC[]);;

declare
 `FindNumber`
 "SCHEMA
   [XI TelephoneBook;
    subscriber? :: SUBSCRIBER;
    number! :: NUMBER]
   %--------------------------%
   [subscriber? IN known;
    number! = book subscriber?]";;

prove_theorem
 (`FindNumber_consistent`,
  "EXISTS [FindNumber] true",
  REWRITE_TAC[PAIR_EQ]
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER |-> CHOICE NUMBER}"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER}"
   THEN EXISTS_TAC "NUMBER DIFF {CHOICE NUMBER}"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER |-> CHOICE NUMBER}"
   THEN EXISTS_TAC "{CHOICE SUBSCRIBER}"
   THEN EXISTS_TAC "NUMBER DIFF {CHOICE NUMBER}"
   THEN EXISTS_TAC "CHOICE SUBSCRIBER"
   THEN EXISTS_TAC "CHOICE NUMBER"
   THEN EXISTS_CONSISTENT_TAC);;

declare
 `initTelephoneBook`
 "SCHEMA
   [TelephoneBook]
   %-------------%
   [known = {}]";;

prove_theorem
 (`initTelephoneBook_consistent`,
  "EXISTS [initTelephoneBook] true",
  EXISTS_TAC "{}:(SUBSCRIBER # NUMBER)set"
   THEN EXISTS_TAC "{}:(SUBSCRIBER)set"
   THEN EXISTS_TAC "NUMBER"
   THEN EXISTS_CONSISTENT_TAC);;

free_set  `REPORT = ok 
                  | full_book 
                  | already_known 
                  | unknown_number 
                  | unknown_subscriber`;;

declare
 `Success`
 "SCHEMA
   [result! :: REPORT]
   %-----------------%
   [result! = ok]";;

declare
 `FullBook`
 "SCHEMA
   [XI TelephoneBook;
    result! :: REPORT]
   %-----------------%
   [free = {};
    result! = full_book]";;

declare
 `AlreadyKnown`
 "SCHEMA
   [XI TelephoneBook;
    subscriber? :: SUBSCRIBER;
    result! :: REPORT]
   %-----------------%
   [subscriber? IN known;
    result! = already_known]";;

declare
 `RConnect`
 "(Connect AND Success) OR FullBook OR AlreadyKnown";;

prove_theorem
 (`RConnect_total`,
  "FORALL [RConnect] (pre RConnect)",
  REWRITE_TAC[::;SCHEMA;CONJL;NOT_IN]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[DIFF_DEF;EXTENSION;+>;|->;dom;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ;IN_SING]
   THEN EXISTS_TAC
         "((free =/= {}) /\ (subscriber? NOT_IN known))
           => (book UNION {subscriber? |-> number!}) 
           | book"
   THEN EXISTS_TAC
         "((free =/= {}) /\ (subscriber? NOT_IN known))
          => dom(book UNION {subscriber? |-> number!}) |
             dom book"
   THEN EXISTS_TAC
         "((free =/= {}) /\ (subscriber? NOT_IN known))
          => NUMBER DIFF ran(book UNION {subscriber? |-> number!}) |
             NUMBER DIFF ran book"
   THEN EXISTS_TAC "number!"
   THEN EXISTS_TAC "result!"
   THEN ASM_CASES_TAC "(free =/= {}) /\ (subscriber? NOT_IN known)"
   THEN LITE_IMP_RES_TAC UNION_SING_IN_P
   THEN LITE_IMP_RES_TAC domPfunIN
   THEN LITE_IMP_RES_TAC ranPfunIN
   THEN SMART_ELIMINATE_TAC
   THEN LITE_IMP_RES_TAC UNION_SING_Pfun
   THEN ASM_REWRITE_TAC[DIFF_IN_P]
   THEN RW_ASM_THEN ASSUME_TAC [K =/=;K NOT_IN;K DE_MORGAN_THM;el 10] (el 7)
   THEN RES_TAC
   THEN ASM_F_TAC);;

declare
 `UnknownNumber`
 "SCHEMA
   [XI TelephoneBook;
    number? :: NUMBER;
    result! :: REPORT]
   %-----------------%
   [number? IN free;
    result! = unknown_number]";;

declare
 `RDisconnect`
 "(Disconnect AND Success) OR UnknownNumber";;

prove_theorem
 (`RDisconnect_total`,
  "FORALL [RDisconnect] (pre RDisconnect)",
  REWRITE_TAC[::;SCHEMA;CONJL;NOT_IN]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[DIFF_DEF;EXTENSION;+>;|->;dom;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ;IN_SING]
   THEN EXISTS_TAC
         "(number? IN ran book /\ (result! = ok))
           => book +> {number?}
           | book"
   THEN EXISTS_TAC
         "(number? IN ran book /\ (result! = ok))
          => dom(book +> {number?}) |
             dom book"
   THEN EXISTS_TAC
         "(number? IN ran book /\ (result! = ok))
          => NUMBER DIFF ran(book +> {number?}) |
             NUMBER DIFF ran book"
   THEN EXISTS_TAC "result!"
   THEN ASM_CASES_TAC "number? IN ran book /\ (result! = ok)"
   THEN LITE_IMP_RES_TAC UNION_SING_IN_P
   THEN LITE_IMP_RES_TAC domPfunIN
   THEN LITE_IMP_RES_TAC ranPfunIN
   THEN SMART_ELIMINATE_TAC
   THEN LITE_IMP_RES_TAC UNION_SING_Pfun
   THEN LITE_IMP_RES_TAC RangeAntiResPfun
   THEN LITE_IMP_RES_TAC domRangeAntiResPfun
   THEN REWRITE_ASMS_TAC[]
   THEN ASM_REWRITE_TAC[DIFF_IN_P]
   THEN RES_TAC);;

declare
 `UnknownSubscriber`
 "SCHEMA
   [XI TelephoneBook;
    subscriber? :: SUBSCRIBER;
    result! :: REPORT]
   %-----------------%
   [subscriber? NOT_IN known;
    result! = unknown_subscriber]";;

declare
 `RFindNumber`
 "(FindNumber AND Success) OR UnknownSubscriber";;

prove_theorem
 (`RFindNumber_total`,
  "FORALL [RFindNumber] (pre RFindNumber)",
  REWRITE_TAC[::;SCHEMA;CONJL;NOT_IN]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[DIFF_DEF;EXTENSION;+>;|->;dom;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ;IN_SING]
   THEN EXISTS_TAC "book"
   THEN EXISTS_TAC "known"
   THEN EXISTS_TAC "free"
   THEN EXISTS_TAC 
         "(subscriber? IN dom book) => book^^subscriber? | number!"
   THEN EXISTS_TAC "(subscriber? IN dom book) => ok | unknown_subscriber"
   THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 4)
   THEN SMART_ELIMINATE_TAC
   THEN (SMART_ELIMINATE_TAC ORELSE ALL_TAC)
   THEN ASM_REWRITE_TAC[REPORT;IN_UNIV]);;
