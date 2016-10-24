%============================================================================%
% HOL theory to represent the "Birthday Book" from Chapter 1 of Spivey's     %
% "The Z Notation".                                                          %
%============================================================================%

%----------------------------------------------------------------------------%
% First load the ML code to support Z.                                       %
%----------------------------------------------------------------------------%

loadf `SCHEMA`;;

%----------------------------------------------------------------------------%
% Declare a new theory called `BirthdayBook`.                                %
%----------------------------------------------------------------------------%

force_new_theory `BirthdayBook`;;

%----------------------------------------------------------------------------%
% 1.2 The birthday book                                                      %
%----------------------------------------------------------------------------%

sets `NAME DATE`;;

declare
 `BirthdayBook`
 "SCHEMA
   [known :: (P NAME);
    birthday :: (NAME -+> DATE)]
   %---------------------------%
   [known = dom birthday]";;

declare
 `AddBirthday`
 "SCHEMA
   [DELTA BirthdayBook;
    name? :: NAME;
    date? :: DATE]
   %--------------------------------------------%
   [~(name? IN known);
    birthday' = birthday UNION {name? |-> date?}]";;

%----------------------------------------------------------------------------%
% Calculate the precondition of AddBirthday.                                 %
%----------------------------------------------------------------------------%

simp "pre AddBirthday";;

%----------------------------------------------------------------------------%
% The lemmma on page 5: known' = known U {name?}                             %
%----------------------------------------------------------------------------%

prove_theorem
 (`known_UNION`,
  "[AddBirthday] |-? (known' = known UNION {name?})",
  REWRITE_ALL_TAC[SCHEMA;CONJL;dom_UNION;dom_SING]);;

declare
 `FindBirthday`
 "SCHEMA
   [XI BirthdayBook;
    name? :: NAME;
    date! :: DATE]
   %-----------------------%
   [name? :: known;
    date! = birthday(name?)]";;

%----------------------------------------------------------------------------%
% Lemma proposed by Jonathan Bowen.                                          %
%----------------------------------------------------------------------------%

prove_theorem
 (`SEQ_AddBirthday_FindBirthday`,
  "[AddBirthday SEQ FindBirthday] |-? (date! = date?)",
  SIMP_TAC
   THEN POP_ASSUM STRIP_ASSUME_TAC
   THEN SMART_ELIMINATE_TAC
   THEN IMP_RES_TAC Ap_UNION2
   THEN ASM_REWRITE_TAC[]);;

declare
 `Remind`
 "SCHEMA
   [XI BirthdayBook;
    today? :: DATE;
    cards! :: P NAME]
   %---------------------------------------------------%
   [cards! = {n | n :: known /\ (birthday(n) = today?)}]";;

declare
 `InitBirthdayBook`
 "SCHEMA
   [BirthdayBook]
   %------------%
   [known = {}]";;

%----------------------------------------------------------------------------%
% 1.3 Strengthening the specification                                        %
%----------------------------------------------------------------------------%

free_set `REPORT = ok | already_known | not_known`;;

declare
 `Success`
 "SCHEMA
   [result! :: REPORT]
   %-----------------%
   [result! = ok]";;
 
declare
 `AlreadyKnown`
 "SCHEMA
   [XI BirthdayBook;
    name? :: NAME;
    result! :: REPORT]
   %-----------------------%
   [name? :: known;
    result! = already_known]";;

declare
 `RAddBirthday`
 "(AddBirthday AND Success) OR AlreadyKnown";;

%----------------------------------------------------------------------------%
% Checking RAddBirthday has correct precondition.                            %
%----------------------------------------------------------------------------%

simp "pre RAddBirthday";;

prove_theorem
 (`pre_RAddBirthday`,
  "[BirthdayBook; sig RAddBirthday] |-? pre RAddBirthday",
  REWRITE_ALL_TAC[SCHEMA;CONJL;::]
   THEN POP_ASSUM_LIST
         (\[th1;th2]. STRIP_ASSUME_TAC th2 THEN STRIP_ASSUME_TAC th1)
   THEN LITE_IMP_RES_TAC domPfunIN
   THEN ASM_REWRITE_TAC[]
   THEN EXISTS_TAC 
         "(name? IN dom birthday) => dom birthday | 
                                     dom(birthday UNION {name? |-> date?})"
   THEN EXISTS_TAC "(name? IN dom birthday) => birthday 
                                            | birthday UNION {name? |-> date?}"
   THEN EXISTS_TAC "(name? IN dom birthday) => already_known | ok"
   THEN ASM_CASES_TAC "name? IN dom birthday"
   THEN ASM_REWRITE_TAC[REPORT;IN_UNIV]
   THEN LITE_IMP_RES_TAC UNION_SING_Pfun
   THEN LITE_IMP_RES_TAC domPfunIN
   THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Equivalence between the definitions of RAddBirthday on pages 9 and 10.     %
%----------------------------------------------------------------------------%

prove_theorem
 (`RAddBirthdayLemma`,
  "(AddBirthday AND Success) OR AlreadyKnown =
   SCHEMA
    [DELTA BirthdayBook;
     name? :: NAME;
     date? :: DATE;
     result! :: REPORT]
    %---------------------------------------------------------%
    [(~(name? IN known) /\
              (birthday' = birthday UNION {name? |-> date?}) /\
              (result! = ok)) \/
     (name? IN known /\
              (birthday' = birthday) /\
              (result! = already_known))]",
  REWRITE_TAC[SCHEMA;PAIR_EQ;CONJL;::]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]);;

declare
 `NotKnown`
 "SCHEMA
   [XI BirthdayBook;
    name? :: NAME;
    result! :: REPORT]
   %-------------------%
   [~(name? IN known);
    result! = not_known]";;

declare
 `RFindBirthday`
 "(FindBirthday AND Success) OR NotKnown";;

declare
 `RRemind`
 "Remind AND Success";;

%----------------------------------------------------------------------------%
% 1.4 From specifications to designs                                         %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% 1.5 Implementing the birthday book                                         %
%----------------------------------------------------------------------------%

declare
 `BirthdayBook1`
 "SCHEMA
   [names :: (NN_1-->NAME);
    dates :: (NN_1-->DATE);
    hwm :: NN]
   %---------------------------------------------------%
   [!i j::(1..hwm). ~(i = j) ==> ~(names(i) = names(j))]";;

declare
 `Abs`
 "SCHEMA
   [BirthdayBook;
    BirthdayBook1]
   %-------------------------------------------%
   [known = {names(i) | i::(1..hwm)};
    !i::(1..hwm). birthday(names(i)) = dates(i)]";;

declare
 `AddBirthday1`
 "SCHEMA
   [DELTA BirthdayBook1;
    name? :: NAME;
    date? :: DATE]
   %-----------------------------------%
   [!i::(1..hwm). ~(name? = names(i));
    hwm' = hwm + 1;
    names' = names (+) {hwm' |-> name?};
    dates' = dates (+) {hwm' |-> date?}]";;

declare
 `FindBirthday1`
 "SCHEMA
   [XI BirthdayBook1;
    name? :: NAME;
    date! :: DATE]
   %------------------------------------------------------%
   [?i::(1..hwm). (name? = names(i)) /\ (date! = dates(i))]";;

declare
 `AbsCards`
 "SCHEMA
   [cards :: P NAME;
    cardlist :: (NN_1-->NAME);
    ncards :: NN]
   %----------------------------------------------%
   [cards = {cardlist(i) | i::(1..ncards)}]";;

declare
 `Remind1`
 "SCHEMA
   [XI BirthdayBook1;
    today? :: DATE;
    cardlist! :: (NN_1-->NAME);
    ncards! :: NN]
   %---------------------------------------------------------%
   [{cardlist!(i) | i::(1..ncards!)} =
    {names(j) | j::(1..hwm) /\ (dates(j) = today?)}]";;

declare
 `InitBirthdayBook1`
  "SCHEMA
    [BirthdayBook1]
    %-------------%
    [hwm = 0]";;


prove_theorem
 (`AbsThm1`,
  "FORALL [BirthdayBook; BirthdayBook1; (name?::NAME); (date?::DATE)]
    ((pre AddBirthday /\ Abs) ==> (pre AddBirthday1))",
  REWRITE_TAC[SCHEMA;CONJL;::;Interval_to;IN_Interval]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN SMART_ELIMINATE_TAC
   THEN EXISTS_TAC "names (+) {(hwm+1) |-> name?}"
   THEN EXISTS_TAC "dates (+) {(hwm+1) |-> date?}"
   THEN EXISTS_TAC "hwm+1"
   THEN LITE_IMP_RES_TAC OverrideSingFun
   THEN ASM_REWRITE_TAC[IN_NN]
   THEN CONJ_TAC
   THENL
    [REMOVE_RESTRICT_TAC
      THEN REWRITE_TAC[IncInterval;UnitInterval;|\/|]
      THEN REPEAT STRIP_TAC
      THENL
       [IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalSINGLemma)
         THEN POP_ASSUMS 2 (MAP_EVERY (ASSUME_TAC o SPEC "name?:NAME"))
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1)
         THEN RES_TAC
         THEN RW_ASM_THEN ACCEPT_TAC [GSYM o el 7;GSYM o el 8;el 11] (el 2);
        IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalSINGLemma)
         THEN POP_ASSUMS 1 (MAP_EVERY (ASSUME_TAC o SPEC "name?:NAME"))
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma2)
         THEN POP_ASSUM(ASSUME_TAC o SPEC "hwm:num")
         THEN RW_ASM_THEN ASSUME_TAC [el 6;el 4;el 1] (el 2)
         THEN ASSUM_LIST
               (IMP_RES_TAC o SPEC "x:num" o CONV_RULE NOT_EXISTS_CONV o 
                SET_SPEC_RULE o el 12);
        SMART_ELIMINATE_TAC
         THEN IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalSINGLemma)
         THEN POP_ASSUMS 1 (MAP_EVERY (ASSUME_TAC o SPEC "name?:NAME"))
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma2)
         THEN POP_ASSUM(ASSUME_TAC o SPEC "hwm:num")
         THEN RW_ASM_THEN ASSUME_TAC [el 4;el 2] (GSYM o el 1)
         THEN ASSUM_LIST
               (IMP_RES_TAC o SPEC "x:num" o CONV_RULE NOT_EXISTS_CONV o 
                SET_SPEC_RULE o el 11);
        SMART_ELIMINATE_TAC
         THEN IMP_RES_TAC (ARITH_PROVE "~(n+1 = n+1) ==> F")];
     REMOVE_RESTRICT_TAC
      THEN REPEAT STRIP_TAC
      THEN ASSUM_LIST
            (IMP_RES_TAC o SPEC "x:num" o CONV_RULE NOT_EXISTS_CONV o 
             SET_SPEC_RULE o el 6)]);;

prove_theorem
 (`AbsThm2`,
  "FORALL [BirthdayBook; BirthdayBook1; BirthdayBook1';
           (name?::NAME); (date?::DATE)]
    ((pre AddBirthday /\ Abs /\ AddBirthday1) 
     ==> 
     (EXISTS BirthdayBook' (Abs' /\ AddBirthday)))",
  REWRITE_TAC[SCHEMA;::;CONJL;Interval_to;IN_Interval]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN SMART_ELIMINATE_TAC
   THEN EXISTS_TAC "dom(birthday UNION {name? |-> date?})"
   THEN EXISTS_TAC "birthday UNION {name? |-> date?}"
   THEN IMP_RES_TAC domPfunIN
   THEN ASM_REWRITE_TAC[EXTENSION]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[dom_UNION;dom_SING;IN_UNION;IN_SING]
   THEN ASSUM_LIST(\thl. REWRITE_TAC[GSYM(el 20 thl)])
   THEN SET_SPEC_TAC
   THEN SMART_ELIMINATE_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [EQ_TAC
      THEN REPEAT STRIP_TAC
      THEN SMART_ELIMINATE_TAC
      THENL
       [EXISTS_TAC "i:num"
         THEN ASM_REWRITE_TAC[IncInterval;|\/|]
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1);
        EXISTS_TAC "hwm+1"
         THEN ASM_REWRITE_TAC[IncInterval;|\/|;UnitInterval]
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma2);
        POP_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[IncInterval;|\/|;UnitInterval])
         THENL
          [DISJ1_TAC
            THEN EXISTS_TAC "i:num"
            THEN ASM_REWRITE_TAC[IncInterval;|\/|]
            THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1);
           DISJ2_TAC
            THEN SMART_ELIMINATE_TAC
            THEN ASM_REWRITE_TAC[IncInterval;|\/|;UnitInterval]
            THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma2)]]
      THEN ASM_REWRITE_TAC[];
     REMOVE_RESTRICT_TAC
      THEN REWRITE_TAC[IncInterval;|\/|;UnitInterval]
      THEN REPEAT STRIP_TAC
      THENL
       [RES_TAC
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma1)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":DATE",":*"]IntervalApLemma1)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*";":DATE",":**"]Ap_UNION1);
        SMART_ELIMINATE_TAC
         THEN LITE_IMP_RES_TAC(INST_TYPE[":DATE",":*"]IntervalApLemma2)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*"]IntervalApLemma2)  
         THEN ASM_REWRITE_TAC[]
         THEN RW_ASM_THEN ASSUME_TAC [el 9] (AP_TERM "$IN(name?:NAME)" o el 22)
         THEN LITE_IMP_RES_TAC(INST_TYPE[":NAME",":*";":DATE",":**"]Ap_UNION2)]
      THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Spivey's "sufficient condition" for the correct implementation of          %
%                                                                            %
%    AddBirthday;Findbirthday                                                %
%                                                                            %
% See page 134 of ZRM2.                                                      %
%----------------------------------------------------------------------------%

prove_theorem
 (`AddFindSeq`,
  "FORALL 
    [BirthdayBook'']
    ((EXISTS [AddBirthday]  (theta BirthdayBook' = theta BirthdayBook''))
     ==>
     (EXISTS [FindBirthday] (theta BirthdayBook  = theta BirthdayBook'')))",
  REWRITE_TAC[SCHEMA;::;CONJL;Interval_to;IN_Interval;PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN SMART_ELIMINATE_TAC
   THEN EXISTS_TAC "known'':NAME set"
   THEN EXISTS_TAC "birthday'':(NAME # DATE)set"
   THEN EXISTS_TAC "known'':NAME set"
   THEN EXISTS_TAC "birthday'':(NAME # DATE)set"
   THEN EXISTS_TAC "name?:NAME"
   THEN EXISTS_TAC "date?:DATE"
   THEN ASM_REWRITE_TAC[dom_UNION;IN_UNION;dom_SING;IN_SING]
   THEN LITE_IMP_RES_TAC Ap_UNION2
   THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Spivey's "sufficient condition" for the correct implementation of          %
%                                                                            %
%    AddBirthday1;Findbirthday1                                              %
%                                                                            %
% See page 134 of ZRM2.                                                      %
%----------------------------------------------------------------------------%

prove_theorem
 (`AddFindSeq1`,
  "FORALL 
    [BirthdayBook1'']
    ((EXISTS [AddBirthday1]  (theta BirthdayBook1' = theta BirthdayBook1''))
     ==>
     (EXISTS [FindBirthday1] (theta BirthdayBook1  = theta BirthdayBook1'')))",
  REWRITE_TAC[SCHEMA;::;CONJL;Interval_to;IN_Interval;PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN SMART_ELIMINATE_TAC
   THEN EXISTS_TAC "names'':(num # NAME)set"
   THEN EXISTS_TAC "dates'':(num # DATE)set"
   THEN EXISTS_TAC "hwm'':num"
   THEN EXISTS_TAC "names'':(num # NAME)set"
   THEN EXISTS_TAC "dates'':(num # DATE)set"
   THEN EXISTS_TAC "hwm'':num"
   THEN EXISTS_TAC "name?:NAME"
   THEN EXISTS_TAC "date?:DATE"
   THEN ASM_REWRITE_TAC[]
   THEN REMOVE_RESTRICT_TAC
   THEN EXISTS_TAC "hwm+1"
   THEN REWRITE_TAC[IncInterval;|\/|;UnitInterval]
   THEN SMART_ELIMINATE_TAC
   THEN LITE_IMP_RES_TAC IntervalApLemma2
   THEN ASM_REWRITE_TAC[]);;

