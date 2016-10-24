% mk_BINOMIAL.ml %
% The Binomial Theorem proven in HOL %
`[mk_BINOMIAL.ml] Last modified on Wed Jul 24 14:28:28 BST 1991 by adg`;;

can unlink `BINOMIAL.th`;;
new_theory `BINOMIAL`;;

set_flag (`timing`, true);;
set_flag (`print_restrict`, true);;

% ------------------------------------------------------------------------- %
% Naming policy.                                                            %
%                                                                           %
% Variables are lower case, theorems and constants are lower case,          %
% except for the constants "Id", "Inv", "Group".                            %
% This is entirely because "ID", "INV" and "GROUP" exist in Elsa Gunter's   %
% theory of groups, used by her theory of integers, which is the only       %
% example ring that exists in the HOL release (as of July 1991).            %
% By the way, one intention for the present theory is that it be            %
% standalone, which is why all the needed group theory is developed here    %
% from scratch (and in a more limited way than Elsa Gunter's theory).       %
% But I do admit that it is ironic that the only example ring in the        %
% release is the `integer` library!                                         %
% ------------------------------------------------------------------------- %

% ------------------------------------------------------------------------- %
% Derived rules.                                                            %
% ------------------------------------------------------------------------- %

let DEEP_SYM t = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) t;;

%
SPEC(L)_EQ - HOL derived rule, specialise variable(s) in an equivalence

        A |- !u1,...,un. t1[u1,...,un] = t2[u1,...,un]
    ----------------------------------------------------
        A u t1[v1,...,vn] |- t2[v1,...,vn]
%

let SPEC_EQ v th = UNDISCH(fst(EQ_IMP_RULE (SPEC v th)));;
let SPECL_EQ vs th = UNDISCH(fst(EQ_IMP_RULE (SPECL vs th)));;

%
SPEC(L)_IMP - HOL derived rule, specialise variable(s) in an implication

        A |- !u1,...,un. t1[u1,...,un] ==> t2[u1,...,un]
    ------------------------------------------------------
        A u t1[v1,...,vn] |- t2[v1,...,vn]
%

let SPEC_IMP v th = UNDISCH(SPEC v th);;
let SPECL_IMP vs th = UNDISCH(SPECL vs th);;
let STRIP_SPEC_IMP v th =
    UNDISCH_ALL(SPEC v (CONV_RULE (ONCE_DEPTH_CONV ANTE_CONJ_CONV) th));;

% ========================================================================= %
% Part I:  The Binomial Coefficients                                        %
% ========================================================================= %

% ------------------------------------------------------------------------- %
% The binomial coefficient, CHOOSE n k, is the number of ways to choose     %
% a k-element subset of an n-element set.  Binomial coefficients are        %
% represented by the logical constant CHOOSE: num -> num -> num, whose      % 
% meaning is completely specified by the following theorem, CHOOSE_DEF:     %
%                                                                           %
% CHOOSE_DEF =                                                              %
%   |- (!n. CHOOSE n 0 = 1) /\                                              %
%      (!k. CHOOSE 0 (SUC k) = 0) /\                                        %
%      (!n k. CHOOSE (SUC n) (SUC k) = CHOOSE n (SUC k) + CHOOSE n k)       %
%                                                                           %
% It is natural to define CHOOSE by primitive recursion, but CHOOSE_DEF     %
% isn't in the form of a primitive recursive definition, so an equivalent   %
% theorem, RAW_CHOOSE_DEF, is used to define the constant CHOOSE,           %
% and then CHOOSE_DEF is a derived theorem.  RAW_CHOOSE_DEF is used only    %
% to define CHOOSE_DEF; the conditional expressions within it make it       %
% fiddly to use for rewriting.                                              %
% ------------------------------------------------------------------------- %

let base_and_inductive =
    "(CHOOSE 0 k = ((0 = k) => 1 | 0)) /\
     (CHOOSE (SUC n) k =
         ((0 = k) => 1 | (CHOOSE n (k-1)) + (CHOOSE n k)))";;

let RAW_CHOOSE_DEF = prove_rec_fn_exists num_Axiom base_and_inductive;;

let CHOOSE_DEF_LEMMA =
    prove
    ("?CHOOSE.
      (!n. CHOOSE n 0 = 1) /\
      (!k. CHOOSE 0 (SUC k) = 0) /\
      (!n k. CHOOSE (SUC n) (SUC k) = CHOOSE n (SUC k) + CHOOSE n k)",
    STRIP_ASSUME_TAC RAW_CHOOSE_DEF THEN
    EXISTS_TAC "CHOOSE : num -> num -> num" THEN
    REPEAT CONJ_TAC THENL
    [INDUCT_TAC THEN ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [SUC_NOT];
     ASM_REWRITE_TAC [SUC_NOT;SUC_SUB1] THEN
     REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC ADD_SYM]);;

let CHOOSE_DEF =
    new_specification `CHOOSE_DEF` [`constant`,`CHOOSE`] CHOOSE_DEF_LEMMA;;

% ------------------------------------------------------------------------- %
% Some basic lemmas about binomial coefficients:                            %
%                                                                           %
% CHOOSE_LESS_LEMMA = |- !m n. CHOOSE m (SUC(m + n)) = 0                    %
% CHOOSE_LESS = |- !n k. n < k ==> (CHOOSE n k = 0)                         %
% CHOOSE_SAME = |- !n. CHOOSE n n = 1                                       %
%                                                                           %
% CHOOSE_SUC and CHOOSE_LESS amount to the same fact: CHOOSE_LESS is        %
% perhaps the easier of the two to use, but is proven as a corollary of     %
% CHOOSE_SUC, which is the easier of the two to prove.                      %
% ------------------------------------------------------------------------- %

let CHOOSE_LESS_LEMMA =
    prove
    ("!m n. CHOOSE m (SUC(m + n)) = 0",
    INDUCT_TAC THENL
       [REWRITE_TAC [CHOOSE_DEF];
        ASM_REWRITE_TAC [CHOOSE_DEF; ADD_CLAUSES] THEN
        STRIP_TAC THEN
        SUBST1_TAC (SPEC_ALL ADD_SUC) THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let CHOOSE_LESS =
    prove_thm
    (`CHOOSE_LESS`,
    "!n k. n < k ==> (CHOOSE n k = 0)",
    REPEAT STRIP_TAC THEN
    IMP_RES_THEN (CHOOSE_THEN SUBST1_TAC) LESS_ADD_1 THEN
    REWRITE_TAC[num_CONV "1"; DEEP_SYM ADD_SUC; CHOOSE_LESS_LEMMA]);;
    
let CHOOSE_SAME =
    prove_thm
    (`CHOOSE_SAME`,
    "!n. CHOOSE n n = 1",
    INDUCT_TAC THENL
       [REWRITE_TAC [CHOOSE_DEF];
        ASSUME_TAC (SPEC_ALL LESS_SUC_REFL) THEN
        IMP_RES_TAC CHOOSE_LESS THEN
        ASM_REWRITE_TAC [ADD_CLAUSES; CHOOSE_DEF]]);;
        
% ========================================================================= %
% Part II:  Monoids, groups and commutative rings                           %
% ========================================================================= %

% ------------------------------------------------------------------------- %
% The following terms are antiquoted to minimise explicit type information. %
% ------------------------------------------------------------------------- %

let plus,times = "plus: *->*->*", "times: *->*->*";;

% ------------------------------------------------------------------------- %
% Associativity and commutativity.                                          %
% ------------------------------------------------------------------------- %

let ASSOCIATIVE =
    new_definition (`ASSOCIATIVE`,
      "!plus: *->*->*. ASSOCIATIVE plus =
          (!a b c. plus a (plus b c) = plus (plus a b) c)");;

let COMMUTATIVE =
    new_definition (`COMMUTATIVE`,
      "!plus: *->*->*. COMMUTATIVE plus =
          (!a b. plus a b = plus b a)");;

% ------------------------------------------------------------------------- %
% An example permutation of an associative, commutative operator.           %
%                                                                           %
% This is only here to be a simple example of proofs about an arbitrary     %
% operator.  At one time it was needed as a lemma, but now that AC_CONV     %
% has been added to HOL, there is no need for it.                           %
% ------------------------------------------------------------------------- %

let PERM =
    prove_thm
    (`PERM`,
    "!plus: *->*->*. ASSOCIATIVE plus /\ COMMUTATIVE plus ==>
        !a b c. plus (plus a b) c = plus b (plus a c)",
    REPEAT STRIP_TAC THEN
    SUBST1_TAC (SPECL ["a:*";"b:*"] (SPEC_EQ plus COMMUTATIVE)) THEN
    PURE_ONCE_REWRITE_TAC [SPEC_EQ plus ASSOCIATIVE] THEN
    REFL_TAC);;

% ------------------------------------------------------------------------- %
% Associative, commutative rewriting.                                       %
% AC_CONV_RATOR is a version of the builtin function AC_CONV, specialised   %
% to deal with operators assumed to be ASSOCIATIVE and COMMUTATIVE.         %
% Given an operator together with an equation between two permutations      %
% of the same terms, AC_CONV_RATOR proves the equation, by assuming that    %
% the operator is both ASSOCIATIVE and COMMUTATIVE.                         %
%                                                                           %
% Example:                                                                  %
% #AC_CONV_RATOR plus                                                       %
% #    "(plus:*->*->*) (plus a b) c = plus b (plus a c)";;                  %
% ASSOCIATIVE plus, COMMUTATIVE plus |- plus(plus a b)c = plus b(plus a c)  %
% ------------------------------------------------------------------------- %

let AC_CONV_RATOR plus eqn =
    let th = AC_CONV (SPEC_EQ plus ASSOCIATIVE, SPEC_EQ plus COMMUTATIVE) eqn
    in MP (snd(EQ_IMP_RULE th)) TRUTH;;

% ------------------------------------------------------------------------- %
% Left and right identity elements in a monoid.                             % 
% ------------------------------------------------------------------------- %

let ID_LEMMA =
    prove
    ("?Id. !plus.
          (?u:*. (!a:*. plus u a = a) /\ (!a:*. plus a u = a)) ==>
              (!a. plus (Id plus) a = a) /\ (!a. plus a (Id plus) = a)",
     EXISTS_TAC "\plus.@u:*.(!a:*. (plus u a = a)) /\ !a. (plus a u = a)" THEN
     GEN_TAC THEN 
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC);;

let ID =
    new_specification `Id` [`constant`, `Id`] ID_LEMMA;;

let LEFT_ID =
    new_definition (`LEFT_ID`,
      "LEFT_ID (plus: *->*->*) = (!a. plus (Id plus) a = a)");;

let RIGHT_ID =
    new_definition (`RIGHT_ID`,
      "RIGHT_ID (plus: *->*->*) = (!a. plus a (Id plus) = a)");;

let UNIQUE_LEFT_ID =
    prove_thm
    (`UNIQUE_LEFT_ID`,
     "!plus. LEFT_ID plus /\ RIGHT_ID plus ==>
          !l:*. (!a. plus l a = a) ==> (Id plus = l)",
    REPEAT STRIP_TAC THEN
    PURE_ONCE_REWRITE_TAC [SYM(SPEC "l:*" (SPEC_EQ plus RIGHT_ID))] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SPEC_EQ plus RIGHT_ID]);;

let UNIQUE_RIGHT_ID =
    prove_thm
    (`UNIQUE_RIGHT_ID`,
     "!plus. LEFT_ID plus /\ RIGHT_ID plus ==>
          !r:*. (!a. plus a r = a) ==> (Id plus = r)",
    REPEAT STRIP_TAC THEN
    PURE_ONCE_REWRITE_TAC [SYM(SPEC "r:*" (SPEC_EQ plus LEFT_ID))] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SPEC_EQ plus LEFT_ID]);;

% ------------------------------------------------------------------------- %
% Monoids.                                                                  % 
% ------------------------------------------------------------------------- %

let RAW_MONOID =
    new_definition (`RAW_MONOID`,
      "!plus: *->*->*. MONOID plus =
          ASSOCIATIVE plus /\
          (?u. (!a. plus u a = a) /\ (!a. plus a u = a))");;

let MONOID =
    prove_thm
    (`MONOID`,
     "!plus. MONOID (plus: *->*->*) =
        LEFT_ID plus /\ RIGHT_ID plus /\ ASSOCIATIVE plus",
    PURE_ONCE_REWRITE_TAC [RAW_MONOID; LEFT_ID; RIGHT_ID] THEN
    GEN_TAC THEN EQ_TAC THENL 
    [REPEAT STRIP_TAC THEN
     IMP_RES_TAC ID THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
     REPEAT STRIP_TAC THENL
     [FIRST_ASSUM MATCH_ACCEPT_TAC;
      EXISTS_TAC "Id(plus:*->*->*)" THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

% ------------------------------------------------------------------------- %
% Left and right inverses are sometimes called left and right units.        %
% ------------------------------------------------------------------------- %

let INV_LEMMA =
    prove
    ("?Inv. !plus.
        (!a:*. ?b:*. (plus b a = Id plus) /\ (plus a b = Id plus)) ==>
        (!a:*. (plus (Inv plus a) a = Id plus) /\
               (plus a (Inv plus a) = Id plus))",
     EXISTS_TAC
         "\plus.\a:*.@b:*.(plus b a = Id plus) /\ (plus a b = Id plus)" THEN
     GEN_TAC THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     DISCH_TAC THEN
     GEN_TAC THEN
     CONV_TAC SELECT_CONV THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC);;

let INV =
    new_specification `Inv` [`constant`, `Inv`] INV_LEMMA;;

let LEFT_INV =
    new_definition (`LEFT_INV`,
      "!plus. LEFT_INV (plus: *->*->*) =
          !a. plus (Inv plus a) a = Id plus");;

let RIGHT_INV =
    new_definition (`RIGHT_INV`,
      "!plus. RIGHT_INV (plus: *->*->*) =
          !a. plus a (Inv plus a) = Id plus");;

% ------------------------------------------------------------------------- %
% Groups.                                                                   % 
% ------------------------------------------------------------------------- %

let RAW_GROUP =
    new_definition (`RAW_GROUP`,
      "!plus:*->*->*. Group plus =
          MONOID plus /\
          !a. ?b. (plus b a = Id plus) /\ (plus a b = Id plus)");;

let GROUP =
    prove_thm
    (`GROUP`,
     "!plus. Group (plus: *->*->*) =
          MONOID plus /\ LEFT_INV plus /\ RIGHT_INV plus",
    PURE_ONCE_REWRITE_TAC [RAW_GROUP; LEFT_INV; RIGHT_INV] THEN
    GEN_TAC THEN EQ_TAC THENL 
       [REPEAT STRIP_TAC THEN
        IMP_RES_TAC INV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
        REPEAT STRIP_TAC THENL
           [FIRST_ASSUM MATCH_ACCEPT_TAC;
            EXISTS_TAC "Inv (plus:*->*->*) (a:*)" THEN
            CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

% ------------------------------------------------------------------------- %
% The backwards proof of RIGHT_CANCELLATION goes as follows:                %
%                                                                           %
%    b = c                                                                  %
%    plus b (Id plus) = plus c (Id plus)                                    %
%    plus b (plus a (Inv plus a)) = plus c (plus a (Inv plus a))            %
%    plus (plus b a) (Inv plus a) = plus (plus c a) (Inv plus a)            %
%                                                                           %
% and the last line follows from the assumption (plus b a = plus c a).      %
% ------------------------------------------------------------------------- %

let RIGHT_CANCELLATION =
    prove_thm
    (`RIGHT_CANCELLATION`,
     "!plus. Group (plus: *->*->*) ==>
         !a b c. ((plus b a = plus c a) ==> (b = c))",
    REWRITE_TAC [GROUP; MONOID] THEN
    REPEAT STRIP_TAC THEN
    SUBST1_TAC (SYM (SPEC "b:*" (SPEC_EQ plus RIGHT_ID))) THEN
    SUBST1_TAC (SYM (SPEC "c:*" (SPEC_EQ plus RIGHT_ID))) THEN
    SUBST1_TAC (SYM (SPEC "a:*" (SPEC_EQ plus RIGHT_INV))) THEN
    ASM_REWRITE_TAC [SPEC_EQ plus ASSOCIATIVE]);;

let UNIQUE_LEFT_INV =
    prove_thm
    (`UNIQUE_LEFT_INV`,
     "!plus. Group plus ==>
          !a l:*. (plus l a = Id plus) ==> (Inv plus a = l)",
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC GROUP THEN
    MATCH_MP_TAC
        (SPECL ["a:*";"Inv ^plus a";"l:*"]
        (SPEC_IMP plus RIGHT_CANCELLATION)) THEN
    ASM_REWRITE_TAC[SPEC_EQ plus LEFT_INV]);;

% ------------------------------------------------------------------------- %
% Commutative rings.                                                        %
% ------------------------------------------------------------------------- %

let LEFT_DISTRIB =
    new_definition (`LEFT_DISTRIB`,
      "LEFT_DISTRIB (^plus, ^times) =
          (!a b c. ^times a (^plus b c) = ^plus (^times a b) (^times a c))");;

let RIGHT_DISTRIB =
    new_definition (`RIGHT_DISTRIB`,
      "RIGHT_DISTRIB (^plus, ^times) =
          (!a b c. ^times (^plus a b) c = ^plus (^times a c) (^times b c))");;

let RING =
    new_definition (`RING`,
      "RING ((plus: *->*->*), (times: *->*->*)) =
          Group plus /\
          COMMUTATIVE plus /\ 
          MONOID times /\
          COMMUTATIVE times /\ 
          LEFT_DISTRIB (plus, times) /\
          RIGHT_DISTRIB (plus, times)");;

% An implicative theorem used by RING_TAC %
let RING_LEMMA =
    prove_thm
    (`RING_LEMMA`,
    "!plus. !times.
        RING (plus: *->*->*, times: *->*->*) ==>
          RING (plus, times) /\
          Group plus /\
          MONOID plus /\
          LEFT_ID plus /\ RIGHT_ID plus /\
          ASSOCIATIVE plus /\
          LEFT_INV plus /\ RIGHT_INV plus /\
          COMMUTATIVE plus /\
          MONOID times /\
          LEFT_ID times /\ RIGHT_ID times /\
          ASSOCIATIVE times /\
          COMMUTATIVE times /\
          LEFT_DISTRIB (plus, times) /\ RIGHT_DISTRIB (plus, times)",
    GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    IMP_RES_TAC RING THEN
    IMP_RES_TAC GROUP THEN
    IMP_RES_TAC MONOID THEN
    ASM_REWRITE_TAC[]);;

%
         !x y. RING(x,y) ==> t[x,y]
       ==================================     RING_TAC
         { MP RING_LEMMA "RING(x,y)" } t[x,y]

Note the use of STRIP_ASSUME_TAC rather than merely ASSUME_TAC so that
each of the conjuncts in the conclusion of RING end up as separate assumptions.
%

let RING_TAC =
    GEN_TAC THEN GEN_TAC THEN
    DISCH_THEN (\th. STRIP_ASSUME_TAC (MATCH_MP RING_LEMMA th));;

% ------------------------------------------------------------------------- %
% The backwards proof of RING_0 goes as follows,                            %
% where 0 means (Id plus), a+b means (plus a b), and a*b means (times a b)  %
%                                                                           %
%    0*a = 0                                                                %
%    (0*a) + (b*a) = 0 + (b*a)                                              %
%    (0+b)*a = b*a                                                          %
%    b*a = b*a                                                              %
% ------------------------------------------------------------------------- %

let tactic(sub, distrib) =
    MATCH_MP_TAC (SPECL sub (SPEC_IMP plus RIGHT_CANCELLATION)) THEN
    PURE_ONCE_REWRITE_TAC [DEEP_SYM distrib] THEN
    REWRITE_TAC [SPEC_EQ plus LEFT_ID];;

let RING_0 =
    prove_thm
    (`RING_0`,
    "!plus: *->*->*. !times: *->*->*. RING (plus,times) ==>
        (!a. times (Id plus) a = (Id plus)) /\
        (!a. times a (Id plus) = (Id plus))",
    RING_TAC THEN
    REPEAT STRIP_TAC THENL map tactic
       [(["^times (Id ^plus) a";"^times b a";"Id ^plus"],
         SPECL_EQ [plus;times] RIGHT_DISTRIB);
        (["^times a (Id ^plus)";"^times a b";"Id ^plus"],
         SPECL_EQ [plus;times] LEFT_DISTRIB)]);;

% ========================================================================= %
% Part III:  Powers, Reductions, Ranges and Sums                            %
% ========================================================================= %

% ------------------------------------------------------------------------- %
% Raising an element of a monoid to a numeric power.                        %
% ------------------------------------------------------------------------- %

let POWER =
    new_recursive_definition false num_Axiom `POWER`
      "(POWER plus 0 (a:*) = Id plus) /\
       (POWER plus (SUC n) (a:*) = plus a (POWER plus n a))";;

let POWER_1 =
    prove_thm
    (`POWER_1`,
    "!plus: *->*->*. MONOID plus ==> (POWER plus 1 a = a)",
    PURE_REWRITE_TAC [MONOID; POWER; num_CONV "1"; RIGHT_ID] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC []);;

let POWER_DISTRIB =
    prove_thm
    (`POWER_DISTRIB`,
    "!plus: *->*->*. !times: *->*->*. RING(plus, times) ==>
        !a b n. times a (POWER plus n b) = POWER plus n (times a b)",
    RING_TAC THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
       [PURE_ONCE_REWRITE_TAC [POWER] THEN
        REWRITE_TAC [SPECL_IMP [plus;times] RING_0];
        PURE_ONCE_REWRITE_TAC [POWER] THEN
        ASM_REWRITE_TAC [SPECL_EQ [plus;times] LEFT_DISTRIB] ]);;
        
let POWER_ADD =
    prove_thm
    (`POWER_ADD`,
    "!plus: *->*->*. MONOID plus ==>
        !m n (a:*).
            (POWER plus (m+n) a) = plus (POWER plus m a) (POWER plus n a)",
    PURE_REWRITE_TAC [MONOID; LEFT_ID; ASSOCIATIVE] THEN
    GEN_TAC THEN STRIP_TAC THEN
    INDUCT_TAC THEN GEN_TAC THEN
    ASM_REWRITE_TAC [ADD; POWER]);;

% ------------------------------------------------------------------------- %
% Reducing a list of elements from a monoid.                                %
% ------------------------------------------------------------------------- %

let REDUCE =
    new_list_rec_definition (`REDUCE`,
      "(!plus. (REDUCE plus NIL) = (Id plus):*) /\
       (!plus (a:*) as. REDUCE plus (CONS a as) = plus a (REDUCE plus as))");;

% ------------------------------------------------------------------------- %
% Some list theoretic results not in the theory `list`.                     %
% ------------------------------------------------------------------------- %
  
let REDUCE_APPEND =
    prove_thm
    (`REDUCE_APPEND`,
     "!plus: *->*->*. MONOID plus ==>
        (!as bs. (REDUCE plus) (APPEND as bs) =
                    plus (REDUCE plus as) (REDUCE plus bs))",
    PURE_REWRITE_TAC [MONOID; LEFT_ID; ASSOCIATIVE] THEN
    GEN_TAC THEN STRIP_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [REDUCE; APPEND]);;

let REDUCE_MAP_MULT =
    prove_thm
    (`REDUCE_MAP_MULT`,
     "!plus: *->*->*. !times: *->*->*. RING (plus, times) ==>
        (!a. !bs. (REDUCE plus) (MAP (times a) bs) =
                      times a (REDUCE plus bs))",
    RING_TAC THEN
    GEN_TAC THEN LIST_INDUCT_TAC THENL
       [REWRITE_TAC [REDUCE; MAP; SPECL_IMP [plus;times] RING_0] ;
        ASM_REWRITE_TAC [MAP; REDUCE; SPECL_EQ [plus;times] LEFT_DISTRIB] ]);;

let REDUCE_MAP =
    prove_thm
    (`REDUCE_MAP`,
     "!plus: *->*->*. MONOID plus /\ COMMUTATIVE plus ==>
        !f:num->*. !g as.
            REDUCE plus (MAP (\k:num. plus (f k) (g k)) as)
                = plus (REDUCE plus (MAP f as)) (REDUCE plus (MAP g as))",
    PURE_REWRITE_TAC [MONOID; LEFT_ID] THEN
    GEN_TAC THEN STRIP_TAC THEN
    GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THENL
       [ASM_REWRITE_TAC [MAP; REDUCE] ;
        ASM_REWRITE_TAC [MAP; REDUCE] THEN
        BETA_TAC THEN
        GEN_TAC THEN
        CONV_TAC
            (AC_CONV (SPEC_EQ plus ASSOCIATIVE, SPEC_EQ plus COMMUTATIVE)) ]);;

% Load theorem MAP_o by hand. %
let MAP_o = theorem `tydefs` `MAP_o`;;

% ------------------------------------------------------------------------- %
% Definition of RANGE and INTERVAL.                                         %
%                                                                           %
% INTERVAL is not used, because although it would admit the standard        %
% definition of SIGMA, it is a bit unwieldy to manipulate because of        %
% the conditionals in its definition.                                       %
% ------------------------------------------------------------------------- %

let RANGE = 
    new_recursive_definition false num_Axiom `RANGE`
      "(RANGE m 0 = NIL) /\
       (RANGE m (SUC n) = CONS m (RANGE (SUC m) n))";;

let INTERVAL =
    new_recursive_definition false num_Axiom `INTERVAL`
      "(INTERVAL m 0 =
          (m > 0) => NIL | [0]) /\
       (INTERVAL m (SUC n) =
          (m > (SUC n)) => NIL | APPEND (INTERVAL m n) ([SUC n]))";;

% ------------------------------------------------------------------------- %
% Proofs of some properties of RANGE.                                       %
% ------------------------------------------------------------------------- %

let RANGE_TOP =
    prove_thm
    (`RANGE_TOP`,
    "!n m. RANGE m (SUC n) = APPEND (RANGE m n) [m+n]",
    INDUCT_TAC THENL
       [REWRITE_TAC [RANGE; APPEND; ADD_0];
        REWRITE_TAC [APPEND] THEN
        ONCE_REWRITE_TAC [RANGE] THEN
        POP_ASSUM(\th. REWRITE_TAC[th]) THEN
        REWRITE_TAC[APPEND; ADD; ADD_SUC] ]);;

let RANGE_SHIFT =
    prove_thm
    (`RANGE_SHIFT`,
    "!n m. RANGE (SUC m) n = MAP SUC (RANGE m n)",
    INDUCT_TAC THEN
    (GEN_TAC THEN ASM_REWRITE_TAC [RANGE; MAP]));;

% ------------------------------------------------------------------------- %
% Definition of SIGMA.                                                      %
% ------------------------------------------------------------------------- %

let SIGMA =
    new_definition (`SIGMA`,
      "SIGMA (plus,m,n) f = REDUCE plus (MAP f (RANGE m n)): *");;

% ------------------------------------------------------------------------- %
% Proofs of some properties of SIGMA.                                       %
% ------------------------------------------------------------------------- %

let SIGMA_ID =
    prove_thm
    (`SIGMA_ID`,
    "!plus:*->*->*. !m f. SIGMA (plus,m,0) f = Id plus",
    REWRITE_TAC [SIGMA; MAP; REDUCE; RANGE]);;

let SIGMA_LEFT_SPLIT =
    prove_thm
    (`SIGMA_LEFT_SPLIT`,
     "!plus:*->*->*. !m n f.
        SIGMA (plus,m,SUC n) f = plus (f m) (SIGMA (plus,SUC m,n) f)",
    REWRITE_TAC [SIGMA; MAP; REDUCE; RANGE]);;

let SIGMA_RIGHT_SPLIT =
    prove_thm
    (`SIGMA_RIGHT_SPLIT`,
     "!plus: *->*->*. MONOID plus ==>
      !m n f. SIGMA (plus,m,SUC n) f = plus (SIGMA (plus,m,n) f) (f (m+n))",
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC MONOID THEN
    ASM_REWRITE_TAC
        [SIGMA; RANGE_TOP; MAP_APPEND; REDUCE; MAP;
         SPEC_IMP plus REDUCE_APPEND; SPEC_EQ plus RIGHT_ID]);;

let SIGMA_SHIFT =
    prove_thm
    (`SIGMA_SHIFT`,
     "!(plus: *->*->*) m n f.
        SIGMA (plus,SUC m,n) f = SIGMA (plus,m,n) (f o SUC)",
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [SIGMA; RANGE_SHIFT; MAP_o; o_DEF] THEN
     BETA_TAC THEN
     REFL_TAC);;

let SIGMA_MULT_COMM =
    prove_thm
    (`SIGMA_MULT_COMM`,
     "!plus: *->*->*. !times: *->*->*. RING (plus, times) ==>
        !m n a f. times a (SIGMA (plus,m,n) f) =
                   SIGMA (plus,m,n) ((times a) o f)",
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [SIGMA; MAP_o; o_DEF] THEN
     BETA_TAC THEN
     REWRITE_TAC [SPECL_IMP [plus;times] REDUCE_MAP_MULT]);;

let SIGMA_PLUS_COMM =
    prove_thm
    (`SIGMA_PLUS_COMM`,
     "!plus: *->*->*. MONOID plus /\ COMMUTATIVE plus ==>
          !f:num->*. !g m n.
                plus (SIGMA (plus,m,n) f) (SIGMA (plus,m,n) g) =
                    SIGMA (plus,m,n) (\k.plus (f k) (g k))",
    GEN_TAC THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP REDUCE_MAP) THEN
    ASM_REWRITE_TAC [SIGMA]);;

let SIGMA_EXT_LEMMA =
    prove
    ("!(f:* -> ** -> ***) x y z. (x = y) ==> (f x z = f y z)",
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SIGMA_EXT =
    prove_thm
    (`SIGMA_EXT`,
     "!plus: *->*->*. MONOID plus ==>
          !f g m n. (!k. k < n ==> (f (m+k) = g (m+k))) ==>
              (SIGMA (plus,m,n) f = SIGMA (plus,m,n) g)",
    GEN_TAC THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP SIGMA_RIGHT_SPLIT) THEN
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
       [REWRITE_TAC [SIGMA_ID] ;
        PURE_ONCE_ASM_REWRITE_TAC[] THEN
        DISCH_THEN (\th.
            SUBST1_TAC
                (MP (SPEC "n:num" th) (SPEC "n:num" LESS_SUC_REFL)) THEN
            ASSUME_TAC th) THEN
        MATCH_MP_TAC SIGMA_EXT_LEMMA THEN        % simplify the goal %
        FIRST_ASSUM MATCH_MP_TAC THEN            % and again %
        GEN_TAC THEN
        DISCH_THEN (ASSUME_TAC o MATCH_MP LESS_SUC) THEN
        RES_TAC ]);;

% ========================================================================= %
% Part IV:  The Binomial Theorem                                            %
% ========================================================================= %

% ------------------------------------------------------------------------- %
% It is a handy abbreviation to define the structure of a term in the       %
% binomial expansion as a constant in HOL.                                  %
%                                                                           %
% When "RING (plus, times)" is assumed,                                     %
%        POWER plus n a     is the sum     of n a's, often written n dot a  %
%        POWER times n a    is the plusuct of n a's, often written a ^ n    %
% ------------------------------------------------------------------------- %

let BINTERM_DEF =
    new_definition (`BINTERM_DEF`,
      "BINTERM (plus: *->*->*) (times: *->*->*) a b n k =
          POWER plus (CHOOSE n k)
              (times (POWER times (n-k) a) (POWER times k b))");;

let BINTERM_0 =
    prove_thm
    (`BINTERM_0`,
    "!plus:*->*->*. !times:*->*->*. RING (plus, times) ==> (
        !a b n. BINTERM plus times a b n 0 = POWER times n a)",
    RING_TAC THEN
    ASM_REWRITE_TAC
       [BINTERM_DEF; CHOOSE_DEF; SUB_0; POWER;
        SPEC_IMP plus POWER_1; SPEC_EQ times RIGHT_ID]);;

let BINTERM_n =
    prove_thm
    (`BINTERM_n`,
    "!plus times. RING (plus: *->*->*, times) ==> (
        !a b n. BINTERM ^plus ^times (a:*) (b:*) (n:num) n = POWER times n b)",
    RING_TAC THEN
    ASM_REWRITE_TAC
       [BINTERM_DEF; CHOOSE_SAME; SUB_EQUAL_0; POWER;
        SPEC_IMP plus POWER_1; SPEC_EQ times LEFT_ID]);;

% ------------------------------------------------------------------------- %
% Some arithmetic results not in the theory `arithmetic`.                   %
% ------------------------------------------------------------------------- %

let SUC_SUB_SUC =
    prove_thm
    (`SUC_SUB_SUC`,
    "!m k. k < m ==> (SUC(m - SUC k) = m - k)",
    REPEAT STRIP_TAC THEN
    SUBST1_TAC
        (SYM (SPECL ["SUC(m - (SUC k))"; "m-k"; "k:num"] EQ_MONO_ADD_EQ)) THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    IMP_RES_THEN SUBST1_TAC SUB_ADD THEN
    REWRITE_TAC [ADD1] THEN
    REWRITE_TAC [DEEP_SYM ADD_ASSOC; SPEC "1" ADD_SYM; DEEP_SYM ADD1] THEN
    IMP_RES_TAC LESS_OR THEN
    IMP_RES_TAC SUB_ADD);;

% ------------------------------------------------------------------------- %
% General versions of the Binomial Theorem and its Lemmas                   %
% ------------------------------------------------------------------------- %

let LEMMA_1 =
    prove_thm
    (`LEMMA_1`,
    "!plus:*->*->*. !times:*->*->*. RING (plus, times) ==> (
        SIGMA (plus,1,n) (BINTERM plus times a b (SUC n))
        = plus
            (times a (SIGMA (plus,1,n) (BINTERM plus times a b n)))
            (times b (SIGMA (plus,0,n) (BINTERM plus times a b n))) )",
    RING_TAC THEN
    PURE_REWRITE_TAC
       [o_DEF; BINTERM_DEF;
        SPECL_IMP [plus;times] SIGMA_MULT_COMM;
        SPECL_IMP [plus;times] POWER_DISTRIB] THEN
    % Absorb a into "POWER times (n-x) a" %
    PURE_REWRITE_TAC
       [SPEC_EQ times ASSOCIATIVE; DEEP_SYM (CONJUNCT2 POWER)] THEN
    % Absorb b into "POWER times x b" %
    PURE_REWRITE_TAC
       [AC_CONV_RATOR times
            "(times:*->*->*) (times a b) c = times b (times a c)"; 
       DEEP_SYM (CONJUNCT2 POWER)] THEN
    % Apply SIGMA_SHIFT and SIGMA_PLUS_COMM %
    PURE_REWRITE_TAC
       [num_CONV "1"; SIGMA_SHIFT; STRIP_SPEC_IMP plus SIGMA_PLUS_COMM] THEN
    % Reduce the problem to that of proving the BINTERMs equivalent %
    MATCH_MP_TAC (SPEC_IMP plus SIGMA_EXT) THEN
    REPEAT STRIP_TAC THEN
    PURE_REWRITE_TAC [o_DEF; ADD_CLAUSES] THEN
    BETA_TAC THEN
    % Turn "SUC(n - (SUC k))" into "n - k", given the assumption "k < n" %
    SUBST1_TAC (SPECL_IMP ["n:num";"k:num"] SUC_SUB_SUC) THEN
    REWRITE_TAC
       [BINTERM_DEF; CHOOSE_DEF; SUB_MONO_EQ; SPEC_IMP plus POWER_ADD] );;

let LEMMA_2 =
    prove_thm
    (`LEMMA_2`,
    "!plus times. RING (plus: *->*->*, times) ==> (
        times a (SIGMA (plus,0,SUC n) (BINTERM plus times a b n))
        = plus
            (POWER times (SUC n) a)
            (times a (SIGMA (plus,1,n) (BINTERM plus times a b n))) )",
    RING_TAC THEN
    REWRITE_TAC
       [SIGMA_LEFT_SPLIT; SPECL_EQ [plus;times] LEFT_DISTRIB;
        POWER; num_CONV "1"; SPECL_IMP [plus;times] BINTERM_0]);;

let LEMMA_3 =
    prove_thm
    (`LEMMA_3`,
    "!plus times. RING (plus: *->*->*, times) ==> (
        times b (SIGMA (plus,0,SUC n) (BINTERM plus times a b n))
        = plus
            (times b (SIGMA (plus,0,n) (BINTERM plus times a b n)))
            (POWER times (SUC n) b) )",
    RING_TAC THEN
    REWRITE_TAC
       [SPEC_IMP plus SIGMA_RIGHT_SPLIT;
        SPECL_EQ [plus;times] LEFT_DISTRIB;
        ADD; POWER; SPECL_IMP [plus;times] BINTERM_n]);;

% We never need to expand out BINTERM during the top level proof of BINOMIAL %
let BINOMIAL =
    prove_thm
    (`BINOMIAL`,
     "!plus times. RING (plus: *->*->*, times) ==>
        !a b n.
            POWER times n (plus a b) =
                SIGMA (plus,0,SUC n) (BINTERM plus times a b n)",
    RING_TAC THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
       [REWRITE_TAC
           [SIGMA; RANGE; MAP; SPECL_IMP [plus;times] BINTERM_0;
            REDUCE; POWER; SPEC_EQ plus RIGHT_ID] ;

        % (a) Expand the rhs with SIGMA_LEFT_SPLIT, SIGMA_RIGHT_SPLIT, LEMMA_1 %
        PURE_ONCE_REWRITE_TAC [SIGMA_LEFT_SPLIT] THEN
        PURE_ONCE_REWRITE_TAC [SPEC_IMP plus SIGMA_RIGHT_SPLIT] THEN
        PURE_REWRITE_TAC
            [ADD; ADD_0;
            SPECL_IMP [plus;times] BINTERM_0;
            SPECL_IMP [plus;times] BINTERM_n] THEN
        SUBST1_TAC (SYM(num_CONV "1")) THEN
        PURE_ONCE_REWRITE_TAC [SPECL_IMP [plus;times] LEMMA_1] THEN

        % (b) Expand the lhs and apply the induction hypothesis %
        SUBST1_TAC
            (SPECL [times; "n:num"; "^plus a b"] (CONJUNCT2 POWER)) THEN
        POP_ASSUM SUBST1_TAC THEN

        % (c) Make the two sides equal %
        REWRITE_TAC
           [SPECL_EQ [plus;times] RIGHT_DISTRIB;
            SPECL_IMP [plus;times] LEMMA_2;
            SPECL_IMP [plus;times] LEMMA_3;
            SPEC_EQ plus ASSOCIATIVE] ]);;

close_theory();;
