% FILE		: elt_gp.show.ml					%
% DESCRIPTION   : gives a history of the development of elt_gp.th, by	%
%                 displaying all the set_goal commands and expand 	%
%                 commands that where given to produce the theorems in	%
%                 the theory.  It can be loaded by loadt and it will	%
%                 also create elt_gp.th, but in a most verbose manner.	%
%                 The resulting theory file is called elt_gp.th		%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.21						%
%									%
%-----------------------------------------------------------------------%

loadt (`start_groups`);;

new_theory (`elt_gp`);;

%extend_theory `elt_gp`;;
include_theory `elt_gp`;;%

% A group is a set G together with a binary operation prod such that:
  0. G is closed under prod
  1. prod is associative
  2. there exists a left identity e for prod
  3. every element of G has a left inverse in G with respect to e.
%

let GROUP_DEF =
new_definition(`GROUP_DEF`, "GROUP ((G:* -> bool),prod) =
 (!x.!y.((G x) /\ (G y)) ==> (G (prod x y))) /\
 (!x.!y.!z.((G x) /\ (G y) /\ (G z)) ==>
    ((prod (prod x y) z) = (prod x (prod y z)))) /\
 (?e.(G e) /\ (!x.(G x) ==> (prod e x = x)) /\
  (!x.(G x) ==> ?y.(G y) /\ (prod y x = e)))");;


let CLOSURE = save_thm (`CLOSURE`,
  (DISCH_ALL (CONJUNCT1 (UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL GROUP_DEF)))))));;


let ID_DEF = new_definition (`ID_DEF`, "ID(G,prod) =
   (@e:*.((G e) /\ (!x.(G x) ==> (prod e x = x)) /\
        (!x.(G x) ==> ?y.(G y) /\ (prod y x = e))))");;


let GROUP_ASSOC = save_thm (`GROUP_ASSOC`,
(DISCH_ALL(CONJUNCT1 (CONJUNCT2 (UNDISCH
   (fst (EQ_IMP_RULE (SPEC_ALL GROUP_DEF))))))));;


set_goal ([], "GROUP(G,prod) ==> ((G (ID(G,prod))) /\
  (!x:*. (G x) ==> (prod (ID(G,prod)) x = x)) /\
  (!x. (G x) ==> (prod x (ID(G,prod)) = x)) /\
  (!x. (G x) ==> ?y. (G y) /\ (prod y x = ID(G,prod))))");;

expand DISCH_TAC;;

expand (ASSUME_TAC 
 (PURE_ONCE_REWRITE_RULE [GROUP_DEF] (ASSUME "GROUP((G:* -> bool),prod)")));;

expand (POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE o CONJUNCT2 o CONJUNCT2));;

expand (ASM_CONJ1_TAC THENL [ALL_TAC;ASM_CONJ1_TAC] THENL
  [ALL_TAC;ALL_TAC;ASM_CONJ2_TAC] THENL
  [(ASM_REWRITE_TAC[ID_DEF]);(ASM_REWRITE_TAC[ID_DEF]); ALL_TAC;
   (ASM_REWRITE_TAC[ID_DEF])]);;

expand (STRIP_ASSUME_TAC 
 (PURE_ONCE_REWRITE_RULE [GROUP_DEF] (ASSUME "GROUP((G:* -> bool),prod)")));;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*"
  (ASSUME "!x:*. G x ==> (?y. G y /\ (prod y x = ID(G,prod)))"))));;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "y:*"
  (ASSUME "!x:*. G x ==> (?y. G y /\ (prod y x = ID(G,prod)))"))));;

expand (SUPPOSE_TAC "prod y' (ID(G,prod)) = (x:*)");;

%first goal %

expand (NEW_SUBST1_TAC (SYM (BETA_RULE
  (AP_TERM "\(X:*).(prod X (ID(G,prod)))"
  (ASSUME "prod y' (ID(G,prod)) = (x:*)")))));;

expand (NEW_SUBST1_TAC(UNDISCH_ALL (hd (IMP_CANON
  (SPECL ["y':*";"ID((G:* -> bool),prod)";"ID((G:* -> bool),prod)"]
  (UNDISCH GROUP_ASSOC))))));;

expand (NEW_SUBST1_TAC (UNDISCH (SPEC "ID((G:* -> bool),prod)"
    (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)"))));;

expand (FIRST_ASSUM ACCEPT_TAC);;

%second goal%

expand (NEW_SUBST1_TAC (SYM (AP_TERM "(prod:* -> * -> *) y'"
  (ASSUME "(prod y x = ID(G,prod):*)"))));;

expand (NEW_SUBST1_TAC (SYM(UNDISCH_ALL (hd (IMP_CANON
  (SPECL ["y':*";"y:*";"x:*"] (UNDISCH GROUP_ASSOC)))))));;

expand (ASM_REWRITE_TAC[]);;

expand (ACCEPT_TAC (UNDISCH (SPEC "x:*"
  (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)"))));;


let ID_LEMMA = prove_thm (`ID_LEMMA`,"GROUP(G,prod) ==> 
  ((G (ID(G,prod))) /\
  (!x:*. (G x) ==> (prod (ID(G,prod)) x = x)) /\
  (!x. (G x) ==> (prod x (ID(G,prod)) = x)) /\
  (!x. (G x) ==> ?y. (G y) /\ (prod y x = ID(G,prod))))",
(DISCH_TAC THEN
 (ASSUME_TAC 
   (PURE_ONCE_REWRITE_RULE [GROUP_DEF]
     (ASSUME "GROUP((G:* -> bool),prod)"))) THEN
 (POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE o CONJUNCT2 o CONJUNCT2)) THEN
 (ASM_CONJ1_TAC THENL [ALL_TAC;ASM_CONJ1_TAC] THENL
   [ALL_TAC;ALL_TAC;ASM_CONJ2_TAC] THENL
   [(ASM_REWRITE_TAC[ID_DEF]);(ASM_REWRITE_TAC[ID_DEF]);ALL_TAC;
    (ASM_REWRITE_TAC[ID_DEF])]) THEN
 (STRIP_ASSUME_TAC 
   (PURE_ONCE_REWRITE_RULE [GROUP_DEF]
     (ASSUME "GROUP((G:* -> bool),prod)"))) THEN
 (REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*"
   (ASSUME "!x:*. G x ==> (?y. G y /\ (prod y x = ID(G,prod)))")))) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "y:*"
   (ASSUME "!x:*. G x ==> (?y. G y /\ (prod y x = ID(G,prod)))")))) THEN
 (SUPPOSE_TAC "prod y' (ID(G,prod)) = (x:*)") THENL
  [((NEW_SUBST1_TAC (SYM (BETA_RULE (AP_TERM "\(X:*).(prod X (ID(G,prod)))"
      (ASSUME "prod y' (ID(G,prod)) = (x:*)"))))) THEN
    (NEW_SUBST1_TAC(UNDISCH_ALL (hd (IMP_CANON
      (SPECL ["y':*";"ID((G:* -> bool),prod)";"ID((G:* -> bool),prod)"]
        (UNDISCH GROUP_ASSOC)))))) THEN
    (NEW_SUBST1_TAC (UNDISCH (SPEC "ID((G:* -> bool),prod)"
      (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))) THEN
    (FIRST_ASSUM ACCEPT_TAC));
   ((NEW_SUBST1_TAC (SYM (AP_TERM "(prod:* -> * -> *) y'"
      (ASSUME "(prod y x = ID(G,prod):*)")))) THEN
    (NEW_SUBST1_TAC (SYM(UNDISCH_ALL (hd (IMP_CANON
      (SPECL ["y':*";"y:*";"x:*"] (UNDISCH GROUP_ASSOC))))))) THEN
    (ASM_REWRITE_TAC[]) THEN
    (ACCEPT_TAC (UNDISCH (SPEC "x:*"
      (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))))]));;


let INV_DEF = new_definition (`INV_DEF`, "INV(G,prod)(x:*) = (@y.(G y)
  /\ (prod y x = ID(G,prod)))");;


set_goal ([], "GROUP((G:* -> bool),prod) ==>
   (!x. (G x) ==> (G (INV (G,prod) x)))");;

expand ((REPEAT STRIP_TAC) THEN
 (ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [(SYM (SPEC_ALL INV_DEF))]
   (SELECT_RULE (UNDISCH (SPEC "x:*" (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
    (UNDISCH ID_LEMMA)))))))))));;

let INV_CLOSURE = prove_thm (`INV_CLOSURE`,"GROUP((G:* -> bool),prod) ==>
   (!x. (G x) ==> (G (INV (G,prod) x)))",
 ((REPEAT STRIP_TAC) THEN
 (ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [(SYM (SPEC_ALL INV_DEF))]
   (SELECT_RULE (UNDISCH (SPEC "x:*" (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
    (UNDISCH ID_LEMMA))))))))))));;


loadt `group_tac`;;


set_goal ([], "GROUP((G:* -> bool),prod) ==>
   (!x y.((G x) /\ (G y)) ==> ((prod y x = ID(G,prod)) ==>
        (prod x y = ID(G,prod))))");;

expand DISCH_TAC;;

expand (STRIP_ASSUME_TAC
  (PURE_ONCE_REWRITE_RULE [GROUP_DEF] (ASSUME "GROUP((G:* -> bool),prod)")));;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC
  (UNDISCH (SPEC "y:*"
    (ASSUME "!(x:*). G x ==> (?y. G y /\ (prod y x = ID(G,prod)))"))));;

expand ((NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "(prod: * -> * -> *) x y"
           (ASSUME "!(x:*). G x ==> (prod(ID(G,prod))x = x)"))))) THENL
 [ALL_TAC;GROUP_ELT_TAC]);;

expand (NEW_SUBST1_TAC (SYM (AP_THM (AP_TERM "prod:* -> * -> *"
 (ASSUME "(prod:* -> * -> *) y' y = ID(G,prod)")) "(prod:* -> * -> *) x y")));;

expand (NEW_SUBST1_TAC (UNDISCH_ALL (hd (IMP_CANON 
  (SPECL ["y':*"; "y:*"; "(prod:* -> * -> *) x y"] (ASSUME "!x y z:*.
    G x /\ G y /\ G z ==> (prod(prod x y)z = prod x(prod y z))"))))));;

expand (NEW_SUBST1_TAC (SYM (UNDISCH_ALL (hd (IMP_CANON 
  (SPECL ["y:*"; "x:*"; "y:*"] (ASSUME "!x y z:*. G x /\ G y /\ G z ==>
    (prod(prod x y)z = prod x(prod y z))")))))));;

expand (ASM_REWRITE_TAC[(UNDISCH (SPEC "y:*"
       (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))]);;


let LEFT_RIGHT_INV = prove_thm (`LEFT_RIGHT_INV`,"GROUP((G:* -> bool),prod) ==>
   (!x y.((G x) /\ (G y)) ==> ((prod y x = ID(G,prod)) ==>
        (prod x y = ID(G,prod))))",
(DISCH_TAC THEN
 (STRIP_ASSUME_TAC
  (PURE_ONCE_REWRITE_RULE [GROUP_DEF]
    (ASSUME "GROUP((G:* -> bool),prod)"))) THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 (REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC
  (UNDISCH (SPEC "y:*" (ASSUME "!(x:*). G x ==>
    (?y. G y /\ (prod y x = ID(G,prod)))")))) THEN
 ((NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "(prod: * -> * -> *) x y"
   (ASSUME "!(x:*). G x ==> (prod(ID(G,prod))x = x)"))))) THENL
  [ALL_TAC;GROUP_ELT_TAC]) THEN
 (NEW_SUBST1_TAC (SYM (AP_THM
   (AP_TERM "prod:* -> * -> *"
      (ASSUME "(prod:* -> * -> *) y' y = ID(G,prod)"))
   "(prod:* -> * -> *) x y"))) THEN
 (NEW_SUBST1_TAC (UNDISCH_ALL (hd (IMP_CANON 
  (SPECL ["y':*"; "y:*"; "(prod:* -> * -> *) x y"] (ASSUME "!x y z:*.
    G x /\ G y /\ G z ==> (prod(prod x y)z = prod x(prod y z))")))))) THEN
 (NEW_SUBST1_TAC (SYM (UNDISCH_ALL (hd (IMP_CANON 
  (SPECL ["y:*"; "x:*"; "y:*"] (ASSUME "!x y z:*. G x /\ G y /\ G z ==>
    (prod(prod x y)z = prod x(prod y z))"))))))) THEN
 (ASM_REWRITE_TAC[(UNDISCH (SPEC "y:*"
       (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))])));;


set_goal ([],"GROUP(G,prod) ==> (!x:*.((G x) ==>
  ((prod (INV(G,prod)x) x = ID(G,prod)) /\
   (prod x (INV(G,prod)x) = ID(G,prod)))))");;

expand (DISCH_TAC THEN GEN_TAC THEN DISCH_TAC);;

expand (STRIP_ASSUME_TAC (SUBS [(SYM (SPEC_ALL INV_DEF))](SELECT_RULE (UNDISCH
  (SPEC "x:*" (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (UNDISCH (ID_LEMMA))))))))));;

expand (ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON
  (SPECL ["x:*";"INV(G,prod)x:*"] (UNDISCH LEFT_RIGHT_INV))))));;

expand ((REPEAT STRIP_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));;


let INV_LEMMA = prove_thm (`INV_LEMMA`,"GROUP(G,prod) ==> (!x:*.((G x) ==>
  ((prod (INV(G,prod)x) x = ID(G,prod)) /\
   (prod x (INV(G,prod)x) = ID(G,prod)))))",
(DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
 (STRIP_ASSUME_TAC (SUBS [(SYM (SPEC_ALL INV_DEF))](SELECT_RULE (UNDISCH
  (SPEC "x:*" (CONJUNCT2(CONJUNCT2(CONJUNCT2 (UNDISCH (ID_LEMMA)))))))))) THEN
 (ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL ["x:*";"INV(G,prod)x:*"]
  (UNDISCH LEFT_RIGHT_INV)))))) THEN
 (REPEAT STRIP_TAC) THEN (FIRST_ASSUM ACCEPT_TAC)));;


set_goal([],"GROUP(G,prod) ==> (!x:*.!y.!z.(G x) /\ (G y) /\ (G z) ==>
 ((prod x y) = (prod x z)) ==> (y = z))");;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "y:*"
        (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))));;

expand (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "z:*"
        (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))));;

expand (NEW_SUBST1_TAC (SYM
        (ASSUME "prod (INV(G,prod)x:*) x = ID(G,prod)")));;

expand (GROUP_RIGHT_ASSOC_TAC "prod(prod(INV(G,prod)(x:*))x)y");;

expand (GROUP_RIGHT_ASSOC_TAC "prod(prod(INV(G,prod)(x:*))x)z");;

expand ((NEW_SUBST1_TAC (ASSUME "(prod:* -> * -> *) x y = prod x z")) 
  THEN REFL_TAC);;


let LEFT_CANCELLATION = prove_thm(`LEFT_CANCELLATION`,
"GROUP(G,prod) ==> (!x:*.!y.!z.(G x) /\ (G y) /\ (G z) ==>
 ((prod x y) = (prod x z)) ==> (y = z))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "y:*"
        (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)"))))) THEN
 (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "z:*"
        (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)"))))) THEN
 (NEW_SUBST1_TAC (SYM (ASSUME "prod (INV(G,prod)x:*) x = ID(G,prod)"))) THEN
 (GROUP_RIGHT_ASSOC_TAC "prod(prod(INV(G,prod)(x:*))x)y") THEN
 (GROUP_RIGHT_ASSOC_TAC "prod(prod(INV(G,prod)(x:*))x)z") THEN
 (NEW_SUBST1_TAC (ASSUME "(prod:* -> * -> *) x y = prod x z")) THEN
 REFL_TAC));;


set_goal([],"GROUP(G,prod) ==> (!x:*.!y.!z.(G x) /\ (G y) /\ (G z) ==>
 (((prod y x) = (prod z x)) ==> (y = z)))");;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "y:*"
        (ASSUME "!x:*. G x ==> (prod x (ID(G,prod)) = x)")))));;

expand (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "z:*"
        (ASSUME "!x:*. G x ==> (prod x (ID(G,prod)) = x)")))));;

expand (NEW_SUBST1_TAC (SYM
       (ASSUME "prod x (INV(G,prod)x:*) = ID(G,prod)")));;

expand (GROUP_LEFT_ASSOC_TAC "prod (y:*)(prod x(INV(G,prod)x))");;

expand (GROUP_LEFT_ASSOC_TAC "prod (z:*)(prod x(INV(G,prod)x))");;

expand ((NEW_SUBST1_TAC (ASSUME "(prod:* -> * -> *) y x = prod z x"))
 THEN REFL_TAC);;


let RIGHT_CANCELLATION = prove_thm (`RIGHT_CANCELLATION`,
"GROUP(G,prod) ==> (!x:*.!y.!z.(G x) /\ (G y) /\ (G z) ==>
  (((prod y x) = (prod z x)) ==> (y = z)))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "y:*"
   (ASSUME "!x:*. G x ==> (prod x (ID(G,prod)) = x)"))))) THEN
 (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "z:*"
   (ASSUME "!x:*. G x ==> (prod x (ID(G,prod)) = x)"))))) THEN
 (NEW_SUBST1_TAC (SYM (ASSUME "prod x (INV(G,prod)x:*) = ID(G,prod)"))) THEN
 (GROUP_LEFT_ASSOC_TAC "prod (y:*)(prod x(INV(G,prod)x))") THEN
 (GROUP_LEFT_ASSOC_TAC "prod (z:*)(prod x(INV(G,prod)x))") THEN
 (NEW_SUBST1_TAC (ASSUME "(prod:* -> * -> *) y x = prod z x")) THEN
 REFL_TAC));;

set_goal ([], "GROUP((G:* -> bool),prod) ==> 
(!x y. ((G x) /\ (G y)) ==>
 (?z. (G z) /\ ((prod x z) = y) /\
  (!u. ((G u) /\ ((prod x u) = y)) ==> (u = z))))");;

expand DISCH_TAC;;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand ((REPEAT GEN_TAC) THEN STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand (EXISTS_TAC "((prod:* -> * -> *) (INV(G,prod)x:*) y)");;

expand (ASM_CONJ1_TAC THENL [GROUP_ELT_TAC;ALL_TAC]);;

expand ASM_CONJ1_TAC;;

%existence goal%

expand (GROUP_LEFT_ASSOC_TAC "prod x(prod(INV(G,prod)x)(y:*))");;

expand (NEW_SUBST1_TAC
  (ASSUME "prod (x:*) (INV(G,prod)x) = ID(G,prod)"));;

expand (ACCEPT_TAC (UNDISCH (SPEC "y:*"
  (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)"))));;

%uniqueness goal%

expand (REPEAT STRIP_TAC);;

expand (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
  (SPECL ["x:*";"u:*";"(prod:* -> * -> *) (INV(G,prod)x) y"]
    (UNDISCH LEFT_CANCELLATION))))))));;

expand (ASM_REWRITE_TAC[]);;


let RIGHT_ONE_ONE_ONTO = prove_thm(`RIGHT_ONE_ONE_ONTO`,
 "GROUP((G:* -> bool),prod) ==> (!x y. ((G x) /\ (G y)) ==>
   (?z. (G z) /\ ((prod x z) = y) /\
   (!u. ((G u) /\ ((prod x u) = y)) ==> (u = z))))",
(DISCH_TAC THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 ((REPEAT GEN_TAC) THEN STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 (EXISTS_TAC "((prod:* -> * -> *) (INV(G,prod)x:*) y)") THEN
 (ASM_CONJ1_TAC THENL [GROUP_ELT_TAC;ALL_TAC]) THEN
 ASM_CONJ1_TAC THENL
 [((GROUP_LEFT_ASSOC_TAC "prod x(prod(INV(G,prod)x)(y:*))") THEN
   (NEW_SUBST1_TAC (ASSUME "prod (x:*) (INV(G,prod)x) = ID(G,prod)")) THEN
   (ACCEPT_TAC (UNDISCH (SPEC "y:*"
     (ASSUME "!x:*. G x ==> (prod(ID(G,prod))x = x)")))));
  ((REPEAT STRIP_TAC) THEN
   (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
    (SPECL ["x:*";"u:*";"(prod:* -> * -> *) (INV(G,prod)x) y"]
      (UNDISCH LEFT_CANCELLATION)))))))) THEN
   (ASM_REWRITE_TAC[]))]));;


set_goal ([], "GROUP((G:* -> bool),prod) ==> 
(!x y. ((G x) /\ (G y)) ==>
 (?z. (G z) /\ ((prod z x) = y) /\
  (!u. ((G u) /\ ((prod u x) = y)) ==> (u = z))))");;


expand DISCH_TAC;;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand ((REPEAT GEN_TAC) THEN STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand (EXISTS_TAC "((prod:* -> * -> *) y (INV(G,prod)x))");;

expand (ASM_CONJ1_TAC THENL [GROUP_ELT_TAC;ALL_TAC]);;

expand ASM_CONJ1_TAC;;

%existence goal%

expand (GROUP_RIGHT_ASSOC_TAC "prod(prod (y:*)(INV(G,prod)x))x");;

expand (NEW_SUBST1_TAC
  (ASSUME "prod (INV(G,prod)x) (x:*) = ID(G,prod)"));;

expand (ACCEPT_TAC (UNDISCH (SPEC "y:*"
  (ASSUME "!x:*. G x ==> (prod x(ID(G,prod)) = x)"))));;

%uniqueness goal%

expand (REPEAT STRIP_TAC);;

expand (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
(SPECL ["x:*";"u:*";"(prod:* -> * -> *)y (INV(G,prod)x)"]
 (UNDISCH RIGHT_CANCELLATION))))))));;

expand (ASM_REWRITE_TAC[]);;


let LEFT_ONE_ONE_ONTO = prove_thm(`LEFT_ONE_ONE_ONTO`,
 "GROUP((G:* -> bool),prod) ==> (!x y. ((G x) /\ (G y)) ==>
   (?z. (G z) /\ ((prod z x) = y) /\
   (!u. ((G u) /\ ((prod u x) = y)) ==> (u = z))))",
(DISCH_TAC THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 ((REPEAT GEN_TAC) THEN STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 (EXISTS_TAC "((prod:* -> * -> *) y (INV(G,prod)x))") THEN
 (ASM_CONJ1_TAC THENL [GROUP_ELT_TAC;ALL_TAC]) THEN
 ASM_CONJ1_TAC THENL
 [((GROUP_RIGHT_ASSOC_TAC "prod(prod (y:*)(INV(G,prod)x))x") THEN
   (NEW_SUBST1_TAC (ASSUME "prod (INV(G,prod)x) (x:*) = ID(G,prod)")) THEN
   (ACCEPT_TAC (UNDISCH (SPEC "y:*"
     (ASSUME "!x:*. G x ==> (prod x(ID(G,prod)) = x)")))));
  ((REPEAT STRIP_TAC) THEN
   (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
    (SPECL ["x:*";"u:*";"(prod:* -> * -> *)y (INV(G,prod)x)"]
     (UNDISCH RIGHT_CANCELLATION)))))))) THEN
   (ASM_REWRITE_TAC[]))]));;


set_goal ([],"GROUP(G,prod) ==>
   (!e:*.((G e) /\ 
         ((?x.((G x) /\ (prod e x = x))) \/ (?x.(G x) /\ (prod x e = x)))) ==>
      (e = ID(G,prod)))");;

expand DISCH_TAC;;

expand (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA));;

expand (REPEAT STRIP_TAC);;

%first goal%

expand RES_TAC;;

expand (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
  (SPECL ["x:*";"e:*";"ID(G,prod):*"] (UNDISCH RIGHT_CANCELLATION))))))));;

expand (ASM_REWRITE_TAC[]);;

%second goal%

expand  RES_TAC;;

expand (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
  (SPECL ["x:*";"e:*";"ID(G,prod):*"] (UNDISCH LEFT_CANCELLATION))))))));;

expand (ASM_REWRITE_TAC[]);;


let UNIQUE_ID = prove_thm (`UNIQUE_ID`,"GROUP(G,prod) ==> (!e:*.((G e) /\ 
 ((?x.((G x) /\ (prod e x = x))) \/ (?x.(G x) /\ (prod x e = x)))) ==>
      (e = ID(G,prod)))",
(DISCH_TAC THEN
 (STRIP_ASSUME_TAC (UNDISCH ID_LEMMA)) THEN
 (REPEAT STRIP_TAC) THENL
  [(RES_TAC THEN
    (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
      (SPECL ["x:*";"e:*";"ID(G,prod):*"]
        (UNDISCH RIGHT_CANCELLATION)))))))) THEN
    (ASM_REWRITE_TAC[]));
   (RES_TAC THEN
    (MP_IMP_TAC (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
      (SPECL ["x:*";"e:*";"ID(G,prod):*"]
        (UNDISCH LEFT_CANCELLATION)))))))) THEN
   (ASM_REWRITE_TAC[]))]));;


set_goal ([],"GROUP(G,prod) ==> !x:*. (G x) ==>
  (!u.((G u) /\ (prod u x = ID(G,prod))) ==> (u = (INV(G,prod)x)))");;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand ((use_thm (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
  (SPECL ["x:*";"u:*";"INV(G,prod)(x:*)"] (UNDISCH RIGHT_CANCELLATION)))))))
  MP_IMP_TAC ) THENL [ALL_TAC;GROUP_ELT_TAC]);;

expand (ASM_REWRITE_TAC []);;


let UNIQUE_INV = prove_thm (`UNIQUE_INV`,"GROUP(G,prod) ==> !x:*. (G x) ==>
  (!u.((G u) /\ (prod u x = ID(G,prod))) ==> (u = (INV(G,prod)x)))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 ((use_thm (UNDISCH (UNDISCH (UNDISCH (hd (IMP_CANON
  (SPECL ["x:*";"u:*";"INV(G,prod)(x:*)"]
    (UNDISCH RIGHT_CANCELLATION))))))) MP_IMP_TAC) THENL
  [ALL_TAC;GROUP_ELT_TAC]) THEN
 (ASM_REWRITE_TAC [])));;


%INV_ID_LEMMA added 23 July 1989 by E.L.Gunter %

set_goal ([],"GROUP(G,prod) ==>
  ((INV(G,prod)(ID(G,prod)):*) = (ID(G,prod)))");;

expand DISCH_TAC;;

expand (NEW_MATCH_ACCEPT_TAC (SYM (UNDISCH (SPEC "(ID((G,prod)):*)"
    (UNDISCH (SPEC_ALL (UNDISCH UNIQUE_INV)))))));;

expand (ASM_CONJ1_TAC THENL
    [GROUP_ELT_TAC;
     (ACCEPT_TAC (UNDISCH (SPEC "(ID((G,prod)):*)" (CONJUNCT1 (CONJUNCT2
      (UNDISCH ID_LEMMA))))))]);;


let INV_ID_LEMMA = prove_thm(`INV_ID_LEMMA`,"GROUP(G,prod) ==>
  ((INV(G,prod)(ID(G,prod)):*) = (ID(G,prod)))",
(DISCH_TAC THEN
 (NEW_MATCH_ACCEPT_TAC (SYM (UNDISCH (SPEC "(ID((G,prod)):*)"
    (UNDISCH (SPEC_ALL (UNDISCH UNIQUE_INV))))))) THEN
 (ASM_CONJ1_TAC THENL
 [GROUP_ELT_TAC;
  (ACCEPT_TAC (UNDISCH (SPEC "(ID((G,prod)):*)" (CONJUNCT1 (CONJUNCT2
   (UNDISCH ID_LEMMA))))))])));;


set_goal ([],"GROUP(G,prod) ==>
  (!x:*.(G x) ==> ((INV(G,prod)(INV(G,prod)x)) = x))");;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA))));;

expand (PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]);;

expand ((use_thm (UNDISCH (hd (IMP_CANON (SPEC "x:*" (UNDISCH
    (SPEC "INV(G,prod)x:*" (UNDISCH UNIQUE_INV))))))) MP_IMP_TAC) THENL
    [ALL_TAC;GROUP_ELT_TAC]);;

expand (FIRST_ASSUM ACCEPT_TAC);;


let INV_INV_LEMMA = prove_thm(`INV_INV_LEMMA`,"GROUP(G,prod) ==>
  (!x:*.(G x) ==> ((INV(G,prod)(INV(G,prod)x)) = x))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (UNDISCH (SPEC "x:*" (UNDISCH INV_LEMMA)))) THEN
 (PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]) THEN
 ((use_thm (UNDISCH (hd (IMP_CANON (SPEC "x:*" (UNDISCH
    (SPEC "INV(G,prod)x:*" (UNDISCH UNIQUE_INV))))))) MP_IMP_TAC) THENL
    [ALL_TAC;GROUP_ELT_TAC]) THEN
 (FIRST_ASSUM ACCEPT_TAC)));;


set_goal ([],"GROUP(G,prod) ==> !x y:*.((G x) /\ (G y)) ==>
 (prod (INV(G,prod)x) (INV(G,prod)y) = INV (G,prod) (prod y x))");;

expand (REPEAT STRIP_TAC);;

expand (IMP_RES_TAC (CONJUNCT2 (UNDISCH ID_LEMMA)));;

expand (IMP_RES_TAC INV_LEMMA);;

expand ((use_thm (UNDISCH (hd (IMP_CANON 
   (SPEC "prod(INV(G,prod)x)(INV(G,prod)y):*" (UNDISCH
   (SPEC "(prod:* -> * -> *) y  x" (UNDISCH UNIQUE_INV)))))))MP_IMP_TAC) THENL
   [ALL_TAC;GROUP_ELT_TAC;GROUP_ELT_TAC]);;

expand (GROUP_RIGHT_ASSOC_TAC
   "prod(prod(INV(G,prod)x)(INV(G,prod)y))(prod y(x:*))");;

expand (GROUP_LEFT_ASSOC_TAC "prod(INV(G,prod)(y:*))(prod y x)");;

%expand ((NEW_SUBST1_TAC (UNDISCH_ALL (hd (IMP_CANON
  (SPECL ["INV(G,prod)x:*";"INV(G,prod)y:*";"(prod:* -> * -> *)y x"]
   (UNDISCH GROUP_ASSOC)))))) THENL
  [ALL_TAC;GROUP_ELT_TAC;GROUP_ELT_TAC]);;

expand (NEW_SUBST1_TAC (SYM (UNDISCH_ALL (hd (IMP_CANON
  (SPECL ["INV(G,prod)y:*";"y:*"; "x:*"] (UNDISCH GROUP_ASSOC)))))));;%

expand (ASM_REWRITE_TAC[]);;


let DIST_INV_LEMMA = prove_thm(`DIST_INV_LEMMA`,
"GROUP(G,prod) ==> !x y:*.((G x) /\ (G y)) ==>
 (prod (INV(G,prod)x) (INV(G,prod)y) = INV (G,prod) (prod y x))",
((REPEAT STRIP_TAC) THEN
 (IMP_RES_TAC (CONJUNCT2 (UNDISCH ID_LEMMA)))THEN
 (IMP_RES_TAC  INV_LEMMA) THEN
 ((use_thm (UNDISCH (hd (IMP_CANON 
   (SPEC "prod(INV(G,prod)x)(INV(G,prod)y):*" (UNDISCH
   (SPEC "(prod:* -> * -> *) y  x" (UNDISCH UNIQUE_INV)))))))MP_IMP_TAC) THENL
   [ALL_TAC;GROUP_ELT_TAC;GROUP_ELT_TAC]) THEN
 (GROUP_RIGHT_ASSOC_TAC
   "prod(prod(INV(G,prod)x)(INV(G,prod)y))(prod y(x:*))") THEN
 (GROUP_LEFT_ASSOC_TAC "prod(INV(G,prod)(y:*))(prod y x)") THEN
  (ASM_REWRITE_TAC[])));;

close_theory `elt_gp`;;


