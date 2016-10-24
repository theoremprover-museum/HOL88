%	-*- Emacs Mode: fundamental -*-                                       %

%------------------------------------------------------------------------------

   File:         mk_tarski.ml

   Authors:      (c) Flemming Andersen & Kim Dam Petersen
   Date:         April 9, 1990
   Last Updated: 28/10-1992.

   Description:  Defines a fixed point theory for defining recursive boolean
                 functions using monotonic predicate transformers. 

                 This theory is based on the article:

		   Alfred Tarski,
		   A Lattice-Theoretical Fixpoint Theorem and its Applications,
		   Pacific Journal of Mathematics, 1955.

  Dependencies: None

  Make:		The theory is created by executing:
			# loadt`mk_tarski`;;

  Usage:	The theory is loaded by executing:
			# load_theory`tarski`;;

------------------------------------------------------------------------------%

system`/bin/rm tarski.th`;;

new_theory`tarski`;;

%
  From Tarski we know that in complete lattices, any monotonic recursive 
  function f:

	Y = f Y

  has a strongest and a weakest solution.  Furthermore it has the same 
  strongest solution as:

	f Y ==> Y

  and the same weakest solution as:

	Y ==> f Y

  It is well known that predicates ordered by pointwise implication constitutes
  a complete lattice.  This knowledge will be used to define a fixed point
  theory for boolean function.

%


%
 =============================================================================

   Definitions for setting up the theory:

 =============================================================================
%

%
  We define the membership predicate In as the characteristic function of a 
  set returning true for every predicate member of the set:
%
let In = new_infix_definition
  (`In`,
   "In (x:*->bool) (X:(*->bool)->bool) = X x");;

%
  The ordering of boolean functions corresponding to set inclusion is defined
  by pointwize implication
%
let Leq = new_infix_definition
  (`Leq`,
   "Leq (x:*->bool) (y:*->bool) = (!s. x s ==> y s)");;

%
  The conjunction of boolean functions corresponding to set intersection is 
  defined by pointwize conjunction:
%
let And = new_infix_definition
  (`And`, "And (p:*->bool) (q:*->bool) = \s. (p s) /\ (q s)");;

%
  The disjunction of boolean functions corresponding to set union is 
  defined by pointwize disjunction:
%
let Or = new_infix_definition
  (`Or`, "Or (p:*->bool) (q:*->bool) = \s. (p s) \/ (q s)");;


%
  Monotonicity is defined as preserved ordering of predicate transformers
  of the ordering relation:
%
let IsMono = new_definition
  (`IsMono`,
   "IsMono (Fn:(*->bool)->(*->bool)) = !x y. x Leq y ==> (Fn x) Leq (Fn y)");;

%
  A fixed point of a functional Fn is any parameter p returning the parameter
  x by application
%
let IsFix = new_definition
  (`IsFix`,
   "IsFix Fn (x:*) = (Fn x = x)");;

%
  The Greatest Lower Bound (GLB) of a set X is the intersection of all members
  of the set
%
let GLB = new_definition
  (`GLB`,
   "GLB (X:(*->bool)->bool) = \s:*. !x. (x In X) ==> x s");;

%
  The minimal fixed point of a monotonic functional Fn is the GLB of the set
  of functions all satisfying that the application of the functional to a
  parameter x is less than x itself
%
let MinFix = new_definition
  (`MinFix`,
   "MinFix (Fn:(*->bool)->(*->bool)) = (GLB (\x:*->bool. (Fn x) Leq x))");;

%
  The requirement to the minimal fixed point is that it is really a fixed
  point IsFix and that it is smaller than every other fixed point
%
let IsMinFix = new_definition
  (`IsMinFix`,
   "IsMinFix Fn x =
      (IsFix Fn x) /\ (!y:*->bool. (IsFix Fn y) ==> (x Leq y))");;

%
  The Least Upper Bound (LUB) of a set X is the union of all members of the set
%
let LUB = new_definition
  (`LUB`,
   "LUB (X:(*->bool)->bool) = \s:*. ?x. (x In X) /\ x s");;

%
  The maximal fixed point of a monotonic functional Fn is the LUB of the set
  of functions all satisfying that the application of the functional to a
  parameter x is greater than x itself
%
let MaxFix = new_definition
  (`MaxFix`,
   "MaxFix (Fn:(*->bool)->(*->bool)) = (LUB (\x:*->bool. x Leq (Fn x)))");;

%
  The requirement to the maximal fixed point is that it is really a fixed
  point and that it is greater than any other fixed point
%
let IsMaxFix = new_definition
  (`IsMaxFix`,
   "IsMaxFix Fn x =
       IsFix Fn x /\ (!y:*->bool. IsFix Fn y ==> (y Leq x))");;


%
 =============================================================================

  We now prove that Leq constitutes a complete lattice


    1) Leq is a partial order:

	a) Leq is transitive
	b) Leq is reflexive
	c) Leq is antisymmetric


    2) Leq has a least upper bound (LUB) and a greatest lower bound (GLB):

	a) LUB is an upper bound
	b) LUB is the maximal upper bound
	c) GLB is a lower bound
	d) GLB is the minimal lower bound

 =============================================================================
%

%
  First we prove that Leq is a partial order:
%

%
  Leq is transitive:
%
let LeqThm1 = TAC_PROOF
  (([],
   "!(x:*->bool) y z. x Leq y ==> y Leq z ==> x Leq z"),
   REWRITE_TAC [Leq] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

%
  Leq is reflexive:
%
let LeqThm2 = TAC_PROOF
  (([],
   "!(x:*->bool). x Leq x"),
   REWRITE_TAC [Leq]);;

%
  Leq is antisymmetric:
%
let LeqThm3_lemma = TAC_PROOF
  (([],
   "!(x:*->bool) y. x Leq y ==> y Leq x ==> (!s. x s = y s)"),
   REWRITE_TAC [Leq] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN RES_TAC);;

%
  |- !x y. x Leq y ==> y Leq x ==> (x = y)
%
let LeqThm3 = (GEN_ALL (DISCH_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (UNDISCH_ALL
                (SPEC_ALL LeqThm3_lemma))))));;

let LeqThm4 = TAC_PROOF
  (([],
   "!(x:*->bool) y. (x Leq y /\ y Leq x) = (x = y)"),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
    [
     STRIP_TAC THEN
     IMP_RES_TAC LeqThm3
    ;
     STRIP_TAC THEN
     ASM_REWRITE_TAC [LeqThm2]
    ]);;

let LeqThm5 = TAC_PROOF
  (([],
   "!(x:*->bool) y z.
     (x Leq (y And z)) = (x Leq y /\ x Leq z)"),
   REWRITE_TAC [And;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

let LeqThm6 = TAC_PROOF
  (([],
   "!(x:*->bool) y. (x And y) Leq y"),
   REWRITE_TAC [And;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC);;

let LeqThm7 = TAC_PROOF
  (([],
   "!(x:*->bool) y. (x And y) Leq x"),
   REWRITE_TAC [And;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC);;

let LeqThm8 = TAC_PROOF
  (([],
   "!(x:*->bool) y. x Leq (x Or y)"),
   REWRITE_TAC [Or;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let LeqThm9 = TAC_PROOF
  (([],
   "!(x:*->bool) y. x Leq (y Or x)"),
   REWRITE_TAC [Or;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let LeqThm10 = TAC_PROOF
  (([],
   "!(x:*->bool) y. (x Or y) Leq y ==> x Leq y"),
   REWRITE_TAC [Or;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LeqThm11 = TAC_PROOF
  (([],
   "!(x:*->bool) y. (y Or x) Leq y ==> x Leq y"),
   REWRITE_TAC [Or;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LeqThm12 = TAC_PROOF
  (([],
   "!(x:*->bool) y z. (x Leq z /\ y Leq z) = ((x Or y) Leq z)"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [Or;Leq] THEN
   BETA_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
 -----------------------------------------------------------------------------

  Properties of GLB and LUB

 -----------------------------------------------------------------------------
%

%
  (GLB X) is less than any other relation in X, hence GLB returns a lower
  bound.
%
let Min_MinGLBThm = TAC_PROOF
  (([],
   "!(X:(*->bool)->bool) x. x In X ==> ((GLB X) Leq x)"),
   REWRITE_TAC [GLB;In;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  For any x less than any member y of X, x satisfies that it is less than
  (GLB X).  Hence GLB returns the greatest lower bound.
%
let Greatest_MinGLBThm = TAC_PROOF
  (([],
   "!(X:(*->bool)->bool) x. (!y. y In X ==> (x Leq y)) ==> (x Leq (GLB X))"),
   REWRITE_TAC [GLB;In;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  (LUB X) is greater than any other relation in X. Hence LUB returns an upper
  bound.
%
let Max_MaxLUBThm = TAC_PROOF
  (([],
   "!(X:(*->bool)->bool) x. x In X ==> (x Leq (LUB X))"),
   REWRITE_TAC [LUB;In;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC "x:*->bool" THEN
   ASM_REWRITE_TAC []);;

%
  For any x greater than any member y of X, x satisfies that it is greater than
  (LUB X).  Hence LUB returns the least upper bound.
%
let Least_MaxLUBThm = TAC_PROOF
  (([],
   "!(X:(*->bool)->bool) x. (!y. y In X ==> (y Leq x)) ==> ((LUB X) Leq x)"),
   REWRITE_TAC [LUB;In;Leq] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;


%
 =============================================================================

  Now we may prove the fixed point theorems:

 =============================================================================
%

%
 -----------------------------------------------------------------------------

  First the minimal fixed point:

 -----------------------------------------------------------------------------
%

%
  Prove that MinFix is smaller than every other fixed point
%
let Min_MinFixThm = prove_thm
  (`Min_MinFixThm`,
   "!(Fn:(*->bool)->(*->bool)) x. (Fn x = x) ==> ((MinFix Fn) Leq x)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MinFix] THEN
   STRIP_ASSUME_TAC (ONCE_REWRITE_RULE
     [SYM (SPEC_ALL LeqThm4)] (ASSUME "(Fn:(*->bool)->(*->bool)) x = x")) THEN
   ACCEPT_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. ((Fn:(*->bool)->(*->bool)) x) Leq x";"x:*->bool"]
      Min_MinGLBThm)))));;

%
  Now prove that MinFix is a fixed point
%
let MinFixImplyThm1_lemma = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==>
       (!x. (Fn x) Leq x ==> (Fn(GLB(\x. (Fn x) Leq x))) Leq x)"),
   REWRITE_TAC [IsMono] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. ((Fn:(*->bool)->(*->bool)) x) Leq x";"x:*->bool"]
      Min_MinGLBThm)))) THEN
   RES_TAC THEN
   ACCEPT_TAC (UNDISCH_ALL (SPECL
    ["(Fn:(*->bool)->(*->bool))(GLB(\x. (Fn x) Leq x))";
     "(Fn:(*->bool)->(*->bool)) x";"x:*->bool"] LeqThm1)));;

let MinFixImplyThm1 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)).
      IsMono Fn ==> (Fn (MinFix Fn) Leq (MinFix Fn))"),
   REWRITE_TAC [MinFix] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MinFixImplyThm1_lemma THEN
   ASSUME_TAC (BETA_RULE (REWRITE_RULE [In] (SPECL
    ["\x. ((Fn:(*->bool)->(*->bool)) x) Leq x";
     "(Fn:(*->bool)->(*->bool))(GLB(\x. (Fn x) Leq x))"]
     Greatest_MinGLBThm))) THEN
   RES_TAC);;

let MinFixImplyThm2 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==> (MinFix Fn) Leq Fn (MinFix Fn)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (BETA_RULE (REWRITE_RULE [In;SYM (SPEC_ALL MinFix)]
    (SPECL ["\x. ((Fn:(*->bool)->(*->bool)) x) Leq x";
            "(Fn:(*->bool)->(*->bool)) (MinFix (Fn:(*->bool)->(*->bool)))"]
            Min_MinGLBThm))) THEN
   IMP_RES_TAC MinFixImplyThm1 THEN
   ASSUME_TAC (REWRITE_RULE
    [IsMono] (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   RES_TAC);;

%
 -----------------------------------------------------------------------------

   Prove that MinFix has the fixed point property:

 -----------------------------------------------------------------------------
%
let MinFixEQThm = prove_thm
  (`MinFixEQThm`,
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==> (Fn (MinFix Fn) = (MinFix Fn))",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MinFixImplyThm2 THEN
   IMP_RES_TAC MinFixImplyThm1 THEN
   IMP_RES_TAC LeqThm3);;

%
  And MinFix is the smallest fixed point
%
let IsMinFixThm = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==> IsMinFix Fn (MinFix Fn)"),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   REWRITE_TAC [IsMinFix;IsFix] THEN
   REWRITE_TAC [UNDISCH (SPEC_ALL MinFixEQThm);Min_MinFixThm]);;

%
 -----------------------------------------------------------------------------

  Now, prove some MinFix introduction theorems

 -----------------------------------------------------------------------------
%

%
  Prove the MinFix introduction theorem
%

let MinFixIntroductThm = prove_thm
  (`MinFixIntroductThm`,
   "!(Fn:(*->bool)->(*->bool)) x. (Fn x Leq x) ==> (MinFix Fn) Leq x",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MinFix] THEN
   ACCEPT_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. ((Fn:(*->bool)->(*->bool)) x) Leq x";"x:*->bool"]
      Min_MinGLBThm)))));;

let ExtMinFixIntroductThm_lemma01 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x.
      (Fn (x And MinFix Fn)) Leq (x And MinFix Fn) ==> (MinFix Fn) Leq x"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (SPECL
    ["Fn:(*->bool)->(*->bool)";"(x:*->bool) And MinFix Fn"]
     MinFixIntroductThm)) THEN
   ASSUME_TAC (SPECL
    ["x:*->bool";"MinFix (Fn:(*->bool)->(*->bool))"] LeqThm7) THEN
   IMP_RES_TAC LeqThm1);;

%
  |- !Fn Y. IsMono Fn ==> (Fn(Y And (MinFix Fn))) Leq (MinFix Fn)
%
let ExtMinFixIntroductThm_lemma02 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (Fn (x And MinFix Fn)) Leq (MinFix Fn)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL
    ["x:*->bool";"MinFix (Fn:(*->bool)->(*->bool))"] LeqThm6) THEN
   ASSUME_TAC (REWRITE_RULE [IsMono]
    (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   IMP_RES_TAC MinFixImplyThm1 THEN
   IMP_RES_TAC LeqThm1);;

let ExtMinFixIntroductThm = prove_thm
  (`ExtMinFixIntroductThm`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (Fn(x And (MinFix Fn)) Leq x) ==> ((MinFix Fn) Leq x)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [UNDISCH (SPEC_ALL ExtMinFixIntroductThm_lemma02)] (SPEC_ALL (BETA_RULE
      (REWRITE_RULE [LeqThm5] ExtMinFixIntroductThm_lemma01)))));;

let ExtMinFixIntroductThm1_lemma0 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x. (x And (MinFix Fn)) Leq x"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [Leq;And] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC);;
   
let ExtMinFixIntroductThm1_lemma = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x. (x And (MinFix Fn)) Leq (MinFix Fn)"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [Leq;And] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC);;

let ExtMinFixIntroductThm1 = prove_thm
  (`ExtMinFixIntroductThm1`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> ((MinFix Fn) Leq x) ==> (Fn(x And (MinFix Fn)) Leq x)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL ExtMinFixIntroductThm1_lemma) THEN
   ASSUME_TAC
    (REWRITE_RULE [IsMono] (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   ASSUME_TAC (REWRITE_RULE [UNDISCH (SPEC_ALL MinFixEQThm)] (ASSUME
    "((Fn:(*->bool)->(*->bool))(x And (MinFix Fn))) Leq (Fn(MinFix Fn))")) THEN
   IMP_RES_TAC LeqThm1);;

%
 -----------------------------------------------------------------------------

   A theorem for proving an extended induction principle:

 -----------------------------------------------------------------------------
%
let ExtMinFixIntroductEQThm = prove_thm
  (`ExtMinFixIntroductEQThm`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (((MinFix Fn) Leq x) = (Fn(x And (MinFix Fn)) Leq x))",
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN STRIP_TAC THENL
    [
     IMP_RES_TAC ExtMinFixIntroductThm1
    ;
     IMP_RES_TAC ExtMinFixIntroductThm
    ]);;


%
 -----------------------------------------------------------------------------

  Next the maximal fixed point:

 -----------------------------------------------------------------------------
%

%
 -----------------------------------------------------------------------------

  Prove that MaxFix is greater than any other fixed point:

 -----------------------------------------------------------------------------
%
let Max_MaxFixThm = prove_thm
  (`Max_MaxFixThm`,
   "!(Fn:(*->bool)->(*->bool)) x. (Fn x = x) ==> x Leq (MaxFix Fn)",
   REWRITE_TAC [MaxFix;SYM (SPEC_ALL LeqThm4)] THEN
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. x Leq ((Fn:(*->bool)->(*->bool)) x)";"x:*->bool"]
      Max_MaxLUBThm)))));;

%
 -----------------------------------------------------------------------------

  Prove the MaxFix introduction theorem

 -----------------------------------------------------------------------------
%
let MaxFixIntroductThm = prove_thm
  (`MaxFixIntroductThm`,
   "!(Fn:(*->bool)->(*->bool)) x. x Leq (Fn x) ==> x Leq (MaxFix Fn)",
   REWRITE_TAC [MaxFix;SYM (SPEC_ALL LeqThm4)] THEN
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. x Leq ((Fn:(*->bool)->(*->bool)) x)";"x:*->bool"]
      Max_MaxLUBThm)))));;

%
  Prove that MaxFix is a fixed point:
%
let MaxFixImplyThm1_lemma = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==>
       (!x. x Leq (Fn x) ==> (x Leq Fn(LUB(\x. x Leq (Fn x)))))"),
   REWRITE_TAC [IsMono] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
     ["\x. x Leq ((Fn:(*->bool)->(*->bool)) x)";"x:*->bool"]
      Max_MaxLUBThm)))) THEN
   RES_TAC THEN
   ACCEPT_TAC (UNDISCH_ALL (SPECL
    ["x:*->bool";"(Fn:(*->bool)->(*->bool)) x";
     "(Fn:(*->bool)->(*->bool))(LUB(\x. x Leq (Fn x)))"] LeqThm1)));;

let MaxFixImplyThm1 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)).
       IsMono Fn ==> (MaxFix Fn) Leq (Fn (MaxFix Fn))"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MaxFix] THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL
    (REWRITE_RULE [MaxFix] MaxFixImplyThm1_lemma))) THEN
   ACCEPT_TAC (UNDISCH (BETA_RULE (REWRITE_RULE [In] (SPECL
    ["\x. x Leq ((Fn:(*->bool)->(*->bool)) x)";
     "(Fn:(*->bool)->(*->bool))(LUB(\x. x Leq (Fn x)))"]
     Least_MaxLUBThm)))));;

let MaxFixImplyThm2 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)).
       IsMono Fn ==>  (Fn (MaxFix Fn)) Leq (MaxFix Fn)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (BETA_RULE (REWRITE_RULE [In;SYM (SPEC_ALL MaxFix)]
    (SPECL ["\x. x Leq ((Fn:(*->bool)->(*->bool)) x)";
            "(Fn:(*->bool)->(*->bool)) (MaxFix (Fn:(*->bool)->(*->bool)))"]
            Max_MaxLUBThm))) THEN
   IMP_RES_TAC MaxFixImplyThm1 THEN
   ASSUME_TAC (REWRITE_RULE
    [IsMono] (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   RES_TAC);;

%
 -----------------------------------------------------------------------------

   Prove that MaxFix has the fixed point property:

 -----------------------------------------------------------------------------
%
let MaxFixEQThm = prove_thm
  (`MaxFixEQThm`,
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==> (Fn (MaxFix Fn) = MaxFix Fn)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC MaxFixImplyThm1 THEN
   IMP_RES_TAC MaxFixImplyThm2 THEN
   IMP_RES_TAC LeqThm4);;

%
  Finally we may prove that MaxFix is the greatest fixed point
%
let IsMaxFixThm = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)). IsMono Fn ==> IsMaxFix Fn (MaxFix Fn)"),
   GEN_TAC THEN
   DISCH_TAC THEN
   REWRITE_TAC [IsMaxFix;IsFix] THEN
   REWRITE_TAC [UNDISCH (SPEC_ALL MaxFixEQThm);Max_MaxFixThm]);;


let ExtMaxFixIntroductThm_lemma01 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x.
     IsMono Fn ==> 
       (x Or MaxFix Fn) Leq (Fn (x Or MaxFix Fn)) ==> x Leq (MaxFix Fn)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (SPECL
    ["Fn:(*->bool)->(*->bool)";"(x:*->bool) Or MaxFix Fn"]
     MaxFixIntroductThm)) THEN
   IMP_RES_TAC LeqThm10);;

let ExtMaxFixIntroductThm_lemma02 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (MaxFix Fn) Leq (Fn (x Or MaxFix Fn))"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL
    ["MaxFix (Fn:(*->bool)->(*->bool))";"x:*->bool"] LeqThm9) THEN
   ASSUME_TAC (REWRITE_RULE [IsMono]
    (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   IMP_RES_TAC MaxFixImplyThm1 THEN
   IMP_RES_TAC LeqThm1);;

let ExtMaxFixIntroductThm = prove_thm
  (`ExtMaxFixIntroductThm`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> x Leq Fn (x Or (MaxFix Fn)) ==> x Leq (MaxFix Fn)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ACCEPT_TAC (UNDISCH (REWRITE_RULE
    [UNDISCH (SPEC_ALL ExtMaxFixIntroductThm_lemma02)] (SPEC_ALL (BETA_RULE
      (REWRITE_RULE [SYM (SPEC_ALL LeqThm12)]
         ExtMaxFixIntroductThm_lemma01))))));;

let ExtMaxFixIntroductThm1_lemma0 = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x. x Leq (x Or (MaxFix Fn))"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [Leq;Or] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;
   
let ExtMaxFixIntroductThm1_lemma = TAC_PROOF
  (([],
   "!(Fn:(*->bool)->(*->bool)) x. (MaxFix Fn) Leq (x Or (MaxFix Fn))"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [Leq;Or] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let ExtMaxFixIntroductThm1 = prove_thm
  (`ExtMaxFixIntroductThm1`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (x Leq (MaxFix Fn)) ==> (x Leq Fn(x Or (MaxFix Fn)))",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL ExtMaxFixIntroductThm1_lemma) THEN
   ASSUME_TAC
    (REWRITE_RULE [IsMono] (ASSUME "IsMono (Fn:(*->bool)->(*->bool))")) THEN
   RES_TAC THEN
   ASSUME_TAC (REWRITE_RULE [UNDISCH (SPEC_ALL MaxFixEQThm)] (ASSUME
    "(Fn(MaxFix Fn)) Leq ((Fn:(*->bool)->(*->bool))(x Or (MaxFix Fn)))")) THEN
   IMP_RES_TAC LeqThm1);;

%
 -----------------------------------------------------------------------------

   A theorem for proving an extended induction principle:

 -----------------------------------------------------------------------------
%
let ExtMaxFixIntroductEQThm = prove_thm
  (`ExtMaxFixIntroductEQThm`,
   "!(Fn:(*->bool)->(*->bool)) x.
      IsMono Fn ==> (x Leq ((MaxFix Fn)) = (x Leq Fn(x Or (MaxFix Fn))))",
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN STRIP_TAC THENL
    [
     IMP_RES_TAC ExtMaxFixIntroductThm1
    ;
     IMP_RES_TAC ExtMaxFixIntroductThm
    ]);;


close_theory();;


% End Of File %
