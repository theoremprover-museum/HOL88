
%-----------------------------------------------------------------------%
% PLEASE FORGIVE THE USE OF AN EDITOR WITH WIDTH > 80 CHARACTERS...	%
%-----------------------------------------------------------------------%

set_flag (`sticky`, true);;

system `rm fpf.th`;;
new_theory `fpf`;;
load_library `sets`;;

loadf `RENAME_TAC`;;
loadf `set_ind`;;
loadf `SSMART_EXISTS_TAC`;;
loadf `ELIMINATE_TACS`;;





%-----------------------------------------------------------------------%
% a few aux. tactics							%
%-----------------------------------------------------------------------%

let DEEP_SYM_CONV = (ONCE_DEPTH_CONV SYM_CONV);;
let DEEP_SYM = (CONV_RULE DEEP_SYM_CONV);;



let DEEP_SYM_ASM_REWRITE_TAC l (asl,g) =
       REWRITE_TAC (l @ 
            (map (\t. DEEP_SYM (ASSUME t) ? (ASSUME t)) asl)) 
          (asl,g);;

let UNDISCH_ALL_TAC = POP_ASSUM_LIST  (EVERY o (map MP_TAC));;
let DEEP_SYM_ASM_THEN tac  =
   POP_ASSUM_LIST (\asms.
      EVERY (map ((ASSUME_TAC o DEEP_SYM) ? ASSUME_TAC) asms)
      THEN tac
   );;






%-----------------------------------------------------------------------%
% theory of finite partial functions					%
%-----------------------------------------------------------------------%



%-----------------------------------------------------------------------%
%
< Some notes on finite partial functions (or finite maps):
<
<
< Besides their finite domain, the important 
< property of finite maps is what happens when we apply    
< things to them.  This is done using the APPLY function defined below.
< Two results are possible - a failure (the result then being FAILURE),
< or a result (RESULT x).  The actual type returned by APPLY is (**+one), where
< ** is the type of the range of the map.  Thus FAILURE = INR one, and 
< RESULT x = INL x.  The user of the finite partial functions can in general
< avoid using the somewhat cryptic INL, INR, OUTL etc. constructors, for
< RESULT, FAILURE, RESULTOF and SUCCEEDS are far more inuitive.
<
<  The constants defined:
<    ZIP = The empty map
<    EXT = extends a map by adding on new mapping
<    APPLY = applies a value to the map to see what it maps to if anything
<    DOM = domain of the map (i.e. the things that are mapped to something)
<    EXTBY = adds one map to another, the first taking precedence
<    SUCCEEDS = true if an application succeeds, as in SUCCEEDS(APPLY x fpf)
<    FAILURE = the result of APPLY when what we are applying doesn't map to anything
<    RESULT x = the result of APPLY when what we are applying maps to x
<    RESULTOF = access the result of a successful application
<    PORTION = predicate to see if one map is a subset of another
<    TRANSFORM = transforms elements of the range of a map by a given function
<    RANGE = range of a map
<    UNEXT = deletes a mapping from a map (Un-Extension)
<    LIST_TO_FPF = converts a list of pairs to a map - useful to allow the use
< of list nottation to specify maps.
<    EVERYF = applies a predicate test to every mapping in the map.
<
< Some examples of things that are easily provable by rewriting:
<
<   APPLY x ZIP = FAILURE 
<   APPLY 1 (EXT (1,10) ZIP) = RESULT 10
<   DOM ZIP = {}
<   DOM (EXT (1,10) ZIP) = {1}
<
<  Finite maps are created using the EXT operator.  All maps have their basis in
< the empty map ZIP.  Inuitively EXT is a cross between CONS and INSERT.  
< The argument to EXT is a pair indicating a maplet 
< x |-> y.  The ordering of EXT's is unimportant if all the domain elements are
< distinct.  However:
<     EXT (1, 100) (EXT (1, 0) ZIP) = EXT (1,100)
< can be proven - i.e. extensions override original mappings.
<
< The finiteness of the maps is captured by the induction principles that are
< proved.  The first induction principle is often not useful, for it does
< not ensure that previous mappings are not overridden.  Often we want to induct
< over the cardinality of the domain of the map, or to use the additional
< assumption that the new extension being added to the map in the step case
< does not already have a value in the map.  These induction principles are
< proved below (see fpf_INDUCT_2).
<									%
%-----------------------------------------------------------------------%


let INL_INR_11 = prove_constructors_one_one sum_Axiom;;
let INL_11 = save_thm(`INL_11`, CONJUNCT1 INL_INR_11);;
let INR_11 = save_thm(`INR_11`, CONJUNCT2 INL_INR_11);;



let FAILURE_DEF = new_definition(`FAILURE_DEF`, "(FAILURE:(**+one)) = INR one");;

let RESULT_DEF = new_definition(`RESULT_DEF`, "(RESULT:(**)->(**+one)) = INL");;

let SUCCEEDS_DEF = new_definition(`SUCCEEDS_DEF`, "(SUCCEEDS:(**+one)->bool) = ISL");;

let FAILS_DEF = new_definition(`FAILS_DEF`, "(FAILS:(**+one)->bool) = ISR");;

let RESULTOF_DEF = new_definition(`RESULTOF_DEF`, "(RESULTOF:(**+one)->**) = OUTL");;

let RESULT_11 = prove_thm(`RESULT_11`, "!(x:**) x'. (RESULT x = RESULT x') = (x = x')",
   REWRITE_TAC [RESULT_DEF; INL_11]);;


let SUCCEEDS_RESULT = prove_thm(`SUCCEEDS_RESULT`, "!x:*. SUCCEEDS (RESULT x)",
   REWRITE_TAC [RESULT_DEF;ISL;SUCCEEDS_DEF]);;

let NOT_SUCCEEDS_FAILURE = prove_thm(`NOT_SUCCEEDS_FAILURE`, "~(SUCCEEDS:(*+one)->bool) FAILURE",
   REWRITE_TAC [SUCCEEDS_DEF; FAILURE_DEF; ISL]);;

let RESULTOF_RESULT = prove_thm(`RESULTOF_RESULT`, "!x:*. RESULTOF (RESULT x) = x", 
    REWRITE_TAC [OUTL;RESULTOF_DEF;RESULT_DEF]);;  

let FAILS_FAILURE = prove_thm(`FAILS_FAILURE`, "FAILS (FAILURE:(**+one))", REWRITE_TAC [FAILS_DEF;FAILURE_DEF;ISR]);;

let NOT_FAILS_RESULT = prove_thm(`NOT_FAILS_RESULT`, "!x. ~(FAILS:(**+one)->bool) (RESULT x)",
   REWRITE_TAC [FAILS_DEF;RESULT_DEF;ISR]);;

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%


let ZIP_REP_DEF = new_definition
   (`ZIP_REP_DEF`,
    "(ZIP_REP:*->(**+one)) = \x.FAILURE"
   );;

let EXT_REP_DEF = new_definition
   (`EXT_REP_DEF`,
    "EXT_REP (x:*,y:**) (map:*->(**+one)) = (\x'.(x=x')=>RESULT y|map x')");;

let IS_fpf_REP = new_definition
   (`IS_fpf_REP`,
    "IS_fpf_REP (fpf:*->(**+one)) = 
       (!P:((*->(**+one))->bool) . P ZIP_REP /\
          (!fpf' x y. P fpf' ==> P(EXT_REP (x,y) fpf')) ==>  P fpf)"
   );;

let fpf_REP_EXISTS = PROVE("?fpf. IS_fpf_REP (fpf:*->(**+one))",
   REWRITE_TAC [IS_fpf_REP]
   THEN EXISTS_TAC "ZIP_REP:*->(**+one)"
   THEN REPEAT STRIP_TAC);;

let fpf_TY_DEF = 
   new_type_definition
      (`fpf`,
       "IS_fpf_REP:(*->(**+one))->bool",
       fpf_REP_EXISTS);;


let fpf_ISO_DEF = 
    define_new_type_bijections
        `fpf_ISO_DEF` `ABS_fpf` `REP_fpf` fpf_TY_DEF;;


let R_11 = prove_rep_fn_one_one fpf_ISO_DEF     and
    R_ONTO = prove_rep_fn_onto fpf_ISO_DEF      and
    A_11   = prove_abs_fn_one_one fpf_ISO_DEF   and
    A_ONTO = prove_abs_fn_onto fpf_ISO_DEF      and
    A_R = CONJUNCT1 fpf_ISO_DEF                 and
    R_A = CONJUNCT2 fpf_ISO_DEF;;



let ZIP_DEF = new_definition
   (`ZIP_DEF`,
    "(ZIP:(*,**)fpf) = ABS_fpf (\x.FAILURE)"
   );;

let ZIP_DEF_LEMMA = PROVE("(ZIP:(*,**)fpf) = ABS_fpf ZIP_REP", REWRITE_TAC [ZIP_DEF; ZIP_REP_DEF]);;

let IS_fpf_REP_ZIP = PROVE("IS_fpf_REP (ZIP_REP:*->(**+one))",
    REWRITE_TAC [IS_fpf_REP; ZIP_REP_DEF; ]
    THEN REPEAT STRIP_TAC
   );;



let EXT_DEF = new_definition
   (`EXT_DEF`,
    "EXT (x:*,y:**) map = ABS_fpf (\x'.(x=x')=>RESULT y|(REP_fpf map) x')");;

let EXT_DEF_LEMMA = PROVE("!x y map. EXT (x:*,y:**) map = ABS_fpf (EXT_REP (x,y) (REP_fpf map))",
    REWRITE_TAC [EXT_DEF; EXT_REP_DEF]);;


let IS_fpf_EXT_REP = PROVE(
    "!x y (fpf:*->(**+one)). (IS_fpf_REP fpf) ==> IS_fpf_REP (EXT_REP (x,y) fpf)",

    PURE_REWRITE_TAC [IS_fpf_REP; ZIP_REP_DEF; EXT_REP_DEF]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC []
);;

let IS_fpf_REP_EXT_REP = PROVE(
    "!x y fpf. IS_fpf_REP (EXT_REP (x,y) (REP_fpf fpf))",
    REPEAT GEN_TAC
    THEN MATCH_MP_TAC IS_fpf_EXT_REP
    THEN REWRITE_TAC[R_ONTO]
    THEN EXISTS_TAC "fpf"
    THEN REFL_TAC
   );;


let R_A_lemma_1 = PROVE(
    "REP_fpf ((ABS_fpf (\x:*.FAILURE)):(*,**)fpf) = (\x:*.FAILURE)",
    REWRITE_TAC [DEEP_SYM R_A; IS_fpf_REP; ZIP_REP_DEF]
    THEN REPEAT STRIP_TAC
);;


let R_A_lemma_2 = PROVE(
    "!(fpf:(*,**)fpf) x y.  REP_fpf (ABS_fpf (\x'. ((x = x') => RESULT y | (REP_fpf fpf) x'))) =
          (\x'. ((x = x') => RESULT y | (REP_fpf fpf) x'))",
    REWRITE_TAC [DEEP_SYM EXT_REP_DEF; DEEP_SYM R_A; IS_fpf_REP_EXT_REP]
);;

let R_A_lemma = CONJ R_A_lemma_1  R_A_lemma_2;;

let REP_LEMMA = PROVE(
    "IS_fpf_REP (REP_fpf (fpf:(*,**)fpf))",
    REWRITE_TAC [R_ONTO]
    THEN EXISTS_TAC "fpf:(*,**)fpf"
    THEN REFL_TAC
   );;






%----------------------------------------------------------------
  induction -- this parallels the derivation of induction by
               T. Melham for natural numbers.
----------------------------------------------------------------%
let ind_lemma_1 = PROVE(
   "!P. P ZIP_REP /\ 
         (!(fpf:*->(**+one)) x y. (P fpf ==> P (EXT_REP (x,y) fpf))) ==>
            (!(fpf:*->(**+one)). IS_fpf_REP fpf ==> P fpf)",
    PURE_ONCE_REWRITE_TAC [IS_fpf_REP]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
);;

let lemma = TAC_PROOF
   (([], "(A ==> A /\ B) = (A ==> B)"),
    ASM_CASES_TAC "A:bool"
    THEN ASM_REWRITE_TAC []
   );;

let ind_lemma_2 = TAC_PROOF
   (([],"!P. P ZIP_REP /\ 
         (!(fpf:*->(**+one)) x y. 
            (IS_fpf_REP fpf /\ P fpf ==> P (EXT_REP (x,y) fpf))) ==>
               (!(fpf:*->(**+one)). IS_fpf_REP fpf ==> P fpf)"),
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (SPEC "\fpf:*->(**+one). IS_fpf_REP fpf /\ P fpf" ind_lemma_1) THEN
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC [lemma;IS_fpf_REP_ZIP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THENL 
    [IMP_RES_THEN MATCH_ACCEPT_TAC IS_fpf_EXT_REP;
     RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let lemma1 = PROVE(
    "(! fpf:*->(**+one). IS_fpf_REP fpf ==> P(ABS_fpf fpf)) = (! fpf. P fpf)",
    EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN STRIP_ASSUME_TAC (SPEC "fpf:(*,**)fpf" A_ONTO)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
  );;


let SYM_RULE =
  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
? failwith `SYM_RULE`;;



let fpf_INDUCT = prove_thm 
   (`fpf_INDUCT`,
   "!P. (P ZIP /\ (!fpf. P fpf ==> !(x:*) (y:**). P(EXT (x,y) fpf))) ==> !fpf. P fpf",
    GEN_TAC
    THEN STRIP_TAC
    THEN MP_TAC (SPEC "\fpf:*->(**+one). P(ABS_fpf fpf):bool" ind_lemma_2)
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC [(SYM_RULE ZIP_DEF_LEMMA); lemma1]
    THEN DISCH_THEN MATCH_MP_TAC
    THEN REWRITE_TAC [R_ONTO]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC ANTE_CONJ_CONV
    THEN DISCH_THEN (STRIP_THM_THEN SUBST1_TAC)
    THEN ASM_REWRITE_TAC [A_R; (SYM_RULE (SPEC_ALL EXT_DEF_LEMMA))] 
    THEN STRIP_TAC THEN RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC
   );;

let fpf_INDUCT_TAC = INDUCT_THEN fpf_INDUCT ASSUME_TAC;;








%----------------------------------------------------------------
  Primitive theorems
----------------------------------------------------------------%


				    


%----------------------------------------------------------------
  APPLY  (derived from finite set IN code, though more of my own stuff here)
----------------------------------------------------------------%



let APPLY_DEF = new_definition
   (`APPLY_DEF`,
    "APPLY x (map:(*,**)fpf) = (REP_fpf map) x");;

let APPLY_ZIP = prove_thm(`APPLY_ZIP`,
   "!x. APPLY x (ZIP:(*,**)fpf) = FAILURE",
   REWRITE_TAC [APPLY_DEF; ZIP_DEF; R_A_lemma]);;

let NOT_SUCCEEDS_APPLY_ZIP = prove_thm(`NOT_SUCCEEDS_APPLY_ZIP`,
   "!x. SUCCEEDS(APPLY x (ZIP:(*,**)fpf)) = F",
   REWRITE_TAC [APPLY_DEF; ZIP_DEF; R_A_lemma] THEN REWRITE_TAC [SUCCEEDS_DEF; FAILURE_DEF; ISL]);;

let APPLY_EXT = prove_thm(`APPLY_EXT`,
   "!x y v (f:(*,**)fpf). APPLY x (EXT (y,v) f) = ((y=x)=>RESULT v|APPLY x f)",
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [APPLY_DEF; EXT_DEF; R_A_lemma]
   THEN BETA_TAC
   THEN COND_CASES_TAC
   THEN REWRITE_TAC []
);;

let APPLY = save_thm(`APPLY`,CONJ APPLY_ZIP APPLY_EXT);;

let EQ_IMP_APPLY_EXT = prove_thm(`EQ_IMP_APPLY_EXT`,
   "!x y v (f:(*,**)fpf). (y=x) ==> (APPLY x (EXT (y,v) f) = RESULT v)",
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [APPLY_DEF; EXT_DEF; R_A_lemma]
   THEN BETA_TAC
   THEN ASM_REWRITE_TAC []
);;


let NE_IMP_APPLY_EXT = prove_thm(`NE_IMP_APPLY_EXT`,
   "!x y v (f:(*,**)fpf). ~(y=x) ==> (APPLY x (EXT (y,v) f) = APPLY x f)",
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [APPLY_DEF; EXT_DEF; R_A_lemma]
   THEN BETA_TAC
   THEN ASM_REWRITE_TAC []
);;




%----------------------------------------------------------------
  fpf EQUALITY
----------------------------------------------------------------%




let fpf_EQ = prove_thm
   (`fpf_EQ`,
   "! (f1:(*,**)fpf) f2 . (f1 = f2) = !x.(APPLY x f1) = (APPLY x f2)",
    REPEAT STRIP_TAC
    THEN EQ_TAC
    THENL [
        REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC []
    ;   REWRITE_TAC [APPLY_DEF]
        THEN REPEAT STRIP_TAC
        THEN POP_ASSUM (\th . ACCEPT_TAC (REWRITE_RULE [R_11] (EXT th)))
    ]
   );;
 



let NOT_INL_EQ_INR = prove_thm(`NOT_INL_EQ_INR`, "!(x:*) (y:**). ~(INL x = INR y)",
   REPEAT STRIP_TAC THEN (DISJ_CASES_THEN MP_TAC (SPEC "(INL x):(*+**)" ISL_OR_ISR)) 
   THENL [PURE_ONCE_ASM_REWRITE_TAC []; ALL_TAC] THEN REWRITE_TAC [ISL;ISR]
);;


let NOT_RESULT_EQ_FAILURE = save_thm(`NOT_RESULT_EQ_FAILURE`, 
    REWRITE_RULE [DEEP_SYM FAILURE_DEF; DEEP_SYM RESULT_DEF] (ISPECL ["x:*";"one"] NOT_INL_EQ_INR));;

let NOT_FAILURE_EQ_RESULT = save_thm(`NOT_FAILURE_EQ_RESULT`, 
    DEEP_SYM NOT_RESULT_EQ_FAILURE);;


let NOT_EXT_ZIP = prove_thm(`NOT_EXT_ZIP`,
   "!(x:*) (y:**) f. (EXT(x,y)f = ZIP) = F",
   REWRITE_TAC [fpf_EQ; PAIR_EQ;APPLY]
   THEN REPEAT GEN_TAC THEN CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC "x:*"
   THEN REWRITE_TAC [NOT_FAILURE_EQ_RESULT;NOT_RESULT_EQ_FAILURE]
);;

let NOT_ZIP_EXT = prove_thm(`NOT_ZIP_EXT`,
   "!(x:*) (y:**) f. (ZIP = EXT(x,y)f) = F",
   REWRITE_TAC [fpf_EQ; PAIR_EQ;APPLY]
   THEN REPEAT GEN_TAC THEN CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC "x:*"
   THEN REWRITE_TAC [NOT_FAILURE_EQ_RESULT;NOT_RESULT_EQ_FAILURE]
);;






let EXT_EXT = prove_thm(`EXT_EXT`,
   "!x u v (f:(*,**)fpf). (EXT(x,u) (EXT (x,v) f) = EXT(x,u) f)",
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [fpf_EQ; APPLY; NOT_EXT_ZIP; NOT_ZIP_EXT]
   THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
);;



let EXT_COMM = prove_thm(`EXT_COMM`, 
   "!x y u v (f:(*,**)fpf). ~(x = y) ==> (EXT(x,u) (EXT (y,v) f) = EXT(y,v) (EXT(x,u) f))",
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [fpf_EQ; APPLY; NOT_EXT_ZIP; NOT_ZIP_EXT]
   THEN GEN_TAC THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC [] THEN DEEP_SYM_ASM_REWRITE_TAC []
);;

let fpf_SING_EQ = prove_thm(`fpf_SING_EQ`, 
   "!(x:*) (y:**) x' y'.
      (EXT (x,y) ZIP = EXT (x',y') ZIP) ==> (x = x') /\ (y = y')",
   REWRITE_TAC [fpf_EQ;APPLY] THEN REPEAT GEN_TAC 
   THEN DISCH_THEN (MP_TAC o REWRITE_RULE [] o SPEC "x:*")
   THEN COND_CASES_TAC 
   THEN ASM_REWRITE_TAC [NOT_RESULT_EQ_FAILURE; NOT_FAILURE_EQ_RESULT; RESULT_11]
);;

let fpf_PAIR_EQ = prove_thm(`fpf_PAIR_EQ`,
   "!(x:*) x' (y:**) y'  y'' y'''.
      ~(x = x') ==>
      (EXT (x,y) (EXT (x',y'')ZIP) = EXT (x,y') (EXT (x',y''')ZIP)) ==>
         (y = y') /\ (y'' = y''')",
   REPEAT GEN_TAC THEN REWRITE_TAC [fpf_EQ; APPLY]
   THEN DISCH_TAC
   THEN DISCH_THEN (\t. MP_TAC (REWRITE_RULE [] (SPEC "x:*" t)) THEN  MP_TAC (REWRITE_RULE [] (SPEC "x':*" t)))
   THEN ASM_REWRITE_TAC [RESULT_11]
   THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
);;






%< This is a REALLY bad proof, but it worked, so I left it >%


let fpf_SND_ABSORPTION = prove_thm(`fpf_SND_ABSORPTION`,
   "!fpf (d:*) (y:**). (SUCCEEDS(APPLY d fpf)) = ?!y. (EXT (d,y) fpf = fpf)",
   REWRITE_TAC [EXISTS_UNIQUE_DEF]
   THEN BETA_TAC THEN BETA_TAC
   THEN INDUCT_THEN fpf_INDUCT STRIP_ASSUME_TAC
   THEN ASM_REWRITE_TAC [NOT_EXT_ZIP; APPLY; NOT_SUCCEEDS_FAILURE]
   THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN TRY SMART_ELIMINATE_TAC THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT]
   THENL [
      CONJ_TAC 
      THENL [
         EXISTS_TAC "y:**" THEN REWRITE_TAC [EXT_EXT]
      ;  REPEAT GEN_TAC THEN REWRITE_TAC [EXT_EXT; fpf_EQ; APPLY]
         THEN STRIP_TAC 
         THEN POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
         THEN SMART_ELIMINATE_TAC 
         THEN POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
	 THEN ASM_REWRITE_TAC []
      ]
    ; EQ_TAC THEN REPEAT STRIP_TAC
      THENL [
            RES_TAC THEN EXISTS_TAC "y':**" 
            THEN DEEP_SYM_ASM_THEN 
               (ONCE_REWRITE_TAC [UNDISCH_ALL (SPECL ["d:*";"x:*";"y':**";"y:**";"fpf"] EXT_COMM)] )
            THEN SMART_ELIMINATE_TAC THEN REWRITE_TAC [EXT_EXT]
         ;  UNDISCH_ALL_TAC
            THEN REPEAT GEN_TAC THEN REWRITE_TAC [EXT_EXT; fpf_EQ; APPLY]
            THEN REPEAT STRIP_TAC
            THEN POP_ASSUM (MP_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
            THEN POP_ASSUM (MP_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
	    THEN ASM_REWRITE_TAC []
            THEN REPEAT STRIP_TAC
            THEN SMART_TERM_ELIMINATE_TAC 
            THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE [RESULT_11]))

       ; EXISTS_TAC "y':**"
         THEN POP_ASSUM (\t. ALL_TAC)
         THEN POP_ASSUM MP_TAC
         THEN ASM_REWRITE_TAC [fpf_EQ; APPLY]
	 THEN REPEAT STRIP_TAC
	 THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
	 THEN UNDISCH_ALL_TAC
	 THEN COND_CASES_TAC
         THEN ASM_REWRITE_TAC []
         THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
       ; POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
         THEN REWRITE_TAC [fpf_EQ; APPLY]
            THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
            THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [RESULT_11]) o (SPEC "d:*"))
            THEN SMART_TERM_ELIMINATE_TAC 
            THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE [RESULT_11]))
      ]
   ]
);;





%----------------------------------------------------------------
  PORTION - equivalent to subset.  Not very useful.
     Was one day hoping to prove the following induction property:

    "!P. P ZIP /\ 
          (!(fpf:(*,**)fpf) x. (!f. ~(SND (APPLY x f)) /\ PORTION f fpf ==> P f) 
                 ==> !y. P(EXT (x,y) fpf))
          ==> (!fpf. !f. PORTION f fpf ==> P f)";;
----------------------------------------------------------------%


let PORTION_DEF = new_definition(`PORTION_DEF`,
  "PORTION (f:(*,**)fpf) f' = !x y. (APPLY x f = RESULT y) ==> (APPLY x f' = RESULT y)");;

let PORTION_SELF = prove_thm(`PORTION_SELF`, "!(f:(*,**)fpf). PORTION f f", REWRITE_TAC [PORTION_DEF]);;
let PORTION_ZIP = prove_thm(`PORTION_ZIP`, "!(f:(*,**)fpf). PORTION f ZIP = (f = ZIP)", 
   REWRITE_TAC [PORTION_DEF;APPLY;PAIR_EQ] THEN fpf_INDUCT_TAC THEN 
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [APPLY;PAIR_EQ;NOT_EXT_ZIP]
   THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
   THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
   THEN EXISTS_TAC "x" THEN EXISTS_TAC "y" THEN REWRITE_TAC [NOT_FAILURE_EQ_RESULT; NOT_RESULT_EQ_FAILURE]
);;




%----------------------------------------------------------------
  EXTBY  (derived from finite set UNION code)
----------------------------------------------------------------%



let EXTBY_P = new_definition
   (`EXTBY_P`,
    "EXTBY_P f (map:(*,**)fpf) map' = 
        !x. APPLY x f = (SUCCEEDS(APPLY x map))=>(APPLY x map)|(APPLY x map')");;


let EXTBY_DEF = new_definition
   (`EXTBY_DEF`,
    "EXTBY (map:(*,**)fpf) map' = @f. EXTBY_P f map map'");;


						     
let EXTBY_MEMBER_LEMMA = PROVE(
  "!(f1:(*,**)fpf) f2.  EXTBY_P (EXTBY f1 f2) f1 f2",
  REWRITE_TAC [EXTBY_DEF]
    THEN REWRITE_TAC [SYM_RULE EXTBY_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [EXTBY_P]
    THEN SPEC_TAC ("f1","f1")
    THEN INDUCT_THEN fpf_INDUCT MP_TAC
    THENL [ % 1 %
        EXISTS_TAC "f2"
        THEN REWRITE_TAC [NOT_SUCCEEDS_APPLY_ZIP]
    ;  % 2 %
        REPEAT STRIP_TAC
        THEN EXISTS_TAC "(EXT (x,y) (f:(*,**)fpf))"
        THEN GEN_TAC
        THEN REWRITE_TAC [APPLY]
        THEN ASM_CASES_TAC "(x:*) = x'"
        THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT]
    ]
);;



let APPLY_EXTBY = save_thm (`APPLY_EXTBY`, REWRITE_RULE [EXTBY_P] EXTBY_MEMBER_LEMMA);;

let EXTBY_ZIP_LEMMA = PROVE(
   "! f:(*,**)fpf . EXTBY ZIP f = f",
    REWRITE_TAC [fpf_EQ; APPLY_EXTBY;NOT_SUCCEEDS_APPLY_ZIP]
   );;
let EXTBY_EXT_1 = PROVE(
    "! x y (f1:(*,**)fpf) f2 .
      EXTBY f1 (EXT (x,y) f2) = 
          (SUCCEEDS(APPLY x f1)) => EXTBY f1 f2 | (EXT (x,y) (EXTBY f1 f2))",
    REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC [fpf_EQ; APPLY_EXTBY;APPLY]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x = x'"
    THEN TRY SMART_ELIMINATE_TAC
    THEN ASM_REWRITE_TAC []
   );;




let EXTBY_EXT_2 = PROVE(
   "!x y (f1:(*,**)fpf) f2. EXTBY (EXT (x,y) f1) f2 = EXT (x,y) (EXTBY f1 f2)",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [fpf_EQ; APPLY_EXTBY;APPLY]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x = x'"
    THEN TRY SMART_ELIMINATE_TAC
    THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT]
   );;



let EXTBY = save_thm (`EXTBY`, (CONJ EXTBY_ZIP_LEMMA (CONJ EXTBY_EXT_1 EXTBY_EXT_2)));;

 


   







%----------------------------------------------------------------
  TRANSFORM - sort of like compose really
(but can't compose two partial functions)
----------------------------------------------------------------%


let TRANSFORM_P = new_definition
   (`TRANSFORM_P`,
    "TRANSFORM_P map' (fn:**->***) (map:(*,**)fpf) = 
        !x. APPLY x map' = (SUCCEEDS(APPLY x map))=>RESULT(fn (RESULTOF(APPLY x map))) |FAILURE");;

let TRANSFORM_DEF = new_definition
   (`TRANSFORM_DEF`,
    "TRANSFORM (fn:**->***) (map:(*,**)fpf) = @map'. TRANSFORM_P map' fn map");;


						     
let TRANSFORM_MEMBER_LEMMA = PROVE(
  "!(fn:**->***) (map:(*,**)fpf).  TRANSFORM_P (TRANSFORM fn map) fn map",
  REWRITE_TAC [TRANSFORM_DEF]
    THEN REWRITE_TAC [SYM_RULE TRANSFORM_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [TRANSFORM_P]
    THEN SPEC_TAC ("map","map")
    THEN INDUCT_THEN fpf_INDUCT MP_TAC
    THENL [ % 1 %
        EXISTS_TAC "ZIP:(*,***)fpf"
        THEN PURE_ONCE_REWRITE_TAC [NOT_SUCCEEDS_APPLY_ZIP] THEN REWRITE_TAC [APPLY]
    ;  % 2 %
        REPEAT STRIP_TAC
        THEN EXISTS_TAC "(EXT (x,(fn (y:**))) (map':(*,***)fpf))"
        THEN GEN_TAC
        THEN REWRITE_TAC [APPLY]
        THEN ASM_CASES_TAC "(x:*) = x'"
        THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT; RESULTOF_RESULT]
    ]
);;



let APPLY_TRANSFORM = save_thm (`APPLY_TRANSFORM`, REWRITE_RULE [TRANSFORM_P] TRANSFORM_MEMBER_LEMMA);;

let TRANSFORM_ZIP = PROVE(
   "! fn:(**->***). TRANSFORM fn (ZIP:(*,**)fpf) = ZIP",
    REWRITE_TAC [fpf_EQ; APPLY_TRANSFORM;APPLY; NOT_SUCCEEDS_FAILURE]
   );;
let TRANSFORM_EXT = PROVE(
    "! fn:(**->***) (fpf:(*,**)fpf) x y. 
      TRANSFORM fn (EXT (x,y) fpf) = 
          (EXT (x,fn y) (TRANSFORM fn fpf))",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [fpf_EQ; APPLY_TRANSFORM;APPLY]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x = x'"
    THEN TRY SMART_ELIMINATE_TAC
    THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT; RESULTOF_RESULT]
   );;



let TRANSFORM = save_thm (`TRANSFORM`, (CONJ TRANSFORM_ZIP TRANSFORM_EXT));;

 





%----------------------------------------------------------------
  DOM
----------------------------------------------------------------%




let DOM_P = new_definition
   (`DOM_P`,
    "DOM_P dom (map:(*,**)fpf) = 
        !x. x IN dom = (SUCCEEDS(APPLY x map))");;

let DOM_DEF = new_definition
   (`DOM_DEF`,
    "DOM (map:(*,**)fpf) = @dom'. DOM_P dom' map");;


						     
let DOM_MEMBER_LEMMA = PROVE(
  "!(map:(*,**)fpf).  DOM_P (DOM map) map",
  REWRITE_TAC [DOM_DEF]
    THEN REWRITE_TAC [SYM_RULE DOM_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [DOM_P]
    THEN SPEC_TAC ("map","map")
    THEN INDUCT_THEN fpf_INDUCT MP_TAC
    THENL [ % 1 %
        EXISTS_TAC "EMPTY:(*)set"
        THEN REWRITE_TAC [NOT_IN_EMPTY;NOT_SUCCEEDS_APPLY_ZIP]
    ;  % 2 %
        REPEAT STRIP_TAC
        THEN RENAME_TAC
        THEN EXISTS_TAC "x INSERT (dom':(*)set)"
        THEN GEN_TAC
        THEN REWRITE_TAC [APPLY;IN_INSERT]
        THEN ASM_CASES_TAC "(x:*) = x'"
        THEN ASM_REWRITE_TAC [SUCCEEDS_RESULT]
       THEN EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN TRY SMART_ELIMINATE_TAC 
       THEN ASM_REWRITE_TAC []
       THEN UNDISCH_ALL_TAC
       THEN REWRITE_TAC []
    ]
);;



let IN_DOM = save_thm (`IN_DOM`, REWRITE_RULE [DOM_P] DOM_MEMBER_LEMMA);;

let DOM_ZIP = PROVE(
    "DOM (ZIP:(*,**)fpf) = EMPTY",
    REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_DOM;APPLY; NOT_SUCCEEDS_FAILURE]
   );;
let DOM_EXT = PROVE(
    "! (fpf:(*,**)fpf) x y. 
      DOM (EXT (x,y) fpf) = 
          (x INSERT (DOM fpf))",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [EXTENSION; IN_DOM;APPLY]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x = x'"
    THEN TRY SMART_ELIMINATE_TAC 
    THEN ASM_REWRITE_TAC [IN_INSERT; IN_DOM; SUCCEEDS_RESULT]
    THEN EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN TRY SMART_ELIMINATE_TAC 
       THEN ASM_REWRITE_TAC []
       THEN UNDISCH_ALL_TAC
       THEN REWRITE_TAC []

   );;




let DOM = save_thm (`DOM`, (CONJ DOM_ZIP DOM_EXT));;



let EMPTY_DOM  = prove_thm(`EMPTY_DOM`,
   "!(f:(*,**)fpf). (DOM f = {}) = (f = ZIP)",
GEN_TAC THEN EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC [DOM]]
THEN SPEC_TAC ("f","f") THEN fpf_INDUCT_TAC THEN ASM_REWRITE_TAC [DOM;NOT_EXT_ZIP;NOT_INSERT_EMPTY]
);;




let IN_DOM_IMP_APPLY = prove_thm (`IN_DOM_IMP_APPLY`, 
   "!(fpf:(*,**)fpf) x. x IN (DOM fpf) ==> (?y. (APPLY x fpf) = RESULT y)",
   fpf_INDUCT_TAC THENL [
      REWRITE_TAC [DOM_ZIP; NOT_IN_EMPTY; APPLY]
    ; REPEAT GEN_TAC THEN REWRITE_TAC [DOM_EXT; IN_INSERT; APPLY]
      THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL [
         EXISTS_TAC "y:**" THEN REWRITE_TAC []
       ; REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SMART_ELIMINATE_TAC
         THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [])
      ]
   ]);;


let IN_DOM_EQ_APPLY = prove_thm (`IN_DOM_EQ_APPLY`, 
    "!(fpf:(*,**)fpf) x. x IN (DOM fpf) = (?y. (APPLY x fpf) = RESULT y)",                                               
   REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [IN_DOM_IMP_APPLY]
   THEN SPEC_TAC ("fpf","fpf") THEN fpf_INDUCT_TAC
   THENL [
      REWRITE_TAC [APPLY;NOT_FAILURE_EQ_RESULT;DOM;NOT_IN_EMPTY]
    ; REWRITE_TAC [APPLY;DOM;IN_INSERT]
      THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN DEEP_SYM_ASM_REWRITE_TAC [] 
      THEN FIRST_ASSUM ACCEPT_TAC 
   ]
);;

let NOT_IN_DOM_IMP_APPLY = prove_thm (`NOT_IN_DOM_IMP_APPLY`, 
   "!(fpf:(*,**)fpf) x. ~(x IN (DOM fpf)) ==> (APPLY x fpf = FAILURE)",
   fpf_INDUCT_TAC THENL [
      REWRITE_TAC [DOM_ZIP; NOT_IN_EMPTY; APPLY]
    ; REPEAT GEN_TAC THEN REWRITE_TAC [DOM_EXT; IN_INSERT; APPLY]
      THEN PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
      THEN REPEAT STRIP_TAC  THEN DEEP_SYM_ASM_REWRITE_TAC [] THEN RES_TAC
   ]);;


%----------------------------------------------------------------
  ABSORPTION cont.
I think the following is the most powerful of the absorption/decomposition results.
It is needed to get the induction results that follow.  Effectively
we are proving that for (EXT(x,y)f) there is a partial function f'
for which (EXT(x,y)f') is the same as (EXT(x,y)f) and x is not in the
domain of f'.  Essentially a decomposition theorem really, but the
name has stuck...

Nb. All of this is probably superseded by the derivation of UNEXT below.
----------------------------------------------------------------%


let EXT_ABSORPTION = prove_thm(`EXT_ABSORPTION`,
  "!f (x:*). ?f'. !(y:**). 
      (EXT(x,y) f = EXT(x,y) f') /\ 
      (!x'. (APPLY x' f' = ((x' = x) => FAILURE | APPLY x' f))) /\
      (DOM f' = (DOM f) DELETE x)",
fpf_INDUCT_TAC
THENL [
   REPEAT GEN_TAC
   THEN EXISTS_TAC "ZIP:(*,**)fpf"
   THEN ASM_REWRITE_TAC [APPLY;DOM;EMPTY_DELETE]
   THEN REPEAT STRIP_TAC THEN COND_CASES_TAC  THEN ASM_REWRITE_TAC []
; REPEAT GEN_TAC
   THEN POP_ASSUM (STRIP_ASSUME_TAC o (SPECL ["x'':*"]))
   THEN ASM_CASES_TAC "(x'':*) = x"
   THENL [
      SMART_ELIMINATE_TAC
      THEN EXISTS_TAC "f':(*,**)fpf"
      THEN ASM_REWRITE_TAC [EXT_EXT;APPLY;EXTENSION;IN_DOM;IN_DELETE;PAIR_EQ]
      THEN CONJ_TAC 
      THEN REPEAT STRIP_TAC 
      THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
      THEN POP_ASSUM (ASSUME_TAC o DEEP_SYM) THEN ASM_REWRITE_TAC [NOT_SUCCEEDS_FAILURE]
   ;  EXISTS_TAC "EXT((x:*),(y:**))f'"
      THEN ONCE_ASM_REWRITE_TAC [UNDISCH_ALL (SPEC_ALL (SPECL ["x'':*";"x:*"] EXT_COMM))]
      THEN ASM_REWRITE_TAC [EXT_EXT;APPLY;EXTENSION;IN_DOM;IN_DELETE;PAIR_EQ]
      THEN CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
      THEN POP_ASSUM (\t1. POP_ASSUM (\t2. ASSUME_TAC (DEEP_SYM t2) THEN
             ASSUME_TAC (DEEP_SYM t1)))
      THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC []
      THEN REPEAT SMART_ELIMINATE_TAC THEN UNDISCH_ALL_TAC THEN REWRITE_TAC [NOT_SUCCEEDS_FAILURE]
   ]
]
);;





%----------------------------------------------------------------
  CARDINALITY OF THE DOMAIN
----------------------------------------------------------------%


let DOM_FINITE = prove_thm(`DOM_FINITE`,
   "!f:(*,**)fpf. FINITE(DOM f)",
   fpf_INDUCT_TAC
   THEN REWRITE_TAC [FINITE_EMPTY; DOM]
   THEN IMP_RES_TAC FINITE_INSERT
);;


let CARD_DOM_INSERT = prove_thm(`CARD_DOM_INSERT`,
   "!x (f:(*,**)fpf). CARD(x INSERT (DOM f)) = (x IN (DOM f) => CARD (DOM f) | SUC(CARD (DOM f)))",
   REPEAT GEN_TAC THEN ASSUME_TAC (SPEC "f" DOM_FINITE) THEN IMP_RES_TAC CARD_INSERT
   THEN ASM_REWRITE_TAC []
);;

let CARD_DOM_EQ_0 = prove_thm(`CARD_DOM_EQ_0`,
   "!x (f:(*,**)fpf). (CARD(DOM f) = 0) = (f = ZIP)",
   REPEAT GEN_TAC THEN ASSUME_TAC (SPEC "f" DOM_FINITE) THEN IMP_RES_TAC CARD_EQ_0
   THEN ASM_REWRITE_TAC [EMPTY_DOM]
);;



   %----------------------------------------------------------------
     CARD_EQ_SUC - This really should have been proven in sets.ml
   ----------------------------------------------------------------%

let FINITE_RULE t = UNDISCH o (SPEC t);;

let CARD_EQ_SUC = prove_thm(`CARD_EQ_SUC`,
 "!i (s:(*)set).  
    FINITE s ==> (CARD s = SUC i) ==> 
    ?s' x. ~x IN s' /\ (CARD s' = i) /\ (s = x INSERT s')",
   GEN_TAC THEN SET_INDUCT_TAC
   THEN ASM_REWRITE_TAC [CARD_EMPTY; SUC_NOT; FINITE_RULE "s" CARD_INSERT; INV_SUC_EQ]
   THEN STRIP_TAC THEN RES_TAC THEN REPEAT (SSMART_EXISTS_TAC)
   THEN ASM_REWRITE_TAC []
);;

   %----------------------------------------------------------------
     CARD_DOM_SUC - This really should have been proven in sets.ml
   ----------------------------------------------------------------%


let CARD_DOM_SUC = prove_thm(`CARD_DOM_SUC`,
  "!(f:(*,**)fpf) i. (CARD(DOM f) = SUC i) ==>
    ?f' x y. ~(SUCCEEDS(APPLY x f')) /\ (CARD(DOM f') = i) /\ (f = EXT(x,y)f')",
   fpf_INDUCT_TAC THEN REWRITE_TAC [CARD_EMPTY; DOM_ZIP;SUC_NOT]
   THEN REPEAT STRIP_TAC THEN ASSUME_TAC (SPEC "f" DOM_FINITE) 
   THEN STRIP_ASSUME_TAC (SPEC_ALL EXT_ABSORPTION)
   THEN EXISTS_TAC  "f'"
   THEN EXISTS_TAC  "x"
   THEN EXISTS_TAC  "y"
   THEN ASM_REWRITE_TAC [fpf_EQ;APPLY;NOT_SUCCEEDS_FAILURE]
   THEN REPEAT STRIP_TAC
   THENL [
      REWRITE_TAC [FINITE_RULE "DOM (f:(*,**)fpf)" CARD_DELETE]
      THEN UNDISCH_TAC "CARD(DOM(EXT(x,y)(f:(*,**)fpf))) = SUC i" 
      THEN REWRITE_TAC [DOM;FINITE_RULE "(DOM (f:(*,**)fpf))" CARD_INSERT]
      THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
      THEN STRIP_TAC THEN IMP_RES_TAC INV_SUC THEN ASM_REWRITE_TAC [SUC_SUB1]
   ;    
      COND_CASES_TAC THEN ASM_REWRITE_TAC [PAIR_EQ] 
      THEN POP_ASSUM (ASSUME_TAC o DEEP_SYM)
      THEN ASM_REWRITE_TAC [PAIR_EQ]
   ]
);;



%----------------------------------------------------------------
  STRONG INDUCTION RESULTS
     STRONG_INDUCTION
        Strong Induction over the natural numbers
     fpf_CARD_INDUCT
        Induction over the cardinality of the domain of the finite map
 
    fpf_INDUCT_2 - similar to SET_INDUCT_TAC_2 where the elemenat added can be assumed to
        not be already in the domain of the function.  Not a trivial exercise to prove!
        Proved by induction over the cardinality of the domain.

    fpf_STRONG_INDUCT - similar to SET_INDUCT_TAC_2 where the elemenat added can be assumed to

----------------------------------------------------------------%



let STRONG_INDUCTION_lemma = prove_thm(`STRONG_INDUCTION_lemma`,
  "!P. P 0 /\ (!j. (!i. i <= j ==> P i) ==> P (SUC j)) ==> 
      !n. (!i. i <= n ==> P i)",
GEN_TAC THEN STRIP_TAC THEN INDUCT_THEN INDUCTION MP_TAC
THEN UNDISCH_ALL_TAC THEN REWRITE_TAC [GREATER; LESS_OR_EQ; NOT_LESS_0]
THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
THENL [
   FIRST_ASSUM MATCH_MP_TAC
   THEN IMP_RES_TAC LESS_SUC_IMP
   THEN ASM_CASES_TAC "i = n"
   THEN RES_TAC
   THEN ASM_REWRITE_TAC []
 ; RES_TAC
]
);;

let STRONG_INDUCTION = save_thm(`STRONG_INDUCTION`,
    (GEN_ALL (DISCH_ALL (GEN_ALL 
    (REWRITE_RULE [LESS_OR_EQ] (SPECL ["n";"n"] (UNDISCH_ALL (SPEC_ALL STRONG_INDUCTION_lemma))))
    ))));;





let fpf_CARD_INDUCT = 
   let P = "\n. !(f:(*,**)fpf). 
      CARD(DOM f) <= n ==> P f" in
   let t1 = REWRITE_RULE [LESS_OR_EQ; NOT_LESS_0;CARD_DOM_EQ_0] (BETA_RULE (SPEC P STRONG_INDUCTION)) in
   let t2 = REWRITE_RULE [] (SPECL ["CARD(DOM (f':(*,**)fpf))";"f':(*,**)fpf"] (UNDISCH_ALL t1)) in
      save_thm(`fpf_CARD_INDUCT`,
         GEN_ALL (REWRITE_RULE [DEEP_SYM LESS_OR_EQ] (DISCH_ALL (GEN "f'" t2))));;



let fpf_INDUCT_2 = prove_thm(`fpf_INDUCT_2`,
   "!P. P ZIP /\ 
          (!(fpf:(*,**)fpf) x y. P fpf ==> ~SUCCEEDS(APPLY x fpf) ==> P(EXT (x,y) fpf))
             ==> (!fpf. P fpf)",
   REPEAT STRIP_TAC		
   THEN SPEC_TAC ("fpf","fpf")
   THEN MATCH_MP_TAC fpf_CARD_INDUCT
   THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
   THEN UNDISCH_ALL_TAC
   THEN REWRITE_TAC [LESS_OR_EQ]
   THEN REPEAT STRIP_TAC
   THENL [
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [LESS_EQ_MONO;LESS_OR_EQ]) o (MATCH_MP LESS_OR))
      THEN POP_ASSUM (\t1. POP_ASSUM (\t2. ASSUME_TAC (MATCH_MP t2 t1)))
      THEN POP_ASSUM (ASSUME_TAC o (REWRITE_RULE []) o (SPEC "f"))
      THEN ASM_REWRITE_TAC []
   ;  IMP_RES_TAC CARD_DOM_SUC
      THEN FIRST_ASSUM (IMP_RES_TAC o REWRITE_RULE [] o SPEC "j:num")
      THEN SMART_ELIMINATE_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []
   ]);;


let fpf_INDUCT_TAC_2 (asm,gl) =
   (MATCH_MP_TAC (BETA_RULE (SPEC (snd (dest_comb gl)) fpf_INDUCT_2))
   THEN REPEAT STRIP_TAC) (asm,gl);;





%----------------------------------------------------------------
  RANGE
----------------------------------------------------------------%




let RANGE_P = new_definition
   (`RANGE_P`,
    "RANGE_P ran (map:(*,**)fpf) = 
        !y. y IN ran = (?x. APPLY x map = RESULT y)");;

let RANGE_DEF = new_definition
   (`RANGE_DEF`,
    "RANGE (map:(*,**)fpf) = @ran'. RANGE_P ran' map");;


						     
let RANGE_MEMBER_LEMMA = PROVE(
  "!(fpf:(*,**)fpf).  RANGE_P (RANGE fpf) fpf",
  REWRITE_TAC [RANGE_DEF]
    THEN REWRITE_TAC [SYM_RULE RANGE_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [RANGE_P]
    THEN SPEC_TAC ("fpf","fpf")
    THEN fpf_INDUCT_TAC_2
    THENL [ % 1 %
        EXISTS_TAC "EMPTY:(**)set"
        THEN REWRITE_TAC [APPLY;NOT_IN_EMPTY;NOT_FAILURE_EQ_RESULT;NOT_RESULT_EQ_FAILURE]
    ;  % 2 %
        EXISTS_TAC "y INSERT (ran':(**)set)"
        THEN GEN_TAC
        THEN REWRITE_TAC [APPLY;IN_INSERT]
        THEN ASM_CASES_TAC "(y':**) = y"
        THEN ASM_REWRITE_TAC []
        THENL [
           EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC []
        ;  EQ_TAC THEN STRIP_TAC 
           THENL [
              EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC []
              THEN COND_CASES_TAC 
              THENL [
                 SMART_ELIMINATE_TAC THEN SMART_TERM_ELIMINATE_TAC 
                 THEN UNDISCH_ALL_TAC THEN REWRITE_TAC [SUCCEEDS_RESULT]
              ; ASM_REWRITE_TAC []
              ]
           ;  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []
              THENL [ 
                 DEEP_SYM_ASM_REWRITE_TAC [RESULT_11] 
              ;  DISCH_TAC THEN EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC []
              ]
           ]
        ]
    ]
);;



let IN_RANGE = save_thm (`IN_RANGE`, REWRITE_RULE [RANGE_P] RANGE_MEMBER_LEMMA);;

let RANGE_ZIP = prove_thm(`RANGE_ZIP`,
    "RANGE (ZIP:(*,**)fpf) = EMPTY",
    REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_RANGE;APPLY;NOT_FAILURE_EQ_RESULT; NOT_RESULT_EQ_FAILURE]
   );;
let RANGE_EXT = prove_thm(`RANGE_EXT`,
    "! (fpf:(*,**)fpf) x y. 
      ~(x IN (DOM fpf)) ==>
          (RANGE (EXT (x,y) fpf) =  y  INSERT (RANGE fpf))",

    REPEAT GEN_TAC
    THEN REWRITE_TAC [EXTENSION;IN_DOM;IN_RANGE;APPLY;IN_INSERT;IN_DELETE]
    THEN STRIP_TAC THEN GEN_TAC
    THEN EQ_TAC THEN STRIP_TAC
    THENL [
       POP_ASSUM MP_TAC THEN COND_CASES_TAC
       THEN REWRITE_TAC [RESULT_11] THEN DISCH_TAC THEN ASM_REWRITE_TAC []
       THEN DISJ2_TAC THEN EXISTS_TAC "x'':*" THEN FIRST_ASSUM ACCEPT_TAC
    ;  EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC []
    ;  EXISTS_TAC "x'':*" THEN ASM_REWRITE_TAC []
       THEN COND_CASES_TAC THEN TRY SMART_VAR_ELIMINATE_TAC  THEN TRY SMART_TERM_ELIMINATE_TAC
       THEN UNDISCH_ALL_TAC THEN REWRITE_TAC [SUCCEEDS_RESULT] 
    ]
);;




let EMPTY_RANGE  = prove_thm(`EMPTY_RANGE`,
   "!(f:(*,**)fpf). (RANGE f = {}) = (f = ZIP)",
GEN_TAC THEN EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC [RANGE_ZIP]]
THEN SPEC_TAC ("f","f") THEN fpf_INDUCT_TAC_2
THEN UNDISCH_ALL_TAC
THEN REWRITE_TAC [(UNDISCH (SPEC_ALL (PURE_REWRITE_RULE [IN_DOM] RANGE_EXT)))]
THEN ASM_REWRITE_TAC [NOT_EXT_ZIP;NOT_INSERT_EMPTY]
);;



%----------------------------------------------------------------
  LIST_TO_FPF - generates a finite partial function from a list of pairs
----------------------------------------------------------------%

let LIST_TO_FPF_DEF = new_recursive_definition false list_Axiom `LIST_TO_FPF_DEF`
   "(LIST_TO_FPF [] = ZIP) /\ (LIST_TO_FPF (CONS (pr:(* # **)) t) = EXT pr (LIST_TO_FPF t))";;




%----------------------------------------------------------------
  UNEXT
----------------------------------------------------------------%


let SUCCEEDS_OR_FAILURE = prove_thm(`SUCCEEDS_OR_FAILURE`,
   "!x (fpf:(*,**)fpf). SUCCEEDS(APPLY x fpf) \/ FAILS(APPLY x fpf)",

   REPEAT GEN_TAC 
   THEN DISJ_CASES_TAC (REWRITE_RULE [DEEP_SYM SUCCEEDS_DEF] (ISPEC "APPLY x (fpf:(*,**)fpf)" ISL_OR_ISR))
   THEN ASM_REWRITE_TAC [] THEN IMP_RES_TAC INR THEN POP_ASSUM (SUBST1_TAC o DEEP_SYM)
   THEN PURE_ONCE_REWRITE_TAC [one]
   THEN REWRITE_TAC [FAILS_DEF; ISR]
);;



let UNEXT_P = new_definition
   (`UNEXT_P`,
    "UNEXT_P x fpf1 (fpf2:(*,**)fpf) = 
        !x'. (x = x') => (APPLY x' fpf2 = FAILURE) | (APPLY x' fpf1 = APPLY x' fpf2)");;

let UNEXT_DEF = new_definition
   (`UNEXT_DEF`,
    "UNEXT x (fpf:(*,**)fpf) = @fpf'. UNEXT_P x fpf fpf'");;


						     
let UNEXT_MEMBER_LEMMA = PROVE(
  "!x (fpf:(*,**)fpf).  UNEXT_P x fpf (UNEXT x fpf)",
  REWRITE_TAC [UNEXT_DEF]
    THEN REWRITE_TAC [SYM_RULE UNEXT_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [UNEXT_P]
    THEN SPEC_TAC ("fpf","fpf")
    THEN fpf_INDUCT_TAC_2
    THENL [ % 1 %
        EXISTS_TAC "ZIP:(*,**)fpf"
        THEN REWRITE_TAC [APPLY] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []
    ;  % 2 %
        EXISTS_TAC "(x' = x) => fpf' | EXT (x',y) fpf'"
        THEN GEN_TAC
        THEN REWRITE_TAC [APPLY]
        THEN COND_CASES_TAC THEN COND_CASES_TAC
        THEN TRY SMART_ELIMINATE_TAC 
        THEN ASM_REWRITE_TAC [APPLY]
        THENL [
           FIRST_ASSUM (ACCEPT_TAC o REWRITE_RULE [] o SPEC "x:*")
         ; FIRST_ASSUM (ACCEPT_TAC o REWRITE_RULE [] o SPEC "x'':*")
	 ; DEEP_SYM_ASM_REWRITE_TAC [APPLY]
         ; COND_CASES_TAC
           THEN FIRST_ASSUM (\t. if is_forall(concl t) then UNDISCH_TAC (concl t) else fail)
           THEN DISCH_THEN (MP_TAC o SPEC "x'':*")
	   THEN ASM_REWRITE_TAC [APPLY]
        ]
    ]
);;


let APPLY_UNEXT = save_thm (`APPLY_UNEXT`, REWRITE_RULE [UNEXT_P] UNEXT_MEMBER_LEMMA);;

let UNEXT_ZIP = prove_thm(`UNEXT_ZIP`,
    "!x. UNEXT x (ZIP:(*,**)fpf) = ZIP",
    REWRITE_TAC [fpf_EQ; APPLY] THEN REPEAT GEN_TAC
    THEN ASM_CASES_TAC "x = x'"
    THEN MP_TAC (SPECL ["x";"ZIP:(*,**)fpf";"x'"] APPLY_UNEXT)
    THEN ASM_REWRITE_TAC []
    THEN STRIP_TAC THEN DEEP_SYM_ASM_REWRITE_TAC [APPLY]
);;

let APPLY_UNEXT_SAME = save_thm(`APPLY_UNEXT_SAME`,
      GEN_ALL(REWRITE_RULE [] (SPECL ["x:*";"fpf";"x:*"] APPLY_UNEXT)));;

let APPLY_UNEXT_DIFF = save_thm(`APPLY_UNEXT_DIFF`,
      PROVE("!x (fpf:(*,**)fpf) x'. ~(x = x') ==> (APPLY x' fpf = APPLY x' (UNEXT x fpf))",
         REPEAT STRIP_TAC THEN MP_TAC (SPECL ["x:*";"fpf";"x':*"] APPLY_UNEXT)
         THEN ASM_REWRITE_TAC []));;


%< Another grotesque proof involving too many cases >%

let UNEXT_EXT = prove_thm(`UNEXT_EXT`,
    "!fpf x x' y. UNEXT x (EXT (x',y) fpf) = (x = x') => (UNEXT x fpf) | EXT (x',y) (UNEXT x fpf)",

    fpf_INDUCT_TAC THEN REPEAT GEN_TAC
    THENL [
       COND_CASES_TAC THEN ASM_REWRITE_TAC [UNEXT_ZIP;APPLY;fpf_EQ]
       THEN GEN_TAC THENL [
          MP_TAC (SPECL ["x'";"EXT(x',y)ZIP";"x''"] APPLY_UNEXT)
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY] THEN DISCH_THEN (ACCEPT_TAC o SYM)
        ; MP_TAC (SPECL ["x";"EXT(x',y)ZIP";"x''"] APPLY_UNEXT)
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY] THENL [
             SMART_ELIMINATE_TAC THEN DISCH_TAC THEN DEEP_SYM_ASM_REWRITE_TAC []
	   ; COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ACCEPT_TAC o SYM)
          ]
       ]
     ;
       COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY;fpf_EQ]
       THEN GEN_TAC THENL [
          MP_TAC (SPECL ["x'";"EXT(x',y')(EXT(x,y)fpf)";"x''':*"] APPLY_UNEXT)
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY] THENL [
             COND_CASES_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [APPLY;APPLY_UNEXT_SAME]
             THEN DEEP_SYM_ASM_REWRITE_TAC []
          ;  COND_CASES_TAC THENL [
                SMART_ELIMINATE_TAC THEN ASM_REWRITE_TAC [APPLY]
                THEN DISCH_TAC THEN DEEP_SYM_ASM_REWRITE_TAC []
   	      ; COND_CASES_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THENL [
                   IMP_RES_TAC APPLY_UNEXT_DIFF
                   THEN FIRST_ASSUM (ACCEPT_TAC o SPEC_ALL)
                 ; ASM_REWRITE_TAC [APPLY]
                   THEN IMP_RES_TAC APPLY_UNEXT_DIFF
                   THEN FIRST_ASSUM (ACCEPT_TAC o SPEC_ALL)
		]
             ]
          ]
        ;

          MP_TAC (SPECL ["x''";"EXT(x',y')(EXT(x,y)fpf)";"x''':*"] APPLY_UNEXT)
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY] THENL [
             DISCH_THEN (SUBST1_TAC)
             THEN SMART_ELIMINATE_TAC THEN DEEP_SYM_ASM_REWRITE_TAC [APPLY_UNEXT_SAME]
          ;  DISCH_THEN (SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
             THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY]
             THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPLY]
             THEN IMP_RES_TAC APPLY_UNEXT_DIFF
             THEN FIRST_ASSUM (ACCEPT_TAC o SPEC_ALL)
          ]
       ]
    ]);;




%----------------------------------------------------------------
  EVERYF - true if every mapping satisfies a predicate
----------------------------------------------------------------%


let EVERYF_DEF = new_definition
   (`EVERYF_DEF`,
    "EVERYF P (map:(*,**)fpf) = !x. x IN (DOM map) ==> P (x,RESULTOF(APPLY x map))");;


let EVERYF_ZIP = prove_thm(`EVERYF_ZIP`,
    "!P. EVERYF (P:(*#**)->bool) ZIP = T",
   REWRITE_TAC [EVERYF_DEF;DOM;NOT_IN_EMPTY]);;


%< 
Initially one might think the result should be:
      mk_thm([], "!P (d:*) (r:**) fpf. EVERYF P (EXT (d,r) fpf) = P (d,r) /\ EVERYF P fpf"));;
However, this can't be proven as fpf may contain overridden mappings for x. It was for
this reason that UNEXT was defined above.
 >%

let EVERYF_EXT = prove_thm(`EVERYF_EXT`,
      "!P fpf (d:*) (r:**). EVERYF P (EXT (d,r) fpf) = P (d,r) /\ EVERYF P (UNEXT d fpf)",
   REWRITE_TAC [EVERYF_DEF; DOM; APPLY; IN_INSERT]
   THEN REWRITE_TAC [IN_DOM_EQ_APPLY]
   THEN REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC 
   THENL [
      FIRST_ASSUM (ACCEPT_TAC o REWRITE_RULE [RESULTOF_RESULT] o SPEC "d")
   ;  ASM_REWRITE_TAC [RESULTOF_RESULT] THEN ASM_CASES_TAC "x = d"
      THENL [
         RES_TAC THEN SMART_ELIMINATE_TAC THEN UNDISCH_ALL_TAC 
         THEN REWRITE_TAC [APPLY_UNEXT_SAME;RESULTOF_RESULT; NOT_FAILURE_EQ_RESULT]
      ;  POP_ASSUM (ASSUME_TAC o DEEP_SYM)
         THEN IMP_RES_TAC APPLY_UNEXT_DIFF
         THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
	 THEN SMART_TERM_ELIMINATE_TAC
         THEN RES_TAC
         THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [RESULTOF_RESULT]
      ]
   ;  SMART_ELIMINATE_TAC THEN ASM_REWRITE_TAC [RESULTOF_RESULT]
   ;  COND_CASES_TAC THEN TRY SMART_ELIMINATE_TAC THEN ASM_REWRITE_TAC [RESULTOF_RESULT]    
      THEN IMP_RES_TAC APPLY_UNEXT_DIFF
      THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
      THEN SMART_TERM_ELIMINATE_TAC
      THEN RES_TAC
      THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC  [RESULTOF_RESULT]                         
   ]
);;

         

let EVERYF = save_thm(`EVERYF`, CONJ EVERYF_ZIP EVERYF_EXT);;



%----------------------------------------------------------------
  CANONICAL representations for fpf's
----------------------------------------------------------------%


system `rm fpf_canon.th`;;
new_theory `fpf_canon`;;

let IS_CANONICALa_REP_DEF = new_recursive_definition false list_Axiom `IS_CANONICALa_REP_DEF`
   "(IS_CANONICALa_REP fpf [] = (fpf = ZIP)) /\
    (IS_CANONICALa_REP fpf (CONS (pr:(*#**)) t) =
         (?d. d IN DOM fpf) /\ 
         (pr = (@d. d IN DOM fpf), (RESULTOF(APPLY (FST pr) fpf))) /\ 
         (IS_CANONICALa_REP (UNEXT (FST pr) fpf) t))";;


let IS_CANONICALa_REP_CONS_PAIR = save_thm(`IS_CANONICALa_REP_CONS_PAIR`,
      let thm1 = PURE_ONCE_REWRITE_RULE [DEEP_SYM PAIR] (CONJUNCT2 IS_CANONICALa_REP_DEF) in
      let thm2 = SPECL ["fpf:(*,**)fpf";"(x:*,y:**)"] (REWRITE_RULE [] (PURE_ONCE_REWRITE_RULE [PAIR_EQ] thm1)) in
         REWRITE_RULE [] (GEN_ALL thm2));;


let IS_CANONICALa_REP_ZIP = prove_thm(`IS_CANONICALa_REP_ZIP`,
    "!(l:(*#**)list). IS_CANONICALa_REP ZIP l = (l = [])",
    INDUCT_THEN list_INDUCT MP_TAC
    THENL [
       REWRITE_TAC [REWRITE_RULE [] (SPEC "ZIP:(*,**)fpf" (CONJUNCT1 IS_CANONICALa_REP_DEF))]
     ; REWRITE_TAC [IS_CANONICALa_REP_DEF;APPLY;UNEXT_ZIP;NOT_CONS_NIL;DOM;theorem `sets` `NOT_IN_EMPTY`]
    ]);;


let IS_CANONICALa_REP = prove_thm(`IS_CANONICALa_REP`,
    "!l (fpf:(*,**)fpf). IS_CANONICALa_REP fpf (CONS((@d. d IN (DOM fpf)), RESULTOF(APPLY(@d. d IN DOM fpf)fpf)) l) =
        (?d. d IN DOM fpf) /\ IS_CANONICALa_REP (UNEXT (@d. d IN DOM fpf) fpf) l",
   REWRITE_TAC [IS_CANONICALa_REP_CONS_PAIR]);;

%< To prove the following I think we would need an induction principal down UNEXT operations, i.e. ZIP
is the result of a finte number of UNEXTs.  Tricky..?? :-)

No...we need the induction over the cardinality of the domain methinks...
   REPEAT STRIP_TAC		
   THEN SPEC_TAC ("fpf","fpf")
   THEN MATCH_MP_TAC fpf_CARD_INDUCT

>%


%< a few lemmas which I didn't have time to prove - hope they're not too hard... >%

let CARD_UNEXT_LEQ_SUC = mk_thm([], 
      "!x. x IN DOM (f:(*,**)fpf) ==> (CARD(DOM f)) <= (SUC j) ==> (CARD(DOM (UNEXT x f))) <= j");;


let CHOICE_IN_DOM = mk_thm([],
      "!f:(*,**)fpf.  (f = ZIP) \/ ((@d. d IN DOM f) IN DOM f)");;


let CANONICALa_REP_EXISTS = BETA_RULE (PROVE (
   " !(fpf:(*,**)fpf). (\fpf. ?l. IS_CANONICALa_REP fpf l) fpf",
   MATCH_MP_TAC fpf_CARD_INDUCT
   THEN BETA_TAC THEN REPEAT STRIP_TAC
   THENL [
      EXISTS_TAC "[]:(*#**)list" THEN ASM_REWRITE_TAC[IS_CANONICALa_REP_DEF]
   ;  FIRST_ASSUM (STRIP_ASSUME_TAC 
          o REWRITE_RULE [DEEP_SYM LESS_OR_EQ] 
          o SPEC "UNEXT (@d. d IN DOM f) (f:(*,**)fpf)" 
          o REWRITE_RULE [LESS_OR_EQ] o SPEC "j:num")
      THEN DISJ_CASES_TAC (SPEC "f" CHOICE_IN_DOM)
      THENL [
         EXISTS_TAC "[]:(*#**)list" THEN ASM_REWRITE_TAC[IS_CANONICALa_REP_DEF]     
      ;  IMP_RES_TAC CARD_UNEXT_LEQ_SUC THEN RES_TAC 
         THEN EXISTS_TAC "CONS ((@d. d IN DOM (f:(*,**)fpf)), RESULTOF(APPLY (@d. d IN DOM f) f)) l"
	 THEN ASM_REWRITE_TAC [IS_CANONICALa_REP]
         THEN EXISTS_TAC "@d. d IN (DOM (f:(*,**)fpf))" THEN ASM_REWRITE_TAC []
      ]
   ]
));;



let CONV_ASM_TAC conv =
   POP_ASSUM_LIST (\asms.
      (EVERY (rev (map (STRIP_ASSUME_TAC o CONV_RULE (DEPTH_CONV conv)) asms))));;


let CANONICALa_REP_UNIQUE = prove_thm(`CANONICALa_REP_UNIQUE`,
   " !(fpf:(*,**)fpf). ?!l. IS_CANONICALa_REP fpf l",
   PURE_ONCE_REWRITE_TAC [EXISTS_UNIQUE_DEF]
   THEN BETA_TAC
   THEN REWRITE_TAC [CANONICALa_REP_EXISTS]
   THEN REPEAT GEN_TAC THEN SPEC_TAC("fpf","fpf") 
   THEN SPEC_TAC ("x:(*#**)list","x") THEN SPEC_TAC ("y:(*#**)list","y")
      THEN INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL [ALL_TAC ; GEN_TAC]
      THEN INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THEN REPEAT GEN_TAC
      THEN BETA_TAC THEN REWRITE_TAC [IS_CANONICALa_REP_DEF;NOT_NIL_CONS;NOT_CONS_NIL]
      THEN REPEAT STRIP_TAC
      THEN (TRY (REPEAT SMART_ELIMINATE_TAC 
            THEN FIRST_ASSUM (ACCEPT_TAC o REWRITE_RULE [DOM;NOT_IN_EMPTY])
	    THEN NO_TAC
      )) THEN  CONV_ASM_TAC BETA_CONV THEN UNDISCH_ALL_TAC 
      THEN PURE_ONCE_REWRITE_TAC [DEEP_SYM PAIR]
      THEN PURE_REWRITE_TAC [PAIR_EQ;FST;SND]
      THEN REPEAT STRIP_TAC
      THEN REPEAT SMART_TERM_ELIMINATE_TAC
      THEN RES_TAC THEN SMART_ELIMINATE_TAC THEN REWRITE_TAC []
);;

let CANONICALa_REP_UNIQUENESS = save_thm(`CANONICALa_REP_UNIQUENESS`,
   (BETA_RULE o GEN_ALL o CONJUNCT2 o BETA_RULE) 
   (PURE_ONCE_REWRITE_RULE [EXISTS_UNIQUE_DEF] (SPEC_ALL CANONICALa_REP_UNIQUE)));;


let CANONICALa_REP_DEF = new_definition(`CANONICALa_REP_DEF`,
   "CANONICALa_REP (fpf:(*,**)fpf) = @l. IS_CANONICALa_REP fpf l"
);;

let CANONICALa_ABS_DEF = new_definition(`CANONICALa_ABS_DEF`,
   "CANONICALa_ABS (l:(*#**)list) = @fpf. IS_CANONICALa_REP fpf l"
);;



%< yet another unproved lemma >%

let lemma = mk_thm([],
      "!fpf (fpf':(*,**)fpf).
       (RESULTOF(APPLY(@d. d IN (DOM fpf))fpf') = RESULTOF(APPLY(@d. d IN (DOM fpf))fpf)) /\
       (UNEXT(@d. d IN (DOM fpf))fpf' = UNEXT(@d. d IN (DOM fpf))fpf) ==>
          (fpf = fpf')");;

let CANONICALa_ABS_UNIQUENESS = prove_thm(`CANONICALa_ABS_UNIQUENESS`,
   " !(l:(*#**)list). !fpf fpf'. IS_CANONICALa_REP fpf l /\ IS_CANONICALa_REP fpf' l ==> (fpf = fpf')",
   INDUCT_THEN list_INDUCT MP_TAC
   THEN REWRITE_TAC [IS_CANONICALa_REP_DEF;PAIR_EQ]
   THENL [
      REPEAT STRIP_TAC THEN REPEAT SMART_ELIMINATE_TAC THEN REWRITE_TAC []
    ; STRIP_TAC THEN REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [DEEP_SYM PAIR]
      THEN PURE_REWRITE_TAC [PAIR_EQ;FST;SND]
      THEN REPEAT STRIP_TAC THEN REPEAT SMART_TERM_ELIMINATE_TAC
      THEN RES_TAC THEN IMP_RES_TAC lemma
   ]
);;



%----------------------------------------------------------------
----------------------------------------------------------------%


close_theory();;

