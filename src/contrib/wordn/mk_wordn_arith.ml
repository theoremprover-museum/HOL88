load_library`more_lists`;;

new_theory`wordn_arith`;;

load_library`more_arithmetic`;;

%-----------------------------------------------------------------------%
% general theorems and untilities   					%
%-----------------------------------------------------------------------%

% list functions %
let REV_ITLIST_DEF = new_definition(`REV_ITLIST_DEF`,
    "REV_ITLIST f (l:(*)list) (x:**) = ITLIST f (REVERSE l) x");;

let ITLIST_SNOC = TAC_PROOF(([],
    "!(f:*->**->**) d l x. ITLIST f (SNOC d l) x = ITLIST f l (f d x)"),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[SNOC_DEF;ITLIST] THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);;

let REV_ITLIST = prove_thm(`REV_ITLIST`,
    "(!(f:*->**->**) (x:**). REV_ITLIST f [] x = x) /\
     (!f (hd:*) tl x. REV_ITLIST f (CONS hd tl)x = REV_ITLIST f tl (f hd x)) /\
     (!f l d x. REV_ITLIST f (SNOC d l) x = f d (REV_ITLIST f l x))",
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    PURE_REWRITE_TAC[REV_ITLIST_DEF;REVERSE_CLAUSES;ITLIST]
    THEN PURE_ONCE_REWRITE_TAC[ITLIST_SNOC] THEN REFL_TAC);;

let SNOC_LENGTH = TAC_PROOF(([], "!l d. LENGTH (SNOC d l) = SUC(LENGTH l)"),
    REPEAT GEN_TAC THEN PURE_REWRITE_TAC[SNOC_APPEND_CONS;LENGTH_APPEND;LENGTH]
    THEN REWRITE_TAC[ADD_CLAUSES]);;

%-------------%

"!n l. (REV_ITLIST (\b v. b=>SUC(2*v)|(2*v)) l 0 = n) ==>
(REV_ITLIST (\b v. b=>SUC(2*v)|(2*v)) l (SUC 0) = (2 EXP (LENGTH l)) + n)"
    GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	PURE_REWRITE_TAC[REV_ITLIST;LENGTH;EXP;ADD_CLAUSES]
    	THEN DISCH_THEN (\t. SUBST1_TAC(SYM t))
    	THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN REWRITE_TAC[ADD_0];
    	PURE_REWRITE_TAC[REV_ITLIST;LENGTH;EXP] THEN BETA_TAC
    	THEN GEN_TAC THEN COND_CASES_TAC THENL[
    	    PURE_REWRITE_TAC[COND_CLAUSES] 

"!l. B_VAL l = VAL l"
    PURE_ONCE_REWRITE_TAC[B_VAL_DEF] THEN LIST_INDUCT_TAC THEN
    PURE_REWRITE_TAC[VAL;REV_ITLIST] THENL[ REFL_TAC;
    	GEN_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    	PURE_REWRITE_TAC[ADD_CLAUSES;BV;MULT;COND_CLAUSES] THENL[
    	    STRIP_ASSUME_TAC (ISPEC "l:(bool)list" SNOC_CASES))
    	    THEN POP_ASSUM SUBST1_TAC THENL[
    	    PURE_REWRITE_TAC[REV_ITLIST;LENGTH;VAL;ADD_CLAUSES;EXP]
    	    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REFL_TAC;

    	    FIRST_ASSUM ACCEPT_TAC

% division and even/odd numbers %

let DBL_EQ = TAC_PROOF(([], "!m n. ((m + m) = (n + n)) = (m = n)"),
    let dbl_lemma = (PURE_ONCE_REWRITE_RULE[EQ_SYM_EQ] TIMES2) in
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[dbl_lemma]
    THEN CONV_TAC (DEPTH_CONV num_CONV)
    THEN PURE_ONCE_REWRITE_TAC[MULT_MONO_EQ] THEN REFL_TAC);;

let DBL_LESS = TAC_PROOF(([], "!m n. ((m + m) < (n + n)) = (m < n)"),
    let dbl_lemma = (PURE_ONCE_REWRITE_RULE[EQ_SYM_EQ] TIMES2) in
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[dbl_lemma]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN MATCH_ACCEPT_TAC LESS_MULT_MONO);;

%<let SUC_DIV_EQ = TAC_PROOF(([],
    "!m n. (0 < n) ==> (((SUC m) DIV (SUC n)) = (m DIV n))"),
    REPEAT INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0];
    	PURE_ONCE_REWRITE_TAC[LESS_THM] THEN STRIP_TAC
    	THEN SUBST1_TAC (SPEC_ZERO_DIV "SUC n")
    	THEN MATCH_MP_TAC DIV_UNIQUE
    	THEN PURE_REWRITE_TAC[MULT;ADD_CLAUSES]
    	THEN EXISTS_TAC "SUC n"
    	THEN ASM_REWRITE_TAC[LESS_SUC_REFL;LESS_MONO_EQ;LESS_0];
    	REWRITE_TAC[NOT_LESS_0];
>%

let ZERO_DIV = TAC_PROOF(([], "!n. 0 < n ==> ((0 DIV n) = 0)"),
    INDUCT_TAC THENL[
        REWRITE_TAC[NOT_LESS_0];
    	DISCH_TAC THEN IMP_RES_THEN (\t. ASSUME_TAC (SPEC "0" t)) DIV_LESS_EQ
    	THEN IMP_RES_TAC LESS_EQ_0_EQ]);;

let SPEC_ZERO_DIV tm = 
    if (is_const tm) then 
    	(let th = num_CONV tm in
    	 let N,Suc,N' = (I # dest_comb) (dest_eq(concl th)) in
    	 (MP (SPEC N ZERO_DIV) (SUBS[(SYM th)] (SPEC N' LESS_0))))
    else 
    	let Suc,N' = dest_comb tm in
    	(MP (SPEC tm ZERO_DIV) (SPEC N' LESS_0)) ;;

let DIV_EQ_ZERO = TAC_PROOF(([],
    "!m n. (0 < n) /\ (m < n) ==> ((m DIV n) = 0)"),
    REPEAT INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0];
    	STRIP_TAC THEN ACCEPT_TAC (SPEC_ZERO_DIV "SUC n");
    	REWRITE_TAC[NOT_LESS_0];
    	STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQUE
    	THEN PURE_REWRITE_TAC[MULT;ADD_CLAUSES]
    	THEN EXISTS_TAC "SUC m" THEN ASM_REWRITE_TAC[]]);;

let EVEN_ODD = TAC_PROOF(([],
    "!n. (EVEN_NUM n ==> ~ODD_NUM n) /\ (ODD_NUM n ==> ~EVEN_NUM n)"),
    GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE[DE_MORGAN_THM]
    	(SPEC_ALL NUM_NOT_EVEN_AND_ODD)) THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE RES_TAC));;

let EVEN_DOUBLE = TAC_PROOF(([], "!n. EVEN_NUM(n + n)"),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[EVEN_NUM]
    THEN EXISTS_TAC "n:num" THEN REWRITE_TAC[TIMES2]);;

let MULT_DIV_2 = TAC_PROOF(([], "!n. (2 * n) DIV 2 = n"),
    GEN_TAC THEN MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC "0"
    THEN CONJ_TAC THENL[
    	PURE_REWRITE_TAC[ADD_CLAUSES;LESS_0]
    	THEN MATCH_ACCEPT_TAC MULT_SYM;
    	CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN MATCH_ACCEPT_TAC LESS_0]);;

% "!n. (n + n) DIV 2 = n" %
let DOUBLE_DIV_2 = PURE_ONCE_REWRITE_RULE[TIMES2] MULT_DIV_2;;

let SUC_DOUBLE_DIV_2 = TAC_PROOF(([],
    "!n. (((SUC (n + n)) DIV 2) = ((n + n) DIV 2))"),
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[DOUBLE_DIV_2]
    THEN MATCH_MP_TAC DIV_UNIQUE THENL[
    	PURE_REWRITE_TAC[MULT;ADD_CLAUSES]
    	THEN EXISTS_TAC "SUC 0" THEN CONV_TAC (REDEPTH_CONV num_CONV)
        	THEN REWRITE_TAC[LESS_MONO_EQ;LESS_0];
    	PURE_ONCE_REWRITE_TAC[(CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) TIMES2)]
    	THEN EXISTS_TAC "1"
    	THEN PURE_ONCE_REWRITE_TAC[(CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) ADD1)]
    	THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] THEN CONJ_TAC THENL[
    	    MATCH_ACCEPT_TAC MULT_SYM;
    	    CONV_TAC (REDEPTH_CONV num_CONV)
    	    THEN REWRITE_TAC[LESS_MONO_EQ;LESS_0]]]);;

%<
let SUC_SUC_HALF_SUC = TAC_PROOF(([],
    "!n. (SUC(SUC n) DIV 2) = SUC (n DIV 2)"),
    INDUCT_TAC THENL[
    	PURE_ONCE_REWRITE_TAC[SPEC_ZERO_DIV "2"]
    	THEN MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC "0"
    	THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
    	THEN PURE_REWRITE_TAC[TIMES2;ADD_CLAUSES] THEN CONJ_TAC
    	THENL[ REFL_TAC;
    	    CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0];
    	MATCH_MP_TAC DIV_UNIQUE THEN PURE_ONCE_REWRITE_TAC[MULT]
>%

let EVEN_SUC_HALF_EQ = TAC_PROOF(([],
    "!n. EVEN_NUM n ==> (((SUC n) DIV 2) = (n DIV 2))"),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[EVEN_NUM]
    THEN PURE_ONCE_REWRITE_TAC[TIMES2] THEN STRIP_TAC
    THEN PURE_ONCE_ASM_REWRITE_TAC[]
    THEN MATCH_ACCEPT_TAC SUC_DOUBLE_DIV_2);;

let ODD_SUC_HALF_SUC = TAC_PROOF(([],
    "!n. ODD_NUM n ==> (((SUC n) DIV 2) = SUC(n DIV 2))"),
    let [_;_;a1;a2] = CONJUNCTS ADD_CLAUSES in
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[ODD_NUM]
    THEN PURE_ONCE_REWRITE_TAC[TIMES2] THEN STRIP_TAC
    THEN POP_ASSUM SUBST1_TAC THEN PURE_ONCE_REWRITE_TAC[SUC_DOUBLE_DIV_2]
    THEN PURE_ONCE_REWRITE_TAC[DOUBLE_DIV_2]
    THEN MATCH_MP_TAC DIV_UNIQUE
    THEN MAP_EVERY (\t.PURE_ONCE_REWRITE_TAC[SYM t])[a1;a2]
    THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC[TIMES2] THEN EXISTS_TAC "0"
    THEN REWRITE_TAC[ADD_0] THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN MATCH_ACCEPT_TAC LESS_0);;

%-----------------------------------------------------------------------%
% B_VAL : (bool)list -> num 	    					%
% converts a bit vector to a num. The bit vector is interpreted as a	%
% unsigned integer in big-endian format.				%
%-----------------------------------------------------------------------%

let B_VAL_DEF = new_definition(`B_VAL_DEF`,
    "B_VAL (l:(bool)list) = REV_ITLIST (\b v. (b => SUC(v+v) | (v+v))) l 0");;

let B_VAL_NIL = TAC_PROOF(([], "B_VAL[] = 0"),
    PURE_REWRITE_TAC[B_VAL_DEF;REV_ITLIST] THEN REFL_TAC);;

let B_VAL_SNOC = TAC_PROOF(([], "!l d. B_VAL (SNOC d l) = 
    (d => SUC((B_VAL l)+(B_VAL l)) | (B_VAL l + B_VAL l))"),
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[B_VAL_DEF]
    THEN PURE_ONCE_REWRITE_TAC[REV_ITLIST] THEN COND_CASES_TAC
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN PURE_ONCE_REWRITE_TAC[COND_CLAUSES] THEN REFL_TAC);;

let B_VAL = save_thm(`B_VAL`, CONJ B_VAL_NIL B_VAL_SNOC);;

let B_VAL_11 = prove_thm(`B_VAL_11`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (B_VAL l1 = B_VAL l2) ==> (l1 = l2)",
    let lemma = TAC_PROOF(([],
    	"!l (d:*). ~(LENGTH([]:(*)list) = LENGTH(SNOC d l))"),
        REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_CLAUSES]
    	THEN MATCH_ACCEPT_TAC SUC_NOT) in
    SNOC_INDUCT_TAC THENL[
      SNOC_INDUCT_TAC THEN REPEAT STRIP_TAC THENL[
    	REFL_TAC; IMP_RES_TAC lemma];
      GEN_TAC THEN SNOC_INDUCT_TAC THENL[
    	REPEAT STRIP_TAC THEN IMP_RES_TAC
    	  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) lemma);
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_CLAUSES]
    	THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] THEN DISCH_TAC
    	THEN PURE_ONCE_REWRITE_TAC[SNOC_11]
    	THEN PURE_ONCE_REWRITE_TAC[B_VAL_SNOC]
    	THEN REPEAT COND_CASES_TAC THENL[
    	  PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] 
    	  THEN PURE_ONCE_REWRITE_TAC[DBL_EQ]
    	  THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[];
    	  DISCH_TAC THEN IMP_RES_TAC NOT_ODD_EQ_EVEN;
    	  CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
    	  THEN DISCH_TAC THEN IMP_RES_TAC NOT_ODD_EQ_EVEN;
    	  PURE_ONCE_REWRITE_TAC[dbl_eq]
    	  THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]]);;

let B_VAL_onto = prove_thm(`B_VAL_onto`, "!l. ?n. (B_VAL l) = n",
    SNOC_INDUCT_TAC THENL[
    	EXISTS_TAC "0" THEN ACCEPT_TAC B_VAL_NIL;
        PURE_ONCE_REWRITE_TAC[B_VAL_SNOC]
    	THEN POP_ASSUM (X_CHOOSE_THEN "m:num" SUBST1_TAC)
    	THEN GEN_TAC THEN COND_CASES_TAC THENL[
    	    EXISTS_TAC "SUC(m+m)";EXISTS_TAC "(m+m)"]
    	THEN REFL_TAC]);;

%<
let VAL3_DEF = new_wordn_definition false word3_FNDEF `VAL3_DEF`
    "VAL3 (WORD3 [b0; b1; b2]) = B_VAL [b0; b1; b2]";;
>%

let prove_VAL_one_one n =
    let nstr = string_ot_int n in
    let bl = (mk_bit_list `b` n ``) and bl' = (mk_bit_list `b` n `'`) in
    let l = mk_list(bl, ":bool") and l' = mk_list(bl', ":bool") in
    let wdty = mk_type((`word`^nstr), []) in
    let Wn = mk_const((`WORD`^nstr), ":(bool)list -> ^wdty") in
    let dth = definition `-` (`VAL`^nstr^`_DEF`) in
    let th2 = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) dth in
    let th3 = SUBS (map (\t. SPECL t th2) [bl; bl']) (SPECL [l; l'] B_VAL_11) in
    let bth = theorem `-` (`word`^nstr^`_BITS_11`) in
    let cth = theorem `-` (`word`^nstr^`_CASES`) in
    let wl = mk_comb(Wn,l) and wl' = mk_comb(Wn, l') in
    let th4 = SPECL [wl';wl] bth in
    let bwth = theorem `-` (`word`^nstr^`_BITS_WORD`) ?
    	prove_BITS_WORD (definition `-` (`word`^nstr)) in
    let th6 = SUBS (map (\t. SPECL t bwth) [bl; bl']) th4 in
    let Vn = mk_const((`VAL`^nstr), ":^wdty -> num") in
    let veq = mk_eq(mk_comb(Vn, wl), mk_comb(Vn, wl')) in
    let th8 = DISCH veq (MP th6 (UNDISCH (UNDISCH th3))) in
    let lth = TRANS (LENGTH_CONV l) (SYM (LENGTH_CONV l')) in
    let th9 = PROVE_HYP lth th8 in
    TAC_PROOF(([], "!w1 w2. (^Vn w1 = ^Vn w2) ==> (w1 = w2)"),
    REPEAT GEN_TAC THEN MAP_EVERY (\t.wordn_CASES_TAC t cth)["w1";"w2"]
    THEN ACCEPT_TAC th9);;


let prove_VAL_onto n =
    let nstr = string_of_int n in
    let dth = definition `-` (`VAL`^nstr^`_DEF`) in
    let cth = theorem `-` (`word`^nstr^`_CASES`) in
    let wdty = mk_type((`word`^nstr), []) in
    let Vn = mk_const((`VAL`^nstr), ":^wdty -> num") in
    TAC_PROOF(([], "!w. ?n. ^Vn w = n"),
    GEN_TAC THEN wordn_CASES_TAC "w" cth
    THEN PURE_ONCE_REWRITE_TAC[dth] THEN MATCH_ACCEPT_TAC B_VAL_onto);;



%-----------------------------------------------------------------------%
% B_MAX : num -> num 	    	    					%
% returns a number which is one plus the maximium an n-bit word can	%
% represent when it is interpreted as an unsigned integer.		%
%-----------------------------------------------------------------------%

let B_MAX_DEF = new_prim_rec_definition(`B_MAX_DEF`,
    "(B_MAX 0 = 1) /\
     (B_MAX (SUC n) =  (B_MAX n) * 2)");;

%-----------------------------------------------------------------------%
% B_LIST : num -> num -> (bool)list    					%
% (B_LIST n m)converts the natural number m to a bit vector of length n %
%-----------------------------------------------------------------------%

let B_LIST_DEF = new_prim_rec_definition(`B_LIST_DEF`,
    "(B_LIST 0 m = []) /\
     (B_LIST (SUC n) m =  SNOC (ODD_NUM m) (B_LIST n (m DIV 2)) )");;

let B_LIST = prove_thm(`B_LIST`,
    "(!m. B_LIST 0 m = []) /\
     (!n. B_LIST (SUC n) 0 = SNOC F (B_LIST n 0)) /\
     (!n m. B_LIST (SUC n) (SUC m) = (EVEN_NUM m) =>
    	(SNOC T (B_LIST n ((SUC m) DIV 2))) |
     	(SNOC F (B_LIST n ((SUC m) DIV 2))))",
    REPEAT CONJ_TAC THENL[
      MATCH_ACCEPT_TAC (CONJUNCT1 B_LIST_DEF);
      INDUCT_TAC THENL[
    	PURE_REWRITE_TAC[B_LIST_DEF;EVEN_ODD_0] THEN REFL_TAC;
    	PURE_ONCE_REWRITE_TAC[B_LIST_DEF]
    	THEN ASM_REWRITE_TAC[(SPEC_ZERO_DIV "2");EVEN_ODD_0]];
      REPEAT INDUCT_TAC THENL[
    	PURE_REWRITE_TAC[B_LIST_DEF;EVEN_ODD_0;COND_CLAUSES;NUM_EVEN_ODD_SUC]
    	THEN REFL_TAC;
    	PURE_REWRITE_TAC[B_LIST_DEF;COND_CLAUSES;NUM_EVEN_ODD_SUC]
    	THEN COND_CASES_TAC THEN REFL_TAC;
       	let lem = 
    	    let th1 = (SPEC "1" LESS_0) in
    	    let th2 = EQ_MP (SYM (SPECL["0";"1"] LESS_MONO_EQ))
    	    	(SUBS [(SYM(num_CONV "1"))](SPEC "0"LESS_0)) in
    	    (MP (SPECL ["SUC 0";"SUC 1"]DIV_EQ_ZERO) (CONJ th1 th2)) in
    	(PURE_REWRITE_TAC[B_LIST_DEF;COND_CLAUSES;EVEN_ODD_0;NUM_EVEN_ODD_SUC;
    	    (SPEC_ZERO_DIV "2")]
    	THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN SUBST1_TAC lem THEN SUBST1_TAC (SPEC_ZERO_DIV "SUC 1")
    	THEN REFL_TAC);
    	PURE_ONCE_REWRITE_TAC[B_LIST_DEF] THEN COND_CASES_TAC
    	THEN PURE_ASM_REWRITE_TAC[SNOC_11;NUM_EVEN_ODD_SUC]
    	THEN REWRITE_TAC[B_LIST_DEF]]]);;

let B_LIST_LENGTH = prove_thm(`B_LIST_LENGTH`,
    "!n m. LENGTH(B_LIST n m) = n",
    INDUCT_TAC THENL[
    	REWRITE_TAC[B_LIST;LENGTH];
    	PURE_ONCE_REWRITE_TAC[B_LIST_DEF]
    	THEN PURE_ONCE_REWRITE_TAC[SNOC_LENGTH]
    	THEN GEN_TAC THEN ASM_REWRITE_TAC[]]);;

let B_LIST_NOT_NULL = prove_thm(`B_LIST_NOT_NULL`,
    "!n m. (0 < n) ==> ~NULL(B_LIST n m)",
    INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0];
    	INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[B_LIST]
    	THEN DISCH_TAC THEN (COND_CASES_TAC ORELSE ALL_TAC)
    	THEN MATCH_ACCEPT_TAC SNOC_NOT_NULL]);;


let B_LIST_onto = prove_thm(`B_LIST_onto`,
    "!m n. ?l. B_LIST n m = l",
    REPEAT INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[B_LIST_DEF] THENL[
      EXISTS_TAC "[]:(bool)list" THEN REFL_TAC;
      let lem = MP (CONV_RULE (ONCE_DEPTH_CONV num_CONV) (SPEC "2" ZERO_DIV))
    	 (SPEC "1" LESS_0) in
      CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN SUBST1_TAC lem THEN POP_ASSUM (CHOOSE_THEN SUBST1_TAC)
      THEN EXISTS_TAC "SNOC F (l:(bool)list)" THEN REWRITE_TAC[EVEN_ODD_0];
      EXISTS_TAC "[]:(bool)list" THEN REFL_TAC;
      STRIP_ASSUME_TAC (SPEC "SUC m" NUM_EVEN_OR_ODD)
      THEN IMP_RES_TAC EVEN_ODD THEN PURE_ASM_REWRITE_TAC[] THENL[
    	EXISTS_TAC "SNOC F (B_LIST n ((SUC m)DIV 2))";
    	EXISTS_TAC "SNOC T (B_LIST n ((SUC m)DIV 2))"] THEN REFL_TAC]);;


let ZERO_B_LIST = prove_thm(`ZERO_B_LIST`,
    "!n k. (k < n) ==> (EL k (B_LIST n 0) = F)",
    let lem = ISPECL["F"; "[]:(bool)list"](CONJUNCT2 NULL) in
    let lem' = TAC_PROOF(([], "!k m n. (k < n) /\ (m = n) ==> (k < m)"),
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]) in
    INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0];
    	PURE_ONCE_REWRITE_TAC[LESS_THM] THEN GEN_TAC THEN STRIP_TAC 
    	THEN PURE_ONCE_REWRITE_TAC[B_LIST]
    	THEN ASSUME_TAC (SPEC "0" (SPEC "n" B_LIST_LENGTH)) THENL[
    	    PURE_ONCE_REWRITE_TAC[SNOC_APPEND_CONS]
    	    THEN PURE_ONCE_ASM_REWRITE_TAC[]
    	    THEN POP_ASSUM (\t. SUBST_OCCS_TAC [[1],(SYM t)])
    	    THEN ASSUME_TAC lem THEN IMP_RES_TAC EL_LENGTH_APPEND
    	    THEN POP_ASSUM (\t. PURE_ONCE_REWRITE_TAC[t])
    	    THEN REWRITE_TAC[HD];
    	    MAP_EVERY IMP_RES_TAC [lem';EL_SNOC] THEN RES_TAC
    	    THEN ASM_REWRITE_TAC[]]]);;

let NUM_CASES = TAC_PROOF(([],"!n. (n = 0) \/ (0 < n)"),
    INDUCT_TAC THENL[
    	DISJ1_TAC THEN REFL_TAC;
    	DISJ2_TAC THEN MATCH_ACCEPT_TAC LESS_0]);;

let B_MAX_GREATER_0 = TAC_PROOF(([], "!n. 0 < (B_MAX n)"),
    INDUCT_TAC THEN PURE_REWRITE_TAC[B_MAX_DEF] THENL[
    	CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
    	PURE_ONCE_REWRITE_TAC[MULT_SYM]
    	THEN PURE_ONCE_REWRITE_TAC[TIMES2]
    	THEN IMP_RES_TAC LESS_IMP_LESS_ADD
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let lem2 = TAC_PROOF(([],
    "!m n. (ODD_NUM m) ==> ((SUC m) < (n * 2)) ==> (SUC(m DIV 2) < n)"),
    let [_;_;a1;a2] = CONJUNCTS ADD_CLAUSES in
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[ODD_NUM]
    THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN PURE_REWRITE_TAC[TIMES2;SUC_DOUBLE_DIV_2;DOUBLE_DIV_2]
    THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
    THEN MAP_EVERY (\t.PURE_ONCE_REWRITE_TAC[SYM t])[a1;a2]
    THEN PURE_ONCE_REWRITE_TAC[TIMES2]
    THEN PURE_ONCE_REWRITE_TAC[DBL_LESS]
    THEN DISCH_THEN ACCEPT_TAC);;

let SUC_B_LIST = prove_thm(`SUC_B_LIST`,
    "!n. (0 < n) ==> !m. ((SUC m) < B_MAX n) ==>
     ?k. (k < n) /\ ~(EL k (B_LIST n (SUC m)) = F)",
    let lem = ISPECL["T"; "[]:(bool)list"](CONJUNCT2 NULL) in
    let lem' = TAC_PROOF(([], "!k m n. (k < n) /\ (m = n) ==> (k < m)"),
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]) in
    let MULT_LEFT_1 = theorem `arithmetic` `MULT_LEFT_1` in
    INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0];
      DISCH_TAC THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[B_LIST;B_MAX_DEF]
      THEN COND_CASES_TAC THENL[
    	DISCH_TAC THEN EXISTS_TAC "n" THEN REWRITE_TAC[LESS_SUC_REFL]
    	THEN SUBST_OCCS_TAC [[1],
    	    (SYM (SPEC "(SUC m) DIV 2" (SPEC "n" B_LIST_LENGTH)))]
    	THEN PURE_ONCE_REWRITE_TAC[SNOC_APPEND_CONS]
    	THEN ASSUME_TAC lem THEN IMP_RES_TAC EL_LENGTH_APPEND
    	THEN POP_ASSUM (\t. PURE_ONCE_REWRITE_TAC[t])
    	THEN REWRITE_TAC[HD];
    	STRIP_ASSUME_TAC (SPEC_ALL NUM_CASES) THENL[
    	  POP_ASSUM SUBST1_TAC THEN IMP_RES_TAC NUM_NOT_EVEN_NOT_ODD
    	  THEN POP_ASSUM MP_TAC THEN PURE_ONCE_REWRITE_TAC[ODD_NUM]
    	  THEN STRIP_TAC THEN POP_ASSUM (\t.SUBST_OCCS_TAC[[1],t])
    	  THEN PURE_ONCE_REWRITE_TAC[B_MAX_DEF]
    	  THEN PURE_ONCE_REWRITE_TAC[MULT_LEFT_1]
    	  THEN CONV_TAC (REDEPTH_CONV num_CONV)
    	  THEN PURE_REWRITE_TAC[LESS_MONO_EQ] THEN REWRITE_TAC[NOT_LESS_0];
    	  DISCH_TAC THEN MAP_EVERY IMP_RES_TAC [NUM_NOT_EVEN_NOT_ODD;lem2]
    	  THEN RES_TAC THEN EXISTS_TAC "k" THEN CONJ_TAC THENL[
    	    IMP_RES_TAC LESS_SUC;
    	    UNDISCH_TAC "k<n" THEN SUBST_OCCS_TAC [[1],
    	    	(SYM(SPECL["n";"(SUC m)DIV 2"] B_LIST_LENGTH))]
    	    THEN DISCH_TAC
    	    THEN IMP_RES_THEN (\t.PURE_ONCE_REWRITE_TAC[t]) EL_SNOC
    	    THEN IMP_RES_THEN SUBST1_TAC ODD_SUC_HALF_SUC
    	    THEN FIRST_ASSUM ACCEPT_TAC]]]]);;


"!n m. (0 < n) => (SUC m) < (B_MAX n) ==> ~(B_LIST n 0 = B_LIST n (SUC m))"
    	

"!n m m'. (m < B_MAX n) /\ (m' < B_MAX n) ==>
 ((B_LIST n m) = (B_LIST n m')) ==> (m = m')"
    INDUCT_TAC THENL[
    	REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[B_MAX_DEF]
    	THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN PURE_ONCE_REWRITE_TAC[LESS_THM]
    	THEN PURE_REWRITE_TAC[NOT_LESS_0;OR_CLAUSES]
    	THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT INDUCT_TAC THENL[
    	REPEAT DISCH_TAC THEN REFL_TAC;
    	STRIP_TAC THEN IMP_RES_TAC SUC_LESS THEN RES_TAC
    	THEN PURE_REWRITE_TAC[SUC_NOT;IMP_CLAUSES]
    	THEN PURE_REWRITE_TAC[B_LIST] THEN COND_CASES_TAC THENL[
    	  REWRITE_TAC[SNOC_11];
    	  REWRITE_TAC[SNOC_11] THEN 

      PURE_ONCE_REWRITE_TAC[B_MAX_DEF] THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_EQ] THEN REWRITE_TAC[NOT_LESS_0];
    	PURE_ONCE_REWRITE_TAC[B_MAX_DEF]

%<
let NWORD3_DEF = new_definition(`NWORD3_DEF`,
    "NWORD3 m = WORD3(B_LIST 3 m)");;

g "VAL3 #110 = 6";;
    CONV_TAC (ONCE_DEPTH_CONV wordn_CONV) THEN
    PURE_ONCE_REWRITE_TAC[VAL3_DEF] THEN PURE_ONCE_REWRITE_TAC[B_VAL_DEF]



    \tm. (let val,w = dest_comb tm in
    	  let (hash.bits),ty  = (explode # I) (dest_const val) in
          if (not (hash = `#`)) then fail else

"!n. ODD_NUM  n ==> ~(((SUC n) DIV 2) = 0)"
    INDUCT_TAC THENL[
    	REWRITE_TAC [EVEN_ODD_0];
    	REWRITE_TAC [ODD_NUM];
>%

let B_LIST_B_VAL = TAC_PROOF(([],
    "!l. (B_LIST (LENGTH l) (B_VAL l)) = l"),
    let lem = GEN_ALL(MATCH_MP (GEN_ALL(CONJUNCT1 (SPEC_ALL  EVEN_ODD)))
    	     (SPEC_ALL EVEN_DOUBLE)) in
    SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;B_LIST];
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[SNOC_LENGTH]
    	THEN PURE_ONCE_REWRITE_TAC[B_VAL_SNOC]
    	THEN COND_CASES_TAC THENL[
    	    PURE_ONCE_REWRITE_TAC[B_LIST]
    	    THEN PURE_REWRITE_TAC[EVEN_DOUBLE;COND_CLAUSES]
    	    THEN PURE_ONCE_REWRITE_TAC[SUC_DOUBLE_DIV_2]
    	    THEN PURE_ONCE_REWRITE_TAC[DOUBLE_DIV_2]
    	    THEN ASM_REWRITE_TAC[];
    	    PURE_ONCE_REWRITE_TAC[B_LIST_DEF]
    	    THEN ASM_REWRITE_TAC[lem;DOUBLE_DIV_2]]]);;

"!n m. (m < B_MAX n) ==> (B_VAL (B_LIST n m) = m)"