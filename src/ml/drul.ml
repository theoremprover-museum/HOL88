%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        drul.ml                                               %
%                                                                             %
%     DESCRIPTION:      This file contains what used to be in drul.ml and     %
%                       pplemmas.ml                                           %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml, hol-drule.ml                             %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% Also depends on hol-rule.ml, and hol-drule.ml				%
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`;
		    loadf `ml/hol-rule`;
		    loadf `ml/hol-drule`);;

%
Generalise a theorem over all variables free in conclusion but not in hyps

         A |- t[x1,...,xn]
    ----------------------------
     A |- !x1...xn.t[x1,...,xn]
%

let GEN_ALL th =
    itlist GEN (subtract (frees(concl th)) (freesl (hyp th))) th;;


%
Discharge all hypotheses 

      A, t1, ... , tn |- t
-------------------------------
 A  |- t1 ==> ... ==> tn ==> t


You can write a simpler version using "itlist DISCH (hyp th) th", but this
may discharge two equivalent (alpha-convertible) assumptions.
%

letrec DISCH_ALL th =  DISCH_ALL (DISCH (hd (hyp th)) th)  ?  th;;

%  |- !x. t    ---->    x', |- t[x'/x]		%

let SPEC_VAR th =
    let bv,() = dest_forall (concl th) in
    let bv' = variant (freesl (hyp th)) bv  in   
    bv', SPEC bv' th;;



%
      A |- t1 ==> ... ==> tn ==> t
    -------------------------------
	 A, t1, ..., tn |- t
%

letrec UNDISCH_ALL th =
    if is_imp (concl th)  then  UNDISCH_ALL (UNDISCH th)
    else th;;

% --------------------------------------------------------------------- %
% SPEC_ALL : thm -> thm							%
%									%
%     A |- !x1 ... xn. t[xi]						%
%    ------------------------   where the xi' are distinct 		%
%        A |- t[xi'/xi]		and not free in the input theorem	%
%									%
% BUGFIX: added the "distinct" part and code to make the xi's not free  %
% in the conclusion !x1...xn.t[xi].		        [TFM 90.10.04]	%
%									%
% OLD CODE:								%
% 									%
% let SPEC_ALL th =							%
%     let vars,() = strip_forall(concl th) in				%
%     SPECL (map (variant (freesl (hyp th))) vars) th;;			%
% --------------------------------------------------------------------- %

let SPEC_ALL =
    let f v (vs,l) = let v' = variant vs v in (v'.vs,v'.l) in
    \th. let hvs,con = (freesl # I) (dest_thm th) in
         let fvs = frees con and vars = fst(strip_forall con) in
         SPECL (snd(itlist f vars (hvs @ fvs,[]))) th;;


%
Use the conclusion of ath to delete a hypothesis of bth

    A |- t1 	B, t1 |- t2
    -----------------------
         A u B |- t2
%

let PROVE_HYP ath bth =  MP (DISCH (concl ath) bth) ath;;


% --------------------------------------------------------------------- %
% A |- t1/\t2  ---> A |- t1, A |- t2 					%
% New failure string added.				[TFM 90.05.06]	%
% --------------------------------------------------------------------- %

let CONJ_PAIR th = 
    (CONJUNCT1 th, CONJUNCT2 th) ? 
     failwith `CONJ_PAIR: input thm not a conjunction`;;

% ["A1|-t1"; ...; "An|-tn"]  ---> "A1u...uAn|-t1 /\ ... /\ tn", where n>0   %

let LIST_CONJ = end_itlist CONJ ;;

%
"A |- t1 /\ (...(... /\ tn)...)"   --->  [ "A|-t1"; ...; "A|-tn"],  where n>0 

Inverse of LIST_CONJ : flattens only right conjuncts.
You must specify n, since tn could itself be a conjunction
%

letrec CONJ_LIST n th =
    if n=1 then [th]
    else 
    CONJUNCT1 th . (CONJ_LIST (n-1) (CONJUNCT2 th)) 
    ? failwith `CONJ_LIST`;;

% --------------------------------------------------------------------- %
% CONJUNCTS:								%
%									%
%   "A |- t1 /\ ... /\ tn"  --->  [ "A|-t1"; ...; "A|-tn"],  where n>0	%
%									%
% Flattens out all conjuncts, regardless of grouping			%
% --------------------------------------------------------------------- %

letrec CONJUNCTS th = 
      (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS(CONJUNCT2 th)) ? [th];;

%
"|- !x. (t1 /\ ...) /\ ... (!y. ... /\ tn)" 
   --->  [ "|-t1"; ...; "|-tn"],  where n>0 

Flattens out conjuncts even in bodies of forall's
%

letrec BODY_CONJUNCTS th =
    if is_forall (concl th)  then  BODY_CONJUNCTS (SPEC_ALL th)
    if is_conj (concl th) then
    	BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
    else [th];;

% --------------------------------------------------------------------- %
% IMP_CANON Puts a theorem 						%
%									%
%	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			%
%									%
% into canonical form by stripping out quantifiers and splitting	%
% conjunctions apart.							%
%									%
%	t1 /\ t2	--->		t1,   t2			%
%	(t1/\t2)==>t	--->		t1==> (t2==>t)			%
%	(t1\/t2)==>t	--->		t1==>t, t2==>t			%
%	(?x.t1)==>t2	--->		t1[x'/x] ==> t2			%
%	!x.t1		--->		t1[x'/x]			%
%       (?x.t1)==>t2    --->            t1[x'/x] ==> t2)		%
%									%
% --------------------------------------------------------------------- %

letrec IMP_CANON th =
    let w = concl th in
    if is_conj w then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th)
    else if is_imp w then
	let ante,conc = dest_neg_imp w in
	if is_conj ante then
	    let a,b = dest_conj ante in
	    IMP_CANON 
	    (DISCH a (DISCH b (NOT_MP th (CONJ (ASSUME a) (ASSUME b)))))
	else if is_disj ante then
	    let a,b = dest_disj ante in
	    IMP_CANON (DISCH a (NOT_MP th (DISJ1 (ASSUME a) b))) @
	    IMP_CANON (DISCH b (NOT_MP th (DISJ2 a (ASSUME b))))
	else if is_exists ante then
	    let x,body = dest_exists ante in
	    let x' = variant (thm_frees th) x in
	    let body' = subst [x',x] body in
	    IMP_CANON 
	    (DISCH body' (NOT_MP th (EXISTS (ante, x') (ASSUME body'))))
	else
	map (DISCH ante) (IMP_CANON (UNDISCH th))
    else if is_forall w then
	IMP_CANON (SPEC_ALL th)
    else [th];;							


%

 A1 |- t1   ...   An |- tn      A |- t1==>...==>tn==>t
 -----------------------------------------------------
            A u A1 u ... u An |- t
%

let LIST_MP  = rev_itlist (\x y.MP y x) ;;

%
      A |-t1 ==> t2
    -----------------
    A |-  ~t2 ==> ~t1

(Rewritten by MJCG to return "~t2 ==> ~t1" rather than "~t2 ==> t1 ==>F")
%

let CONTRAPOS impth =
 (let a,b = dest_imp (concl impth) 
  in
  let notb = "~ ^b" 
  in
  DISCH
   notb
   (EQ_MP
    (el 5 (CONJUNCTS (SPEC a IMP_CLAUSES)))
    (DISCH a (NOT_MP (ASSUME notb) (MP impth (ASSUME a)))))
 ) ? failwith `CONTRAPOS`;;

%
       A |- t1 \/ t2
    --------------------
     A |-  ~ t1 ==> t2
%

let DISJ_IMP dth =
 (let a,b = dest_disj (concl dth)
  in
  let nota = "~ ^a"
  in
  DISCH nota 
   (DISJ_CASES dth 
    (CONTR b (NOT_MP (ASSUME nota) (ASSUME a)))
    (ASSUME b))
 ) ? failwith `DISJ_IMP`;;

%
   A |- t1 ==> t2
  ---------------
   A |- ~t1 \/ t2
%

let IMP_ELIM th =
 (let t1,t2 = dest_imp (snd (dest_thm th))
  in
  DISJ_CASES
   (SPEC t1 EXCLUDED_MIDDLE)
   (DISJ2 "~^t1" (MP th (ASSUME t1)))
   (DISJ1 (ASSUME "~^t1") t2)
 ) ? failwith `IMP_ELIM`;;

% --------------------------------------------------------------------- %
% NOT_CLAUSES = |- (~~t = t) /\ (~T = F) /\ (~F = T) 			%
% --------------------------------------------------------------------- %

let NOT_CLAUSES =
 (CONJ
  (GEN "t:bool"
    (IMP_ANTISYM_RULE
      (DISJ_IMP(IMP_ELIM(DISCH "t:bool" (ASSUME "t:bool"))))
      (DISCH "t:bool"
       (NOT_INTRO(DISCH "~t" (UNDISCH (NOT_ELIM(ASSUME "~t"))))))))
  (CONJ
   (IMP_ANTISYM_RULE
    (DISCH "~T" (MP (MP (SPEC "T" F_IMP) (ASSUME "~T")) TRUTH))
    (SPEC "~T" FALSITY))
   (IMP_ANTISYM_RULE
    (DISCH "~F" TRUTH)
    (DISCH "T" (MP (SPEC "F" IMP_F) (SPEC "F" FALSITY))))));;

% --------------------------------------------------------------------- %
%   A |- t1 \/ t2     A1, t1 |- t3      A2, t2 |- t4			%
%   ------------------------------------------------			%
%               A u A1 u A2 |- t3 \/ t4					%
% --------------------------------------------------------------------- %

let DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);;

% --------------------------------------------------------------------- %
% FORWARD CHAINING: (from LCF)				 [TFM 90.04.24] %
%									%
% deleted until found useful and properly reimplemented for HOL.	%
%									%
% Forward chain using an inference rule on top-level sub-parts of a 	%
% theorem. Could be extended to handle other connectives		%
%									%
% let SUB_CHAIN rule th =						%
%    let w = concl th in						%
%    if is_conj w then 							%
% 	CONJ (rule(CONJUNCT1 th)) (rule(CONJUNCT2 th))			%
%    else if is_disj w then						%
%	let a,b = dest_disj w in					%
% 	DISJ_CASES_UNION th (rule (ASSUME a)) (rule (ASSUME b))		%
%    else if is_imp w then						%
%	let a,b = dest_imp w in						%
% 	DISCH a (rule (UNDISCH th))					%
%    else if is_forall w then						%
%	let x', sth = SPEC_VAR th in					%
%	GEN x' (rule sth)						%
%    else th;;								%
%									%
% Repeatedly apply the rule (looping if it never fails)			%
%									%
% letrec REDEPTH_CHAIN rule x =						%
%    (SUB_CHAIN (REDEPTH_CHAIN rule) thenf				%
%    ((rule thenf (REDEPTH_CHAIN rule)) orelsef I))			%
%   x;;									%
%									%
% Apply the rule no more than once in any one place			%
%									%
%letrec ONCE_DEPTH_CHAIN rule x =					%
%   (rule  orelsef  SUB_CHAIN (ONCE_DEPTH_CHAIN rule))			%
%   x;;									%
%									%
% DSPEC : Specialize a theorem whose quantifiers are buried inside	%
%									%
% let DSPEC x = ONCE_DEPTH_CHAIN (SPEC x);;				%
% let DSPECL = rev_itlist DSPEC;;					%
%									%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% let CLOSE_UP = GEN_ALL o DISCH_ALL;;					%
% let save_thm (name, th) =  save_open_thm (name, CLOSE_UP th);; 	%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% EQ_REFL: |- !x. x=x 							%
% --------------------------------------------------------------------- %

let EQ_REFL = GEN "x:*" (REFL "x:*");;

% --------------------------------------------------------------------- %
% REFL_CLAUSE |- !x. (x=x) = T 						%
% --------------------------------------------------------------------- %

let REFL_CLAUSE = GEN "x:*" (EQT_INTRO(SPEC "x:*" EQ_REFL));;

% --------------------------------------------------------------------- %
% EQ_SYM : |- !x y. x=y  ==>  y=x  					%
% --------------------------------------------------------------------- %

let EQ_SYM = 
    GEN "x:*" (GEN "y:*" (DISCH "x:* = y:*" (SYM(ASSUME "x:* = y:*"))));;

% --------------------------------------------------------------------- %
% EQ_SYM_EQ: |- !x y. (x = y) = (y = x) 				%
% --------------------------------------------------------------------- %

let EQ_SYM_EQ =
 GEN
  "x:*"
  (GEN
   "y:*"
   (IMP_ANTISYM_RULE
    (SPEC "y:*" (SPEC "x:*" EQ_SYM))
    (SPEC "x:*" (SPEC "y:*" EQ_SYM))));;


% --------------------------------------------------------------------- %
% |- !f g. (!x. f x = g x)  ==>  f=g 					%
% --------------------------------------------------------------------- %

let EQ_EXT =
 let f = "f: * -> **"
 and g = "g: * -> **"
 and t = "!x:*. (f:*->**) (x:*) = (g:*->**) (x:*)"
 in
 GEN f (GEN g (DISCH t (EXT(ASSUME t))));;

% --------------------------------------------------------------------- %
% EQ_TRANS |- !x y z. x=y  /\  y=z  ==>  x=z 				%
% --------------------------------------------------------------------- %

let EQ_TRANS =
 let x,y,z = "x:*","y:*","z:*"
 and xyyz  = "(x:*=y:*) /\ (y:*=z:*)"
 in
 GEN x
  (GEN y
   (GEN z
    (DISCH xyyz
     (CONJUNCT1(ASSUME xyyz) TRANS (CONJUNCT2(ASSUME xyyz)))))) ;;

% --------------------------------------------------------------------- %
% BOOL_EQ_DISTINCT |- ~(T=F) /\ ~(F=T) 					%
% --------------------------------------------------------------------- %

let BOOL_EQ_DISTINCT =
 CONJ
  (NOT_INTRO(DISCH "T=F" (EQ_MP (ASSUME "T=F") TRUTH)))
  (NOT_INTRO(DISCH "F=T" (EQ_MP (SYM(ASSUME "F=T")) TRUTH)));;


% --------------------------------------------------------------------- %
% EQ_CLAUSES: proof rewritten to make clauses 1-4 local 		%
%									%
% |- !t.  (T = t)  =  t  /\						%
%         (t = T)  =  t  /\						%
%         (F = t)  =  ~t /\						%
%         (t = F)  =  ~t		                   TFM 90.04.20 %
% --------------------------------------------------------------------- %

let EQ_CLAUSES =
 let t = "t:bool" in
 let cl1 = 						  % (T = t) = t %
     let th1 = DISCH "T = ^t" (EQ_MP (ASSUME "T = ^t") TRUTH)
     and th2 = DISCH t (SYM(EQT_INTRO(ASSUME t))) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl2 = 				 	          % (t = T) = t %
    let th1 = DISCH "^t = T" (EQ_MP (SYM (ASSUME "^t = T")) TRUTH)
    and th2 = DISCH t (EQT_INTRO(ASSUME t)) in
    (IMP_ANTISYM_RULE th1 th2)
 and cl3 = 					         % (F = t) = ~t %
     let th1 = DISCH
                "F = ^t"
                (MP
                 (SPEC t IMP_F)
                 (DISCH t (EQ_MP(SYM(ASSUME "F = ^t"))(ASSUME t))))
     and th2 = IMP_TRANS
                (SPEC t NOT_F)
                (DISCH "^t = F" (SYM(ASSUME "^t = F"))) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl4 =  						 % (t = F) = ~t %
     let th1 = DISCH
                "^t = F"
                (MP
                 (SPEC t IMP_F)
                 (DISCH t (EQ_MP(ASSUME "^t = F")(ASSUME t))))
     and th2 = SPEC t NOT_F in
     (IMP_ANTISYM_RULE th1 th2) in
 GEN t (end_itlist CONJ [cl1;cl2;cl3;cl4]);;



% --------------------------------------------------------------------- %
% MK_COMB:                                                   		%
%									%
%     A1 |- f = g  ,  A2 |- x = y					%
%     ---------------------------					%
%       A1 u A2 |- f x = g y						%
%									%
%<
let MK_COMB (funth,argth) = 
   (let f = lhs (concl funth)
    and x = lhs (concl argth)
    in
    SUBS_OCCS [([2], funth); ([2], argth)] (REFL (mk_comb(f,x))))
   ? failwith `MK_COMB`;;
>%
% --------------------------------------------------------------------- %

let MK_COMB (funth,argth) =
 (let f,g = dest_eq (concl funth)
  and x,y = dest_eq (concl argth)
  in
  (RecordStep(MkCombStep(funth,argth));
   mk_thm(union (hyp funth) (hyp argth), mk_eq(mk_comb(f,x),mk_comb(g,y))))
 ) ? failwith `MK_COMB`;;

%
       A |- !x. (t1 = t2)
     ----------------------
     A |- (\x.t1) = (\x.t2)

let MK_ABS qth =
   (let x,body = dest_forall (concl qth) 
    in
    let ufun = mk_abs(x, lhs body)
    and vfun = mk_abs(x, rhs body)
    in
    let gv = genvar (type_of x) 
    in
    EXT (GEN gv
	 ((BETA_CONV (mk_comb(ufun,gv)))  TRANS  
	  (SPEC gv qth)  TRANS  
	   (SYM (BETA_CONV (mk_comb(vfun,gv)))))))
   ? failwith `MK_ABS`;;
%

let MK_ABS th =
 (let x,(t1,t2) = ((I # dest_eq) o dest_forall o concl) th
  in
  (RecordStep(MkAbsStep th);
   mk_thm(hyp th, mk_eq(mk_abs(x,t1),mk_abs(x,t2))))
 ) ? failwith `MK_ABS`;;


%
     A |- !x. t1 x = t2
     ------------------
      A |-  t1 = \x.t2
%

let HALF_MK_ABS qth =
   (let x,body = dest_forall (concl qth) 
    in
    let t = rhs body
    and gv = genvar (type_of x) 
    in
    let tfun = mk_abs(x,t)
    in
    EXT (GEN gv 		% |- !gv. u gv =< (\x.t) gv  %
	 ((SPEC gv qth)  TRANS  
	  (SYM (BETA_CONV (mk_comb(tfun,gv)))))))
   ? failwith `HALF_MK_ABS`;;

% --------------------------------------------------------------------- %
% ALPHA_CONV: Rename the bound variable of a lambda-abstraction		%
%									%
% ALPHA_CONV "x" "(\y.t)" ---> |- "\y.t = \x. t[x/y]"  			%
%									%
% OLD VERSION: 								%
% 									%
%    let ALPHA_CONV x t =						%
%        (let x' = variant (frees t) x  in				%
%         HALF_MK_ABS (GEN x'(BETA_CONV(mk_comb(t,x')))))		%
%        ? failwith `ALPHA_CONV`;;					%
%									%
% replaced in version 1.12 by an optimized proof.        [TFM 90.06.12] %
% --------------------------------------------------------------------- %

let ALPHA_CONV x t =
   (let x' = variant (frees t) x  in
    let cmb = mk_comb(t,x') in
    let th1 = SYM(ETA_CONV(mk_abs(x',cmb))) and
        th2 = ABS x' (BETA_CONV cmb) in
	TRANS th1 th2) ? 
   failwith `ALPHA_CONV`;;

% Equivalence of alpha-convertable terms 

     t1, t2 alpha-convertable
     -------------------------
            |- t1 = t2

letrec ALPHA t1 t2 =
 (if t1=t2
   then REFL t1
  if is_comb t1 & is_comb t2
   then
   (let t11,t12 = dest_comb t1
    and t21,t22 = dest_comb t2
    in
    let th1 = ALPHA t11 t21
    and th2 = ALPHA t12 t22
    in (AP_THM th1 t12) TRANS (AP_TERM t21 th2))
  if is_abs t1 & is_abs t2
   then
   (let x1,()  = dest_abs t1
    and x2,t2' = dest_abs t2
    in
    let th1 = ALPHA_CONV x2 t1
    in
    let (),t1' = dest_abs(rhs(concl th1))
    in
    let th2 = ALPHA t1' t2'
    in 
    th1 TRANS (ABS x2 th2))
   else fail
   ) ? failwith `ALPHA`;;
%

let ALPHA t1 t2 =
    if aconv t1 t2 
    then
    (RecordStep(AlphaStep(t1,t2));
     mk_thm([],mk_eq(t1,t2)))
    else failwith `ALPHA`;;

% --------------------------------------------------------------------- %
% GEN_ALPHA_CONV: rename bound variables				%
%									%
%       "x"   "(\y.t)"   --->   |- "\y.t = \x. t[x/y]"  		%
%       "x"   "(!y.t)"   --->   |- "!y.t = !x. t[x/y]"  		%
%       "x"   "(?y.t)"   --->   |- "?y.t = ?x. t[x/y]"  		%
%       "x"   "(@y.t)"   --->   |- "@y.t = @x. t[x/y]"  		%
%       "x"   "(?!y.t)"   --->  |- "?!y.t = ?!x. t[x/y]"  		%
%									%
% REVISED: to also deal with ?! quantifier.              [TFM 91.02.24] %
%									%
% Revised to work with any term of the form "B \x.M", where B is a 	%
% binder constant (according to is_binder).              [TFM 92.03.09] %
% --------------------------------------------------------------------- %

let GEN_ALPHA_CONV =
    let check = assert (is_binder o fst o dest_const) in
    \x t. if (is_abs t) then ALPHA_CONV x t else
          (let (c,body) = (check # I) (dest_comb t) in
              AP_TERM c (ALPHA_CONV x body)) ? failwith `GEN_ALPHA_CONV`;;


% --------------------------------------------------------------------- %
% COND_CLAUSES: proof rewritten to make clauses 1 and 2 local 		%
%									%
% |- !t1:*.!t2:*. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2) 	%
%									%
%					                   TFM 90.04.20 %
% --------------------------------------------------------------------- %

let COND_CLAUSES =
    let x,t1,t2,v = "x:*","t1:*","t2:*",genvar":bool" in
    let cl1 =
        let th0 = RIGHT_BETA(AP_THM COND_DEF "T") in
	let th1 = RIGHT_BETA(AP_THM th0 t1) in
        let th2 = RIGHT_BETA(AP_THM th1 t2) in
        let TT = EQT_INTRO(REFL "T") in
        let th3= 
            SUBST[SYM TT,v] "(^v ==> (^x=^t1))=(^x=^t1)" 
                            (CONJUNCT1 (SPEC "^x=^t1" IMP_CLAUSES)) and
            th4 =
            DISCH
              "T=F"
               (MP
                 (SPEC "^x=^t2" FALSITY)
                 (UNDISCH (MP (SPEC "T=F" F_IMP) 
		 	      (CONJUNCT1 BOOL_EQ_DISTINCT)))) in
        let th5 = DISCH "^x=^t1" 
		    (CONJ(EQ_MP(SYM th3)(ASSUME "^x=^t1"))th4) and
            th6	= DISCH "((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))"
                  (MP
                  (CONJUNCT1
  		    (ASSUME "((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))"))
                    (REFL "T")) in
        let th7 = 
              MP
               (MP (SPEC "((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))" 
                   (SPEC "^x=^t1" IMP_ANTISYM_AX))
               th5)
               th6 in
        let th8 = TRANS th2 (SYM(SELECT_EQ x th7)) in
        let th9 = EQ_MP (SYM(BETA_CONV "(\^x.^x = ^t1) ^t1")) (REFL t1) in
        let th10 = MP (SPEC t1 (SPEC "\^x.^x = ^t1" SELECT_AX)) th9 in
            (TRANS th8 (EQ_MP (BETA_CONV(concl th10)) th10))
    and cl2 =
        let th0 = RIGHT_BETA(AP_THM COND_DEF "F") in
	let th1 = RIGHT_BETA(AP_THM th0 t1) in
        let th2 = RIGHT_BETA(AP_THM th1 t2) in
        let FF = EQT_INTRO(REFL "F") in
        let th3 = 
            SUBST[SYM FF,v] "(^v ==> (^x=^t2))=(^x=^t2)" 
                 (CONJUNCT1 (SPEC "^x=^t2" IMP_CLAUSES))
        and th4 =
               DISCH
                  "F=T"
                   (MP
                   (SPEC "^x=^t1" FALSITY)
                    (UNDISCH(MP (SPEC "F=T" F_IMP) 
		             (CONJUNCT2 BOOL_EQ_DISTINCT)))) in
        let th5 =
            DISCH "^x=^t2" (CONJ th4 (EQ_MP(SYM th3)(ASSUME "^x=^t2")))
        and th6 =
            DISCH "((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))"
             (MP
            (CONJUNCT2(ASSUME "((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))"))
           (REFL "F")) in
        let th7 = 
             MP
             (MP (SPEC "((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))" 
                  (SPEC "^x=^t2" IMP_ANTISYM_AX))
               th5)
               th6 in
        let th8 = TRANS th2 (SYM(SELECT_EQ x th7)) in
        let th9 = EQ_MP (SYM(BETA_CONV "(\^x.^x = ^t2) ^t2")) (REFL t2) in
        let th10 = MP (SPEC t2 (SPEC "\^x.^x = ^t2" SELECT_AX)) th9 in
             (TRANS th8 (EQ_MP (BETA_CONV(concl th10)) th10)) in
     GEN t1 (GEN t2 (CONJ cl1 cl2));;

% --------------------------------------------------------------------- %
% COND_ID: 								%
%									%
% |- b. !t:*. (b => t | t) = t						%
%									%
%					                   TFM 90.07.23 %
% --------------------------------------------------------------------- %

let COND_ID =
    let b = "b:bool" and t = "t:*" in
    let def = INST_TYPE [":*",":**"] COND_DEF in
    let th1 = itlist (\x.RIGHT_BETA o (C AP_THM x)) [t;t;b] def in
    let p = genvar ":bool" in
    let asm1 = ASSUME ("((^b=T)==>^p) /\ ((^b=F)==>^p)") in
    let th2 = DISJ_CASES (SPEC b BOOL_CASES_AX)
    	                  (UNDISCH (CONJUNCT1 asm1))
   		          (UNDISCH (CONJUNCT2 asm1)) in
    let imp1 = DISCH (concl asm1) th2 in
    let asm2 = ASSUME p in
    let imp2 = DISCH p (CONJ (DISCH "^b=T" (ADD_ASSUM "^b=T" asm2))
	                     (DISCH "^b=F" (ADD_ASSUM "^b=F" asm2))) in
    let lemma = SPEC "x:* = ^t" (GEN p (IMP_ANTISYM_RULE imp1 imp2)) in
    let th3 = TRANS th1 (SELECT_EQ "x:*" lemma) in
    let th4 = EQ_MP (SYM(BETA_CONV "(\x.x = ^t) ^t")) (REFL t) in
    let th5 = MP (SPEC t (SPEC "\x.x = ^t" SELECT_AX)) th4 in
    let lemma2 = EQ_MP (BETA_CONV(concl th5)) th5 in
         GEN b (GEN t (TRANS th3 lemma2));;

% --------------------------------------------------------------------- %
% IMP_CONJ implements the following derived inference rule:		%
%									%
%  A1 |- P ==> Q    A2 |- R ==> S					%
% --------------------------------- IMP_CONJ				%
%   A1 u A2 |- P /\ R ==> Q /\ S					%
% --------------------------------------------------------------------- %

let IMP_CONJ th1 th2 = 
    let A1,C1 = dest_imp (concl th1) and A2,C2 = dest_imp (concl th2) in
    let a1,a2 = CONJ_PAIR (ASSUME (mk_conj(A1,A2))) in
        DISCH (mk_conj(A1,A2)) (CONJ (MP th1 a1) (MP th2 a2));;

% --------------------------------------------------------------------- %
% EXISTS_IMP : existentially quantify the antecedent and conclusion 	%
% of an implication.							%
%									%
%        A |- P ==> Q							%
% -------------------------- EXISTS_IMP "x"				%
%   A |- (?x.P) ==> (?x.Q)						%
%									%
% --------------------------------------------------------------------- %

let EXISTS_IMP x =
    if (not (is_var x))
       then failwith `EXISTS_IMP: first argument not a variable`
       else \th. let ante,cncl = dest_imp(concl th) in
                 let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
                 let asm = mk_exists(x,ante) in
                      DISCH asm (CHOOSE (x,ASSUME asm) th1) ?
                      failwith `EXISTS_IMP: variable free in assumptions`;;



% ------------------------------------------------------------------------- %
% Distributive laws:							    %
%									    %
% LEFT_AND_OVER_OR |- !t1 t2 t3. t1 /\ (t2 \/ t3) = t1 /\ t2 \/ t1 /\ t3    %
%									    %
% RIGHT_AND_OVER_OR |- !t1 t2 t3. (t2 \/ t3) /\ t1 = t2 /\ t1 \/ t3 /\ t1   %
%									    %
% LEFT_OR_OVER_AND |- !t1 t2 t3. t1 \/ t2 /\ t3 = (t1 \/ t2) /\ (t1 \/ t3)  %
%									    %
% RIGHT_OR_OVER_AND |- !t1 t2 t3. t2 /\ t3 \/ t1 = (t2 \/ t1) /\ (t3 \/ t1) %
% ------------------------------------------------------------------------- %

let LEFT_AND_OVER_OR = 
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in
    let th1,th2 = CONJ_PAIR(ASSUME (mk_conj(t1,mk_disj(t2,t3)))) in
    let th3 = CONJ th1 (ASSUME t2) and th4 = CONJ th1 (ASSUME t3) in
    let th5 = DISJ_CASES_UNION th2 th3 th4 in
    let imp1 = DISCH (mk_conj(t1,mk_disj(t2,t3))) th5 in
    let th1,th2 = (I # C DISJ1 t3) (CONJ_PAIR (ASSUME (mk_conj(t1,t2)))) in
    let th3,th4 = (I # DISJ2 t2) (CONJ_PAIR (ASSUME (mk_conj(t1,t3)))) in
    let th5 = CONJ th1 th2 and th6 = CONJ th3 th4 in
    let th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6 in
    let imp2 = DISCH (rand(concl imp1)) th6 in
        GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)));;
    
let RIGHT_AND_OVER_OR = 
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in
    let th1,th2 = CONJ_PAIR(ASSUME (mk_conj(mk_disj(t2,t3),t1))) in
    let th3 = CONJ (ASSUME t2) th2 and th4 = CONJ (ASSUME t3) th2 in
    let th5 = DISJ_CASES_UNION th1 th3 th4 in
    let imp1 = DISCH (mk_conj(mk_disj(t2,t3),t1)) th5 in
    let th1,th2 = (C DISJ1 t3 # I) (CONJ_PAIR (ASSUME (mk_conj(t2,t1)))) in
    let th3,th4 = (DISJ2 t2 # I) (CONJ_PAIR (ASSUME (mk_conj(t3,t1)))) in
    let th5 = CONJ th1 th2 and th6 = CONJ th3 th4 in
    let th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6 in
    let imp2 = DISCH (rand(concl imp1)) th6 in
        GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)));;
    
let LEFT_OR_OVER_AND = 
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in
    let th1 = ASSUME (mk_disj(t1,mk_conj(t2,t3))) in
    let th2 = CONJ (DISJ1 (ASSUME t1) t2) (DISJ1 (ASSUME t1) t3) in
    let th3,th4 = CONJ_PAIR (ASSUME(mk_conj(t2,t3))) in
    let th5 = CONJ (DISJ2 t1 th3) (DISJ2 t1 th4) in
    let imp1 = DISCH (concl th1) (DISJ_CASES th1 th2 th5) in
    let th1,th2 = CONJ_PAIR (ASSUME (rand(concl imp1))) in
    let th3 = DISJ1 (ASSUME t1) (mk_conj(t2,t3)) in
    let th4,th5 = CONJ_PAIR (ASSUME (mk_conj(t2,t3))) in
    let th4 = DISJ2 t1 (CONJ (ASSUME t2) (ASSUME t3)) in
    let th5 = DISJ_CASES th2 th3 (DISJ_CASES th1 th3 th4) in
    let imp2 = DISCH (rand(concl imp1)) th5 in
        GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)));;

let RIGHT_OR_OVER_AND = 
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in
    let th1 = ASSUME (mk_disj(mk_conj(t2,t3),t1)) in
    let th2 = CONJ (DISJ2 t2 (ASSUME t1)) (DISJ2 t3 (ASSUME t1)) in
    let th3,th4 = CONJ_PAIR (ASSUME(mk_conj(t2,t3))) in
    let th5 = CONJ (DISJ1 th3 t1) (DISJ1 th4 t1) in
    let imp1 = DISCH (concl th1) (DISJ_CASES th1 th5 th2) in
    let th1,th2 = CONJ_PAIR (ASSUME (rand(concl imp1))) in
    let th3 = DISJ2 (mk_conj(t2,t3)) (ASSUME t1)  in
    let th4,th5 = CONJ_PAIR (ASSUME (mk_conj(t2,t3))) in
    let th4 = DISJ1 (CONJ (ASSUME t2) (ASSUME t3)) t1 in
    let th5 = DISJ_CASES th2 (DISJ_CASES th1 th4 th3) th3 in
    let imp2 = DISCH (rand(concl imp1)) th5 in
        GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)));;

% --------------------------------------------------------------------- %
% IMP_DISJ_THM								%
%									%
% |- !t1 t2. t1 ==> t2 = ~t1 \/ t2					%
%									%
% Moved from arithmetic theory	       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let IMP_DISJ_THM =
   let [_;IMP2;_;_;IMP4] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
   and [_;OR2;_;OR4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   in  let thT1 = (SPEC "t1:bool" IMP2) TRANS (SYM (SPEC "~t1" OR2))
       and thF1 = (SPEC "t1:bool" IMP4) TRANS (SYM (SPEC "~t1" OR4))
   in  let tm = "t1 ==> t2 = ~t1 \/ t2"
   in  let thT2 = SUBST_CONV [(ASSUME "t2 = T","t2:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t2 = F","t2:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t2:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% IMP_F_EQ_F								%
%									%
% |- !t. t ==> F = (t = F)						%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let IMP_F_EQ_F =
   GEN_ALL (TRANS (el 5 (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))
                     (SYM (el 4 (CONJUNCTS (SPEC_ALL EQ_CLAUSES)))));;

% --------------------------------------------------------------------- %
% AND_IMP_INTRO								%
%									%
% |- !t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3			%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let AND_IMP_INTRO =
   let [IMP1;IMP2;IMP3;_;IMP4] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   in  let thTl = SPEC "t2 ==> t3" IMP1
       and thFl = SPEC "t2 ==> t3" IMP3
   in  let thTr = AP_THM (AP_TERM "$==>" (SPEC "t2:bool" AND1)) "t3:bool"
       and thFr =
          TRANS (AP_THM (AP_TERM "$==>" (SPEC "t2:bool" AND3)) "t3:bool")
                   (SPEC "t3:bool" IMP3)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% EQ_IMP_THM								%
%									%
% |- !t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)			%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let EQ_IMP_THM =
   let [IMP1;IMP2;IMP3;_;IMP4] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
   and [EQ1;EQ2;EQ3;EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   in  let thTl = SPEC "t2:bool" EQ1
       and thFl = SPEC "t2:bool" EQ3
   in  let thTr =
          TRANS
          (MK_COMB (AP_TERM "$/\" (SPEC "t2:bool" IMP1),SPEC "t2:bool" IMP2))
          (SPEC "t2:bool" AND2)
       and thFr =
          TRANS
          (MK_COMB (AP_TERM "$/\" (SPEC "t2:bool" IMP3),SPEC "t2:bool" IMP4))
          (SPEC "~t2" AND1)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% EQ_EXPAND								%
%									%
% |- !t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))			%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let EQ_EXPAND =
   let [NOT1;NOT2] = tl (CONJUNCTS NOT_CLAUSES)
   and [EQ1;EQ2;EQ3;EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   and [OR1;OR2;OR3;OR4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   in  let thTl = SPEC "t2:bool" EQ1
       and thFl = SPEC "t2:bool" EQ3
   in  let thTr =
          TRANS
          (MK_COMB
              (AP_TERM "$\/" (SPEC "t2:bool" AND1),
               TRANS (AP_THM (AP_TERM "$/\" NOT1) "~t2") (SPEC "~t2" AND3)))
          (SPEC "t2:bool" OR4)
       and thFr =
          TRANS
          (MK_COMB
              (AP_TERM "$\/" (SPEC "t2:bool" AND3),
               TRANS (AP_THM (AP_TERM "$/\" NOT2) "~t2") (SPEC "~t2" AND1)))
          (SPEC "~t2" OR3)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% COND_RATOR								%
%									%
% |- !b (f:*->**) g x. (b => f | g) x = (b => f x | g x)		%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let COND_RATOR =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   in  let thTl = AP_THM (ISPECL ["f:*->**";"g:*->**"] COND_T) "x:*"
       and thFl = AP_THM (ISPECL ["f:*->**";"g:*->**"] COND_F) "x:*"
   in  let thTr = ISPECL ["(f:*->**) x";"(g:*->**) x"] COND_T
       and thFr = ISPECL ["(f:*->**) x";"(g:*->**) x"] COND_F
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(b => (f:*->**) | g) x = (b => f x | g x)"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% COND_RAND								%
%									%
% |- !(f:*->**) b x y. f (b => x | y) = (b => f x | f y)		%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let COND_RAND =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   in  let thTl = AP_TERM "f:*->**" (ISPECL ["x:*";"y:*"] COND_T)
       and thFl = AP_TERM "f:*->**" (ISPECL ["x:*";"y:*"] COND_F)
   in  let thTr = ISPECL ["(f:*->**) x";"(f:*->**) y"] COND_T
       and thFr = ISPECL ["(f:*->**) x";"(f:*->**) y"] COND_F
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(f:*->**) (b => x | y) = (b => f x | f y)"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

% --------------------------------------------------------------------- %
% COND_ABS								%
%									%
% |- !b (f:*->**) g. (\x. (b => f(x) | g(x))) = (b => f | g)		%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let COND_ABS =
   let th = SYM (SPECL ["b:bool";"f:*->**";"g:*->**";"x:*"] COND_RATOR)
   in  GEN_ALL ((ABS "x:*" th) TRANS (ETA_CONV "\x. (b => (f:*->**) | g) x"));;

% --------------------------------------------------------------------- %
% COND_EXPAND								%
%									%
% |- !b t1 t2. (b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))		%
%									%
%				       	                   RJB 92.09.26 %
% --------------------------------------------------------------------- %

let COND_EXPAND =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   and [NOT1;NOT2] = tl (CONJUNCTS NOT_CLAUSES)
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   and [OR1;OR2;OR3;OR4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   in  let thTl = ISPECL ["t1:bool";"t2:bool"] COND_T
       and thFl = ISPECL ["t1:bool";"t2:bool"] COND_F
   in  let thTr =
          let th1 = TRANS (AP_THM (AP_TERM "$\/" NOT1) "t1:bool")
                             (SPEC "t1:bool" OR3)
          and th2 = SPEC "t2:bool" OR1
          in  TRANS (MK_COMB (AP_TERM "$/\" th1,th2)) (SPEC "t1:bool" AND2)
       and thFr =
          let th1 = TRANS (AP_THM (AP_TERM "$\/" NOT2) "t1:bool")
                             (SPEC "t1:bool" OR1)
          and th2 = SPEC "t2:bool" OR3
          in  TRANS (MK_COMB (AP_TERM "$/\" th1,th2)) (SPEC "t2:bool" AND1)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

