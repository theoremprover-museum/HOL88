% ===================================================================== %
% FILE		: wordn_rules.ml					%
% DESCRIPTION   : wordn type definition package.			%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 90.08.20						%
% MODEFIED BY   : Wai Wong  	02 April 1992				%
%   	    adding new_definition and use_wordn				%
% ===================================================================== %

% ===================================================================== %
% The following are user level functions: (i.e. should be documented)	%
%   define_wordn_type : string -> int -> thm				%
%   prove_BITS_one_one : (thm -> thm)					%
%   prove_BITS_onto : (thm -> thm)  					%
%   prove_WORD_one_one : (thm -> thm)					%
%   prove_WORD_onto : (thm -> thm)  					%
%   prove_LENGTH_BITS_thm : (thm -> thm)				%
%   prove_function_defn_thm : (thm -> thm)				%
%   prove_wordn_induction_thm : (thm -> thm)				%
%   prove_wordn_cases_thm : (thm -> thm)				%
%   new_wordn_definition : (bool -> thm -> string -> conv)		%
%   use_wordn : (int -> (thm) list) 					%
% ===================================================================== %

% ===================================================================== %
% Type definition.							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define_wordn_type: for given n, define a type :wordn of n-bit words.	%
%									%
% For example:                                                          %
%									%
%    define_wordn_type <name> 3				                %
%                                                                       %
% defines:				                                %
%									%
%    1) a type :word3						        %
%    2) a constant WORD3:(bool)list->word3				%
%    3) a constant BITS3:word3->(bool)list				%
%									%
% and proves that the functions WORD3 and BITS3 have the following      %
% property:		                                        	%
%									%
%  |- (!w. WORD3(BITS3 w) = w) /\                                       %
%     (!l. (LENGTH l = 3) = (BITS3(WORD3 l) = l))                       %
%									%
% This theorem is stored under the supplied name and is returned.	%
% ===================================================================== %

let define_wordn_type =
    let numty = ":num" in
    let arthm = theorem `wordn_base` `wordn_ABS_REP` and
        exthm = theorem `wordn_base` `EXISTS_wordn_REP` in
    \name n. 
      (if (is_axiom(`-`,name)) then
	  failwith `"` ^ name ^ `" already a defn.` else
       if (n<0) then failwith `negative word width` else
       if not(draft_mode()) then failwith `not in draft mode` else
       let nstr = string_of_int n in
       let WORDn = `WORD` ^ nstr and BITSn = `BITS` ^ nstr in
       if (is_constant WORDn) then
          failwith `"` ^ WORDn ^ `" already a constant` else
       if (is_constant BITSn) then
          failwith `"` ^ BITSn ^ `" already a constant` else
       if (is_type (`word` ^ nstr)) then
          failwith `type ":word` ^ nstr ^ `" already defined` else
       let eth = SPEC (mk_const(nstr, numty)) exthm in
       let tyax = new_type_definition
                  (`word` ^ nstr,rator(snd(dest_exists(concl eth))),eth) in
       let ABS_REP = MATCH_MP arthm tyax in
           new_specification name
	        [`constant`,BITSn;`constant`,WORDn] ABS_REP) 
       ?\st failwith `define_wordn_type: ` ^ st;;

% ===================================================================== %
% Derived inference rules for theorems about BITSn and WORDn            %
% ===================================================================== %

% --------------------------------------------------------------------- %
% prove_BITS_one_one: prove that the BITSn function for a wordn type is %
% one-to-one. The input theorem is a theorem of the form returned by    %
% define_wordn_type:                                                    %
%                                                                       %
%     |- (!w. WORDn(BITSn w) = w) /\                                    %
%        (!l. (LENGTH l = n) = (BITSn(WORDn l) = l))                    %
%                                                                       %
% The output is the corresponding theorem:                              %
%                                                                       %
%     |- !w' w. (BITSn w = BITSn w') ==> (w = w')                       %
%                                                                       %
% --------------------------------------------------------------------- %

let prove_BITS_one_one =
    let MKEQ = \eq t1 t2. MK_COMB(AP_TERM eq t1,t2) in
    \th. (let WBth = CONJUNCT1 th in
          let w,eq,WB = (I # (dest_comb o rator)) (dest_forall(concl WBth)) in
          let w' = variant [w] w and W,B = dest_comb WB in
          let asm = AP_TERM W (ASSUME (mk_eq(B,mk_comb(rator B,w')))) in
          let thm = EQ_MP (MKEQ eq (SPEC w WBth)(SPEC w' WBth)) asm in
              GEN w' (GEN w (DISCH  (mk_eq(B,mk_comb(rator B,w'))) thm)))
         ? failwith `prove_BITS_one_one`;;

% --------------------------------------------------------------------- %
% prove_BITS_onto: prove that the BITSn function for a wordn type is    %
% onto the set of all boolean lists of length n. The input theorem is a %
% theorem of the form returned by define_wordn_type:                    %
%                                                                       %
%     |- (!w. WORDn(BITSn w) = w) /\                                    %
%        (!l. (LENGTH l = n) = (BITSn(WORDn l) = l))                    %
%                                                                       %
% The output is the corresponding theorem:                              %
%                                                                       %
%     |- !l. (LENGTH l = n) ==> (?w. BITSn w = l)                       %
% --------------------------------------------------------------------- %

let prove_BITS_onto th = 
    let BWth = CONJUNCT2 th in
    let l,len,BW = (I # dest_eq) (dest_forall(concl BWth)) in
    let w = fst(dest_forall(fst(dest_conj (concl th)))) in
    let BITS = rator(lhs BW) in
    let pat = mk_exists(w,mk_eq(mk_comb(rator(lhs BW),w),l)) in
    let asm = EQ_MP (SPEC l BWth) (ASSUME len) in
        GEN l (DISCH len (EXISTS(pat,rand(lhs BW)) asm))
    ? failwith `prove_BITS_onto`;;

% --------------------------------------------------------------------- %
% prove_WORD_one_one: prove that the WORDn function for a wordn type    %
% is one-to-one for lists of length n. The input is a theorem of the    %
% form returned by define_wordn_type:                                   %
%                                                                       %
%     |- (!w. WORDn(BITSn w) = w) /\                                    %
%        (!l. (LENGTH l = n) = (BITSn(WORDn l) = l))                    %
%                                                                       %
% The output is the corresponding theorem:                              %
%                                                                       %
%     |- !l l'. (LENGTH l = n) /\ (LENGTH l' = n) ==>                   %
%               (WORDn l = WORDn l') ==> (l = l')                       %
% --------------------------------------------------------------------- %

let prove_WORD_one_one =
    let MKEQ = let eq = "$=:(bool)list->(bool)list->bool" in 
              \th1 th2. MK_COMB(AP_TERM eq th1,th2) in
    \th. (let wth = CONJUNCT2 th in
          let l,lenl,eq = (I # dest_eq) (dest_forall (concl wth)) in
          let l' = variant [l] l in
          let conj = mk_conj(lenl,subst[l',l] lenl) in
          let as1,as2 = CONJ_PAIR(ASSUME conj) in
          let thm = MKEQ (EQ_MP(SPEC l wth)as1) (EQ_MP(SPEC l' wth)as2) in
          let BITS,WORD = (I # rator) (dest_comb(lhs eq)) in
          let asm = mk_eq(mk_comb(WORD,l),mk_comb(WORD,l')) in
          let th1 = DISCH asm (EQ_MP thm (AP_TERM BITS (ASSUME asm))) in
              GEN l (GEN l' (DISCH conj th1)))
         ? failwith `prove_WORD_one_one`;;

% --------------------------------------------------------------------- %
% prove_WORD_onto: prove that the WORDn function for a wordn type is    %
% onto the set of all n-bit words. The input is a theorem of the form   %
% returned by define_wordn_type:                                        %
%                                                                       %
%     |- (!w. WORDn(BITSn w) = w) /\                                    %
%        (!l. (LENGTH l = n) = (BITSn(WORDn l) = l))                    %
%                                                                       %
% The output is the corresponding theorem:                              %
%                                                                       %
%     |- !w. ?l. (LENGTH l = n) /\ (WORDn l = w)                        %
% --------------------------------------------------------------------- %

let prove_WORD_onto th =
   let wth = CONJUNCT1 th in
   let w,WO,BI = (I # (dest_comb o lhs)) (dest_forall (concl wth)) in
   let lth = SPEC BI (CONJUNCT2 th) and wbth = SPEC w wth in
   let thm = CONJ (EQ_MP (SYM lth) (AP_TERM (rator BI) wbth)) wbth in
   let l = fst(dest_forall(concl (CONJUNCT2 th))) in
   let pat = mk_exists(l,subst [l,BI] (concl thm)) in
       GEN w (EXISTS (pat,BI) thm)
   ? failwith `prove_WORD_onto`;;

% --------------------------------------------------------------------- %
% prove_LENGTH_BITS_thm: prove that the BITSn function for a wordn type %
% always yields a list of length n. The input is a theorem of the form  %
% returned by define_wordn_type:                                        %
%                                                                       %
%     |- (!w. WORDn(BITSn w) = w) /\                                    %
%        (!l. (LENGTH l = n) = (BITSn(WORDn l) = l))                    %
%                                                                       %
% The output is the corresponding theorem:                              %
%                                                                       %
%     |- !w. LENGTH(BITSn w) = n                                        %
% --------------------------------------------------------------------- %

let prove_LENGTH_BITS_thm th =
    let WB,BW = CONJ_PAIR th in
    let w,Bw = (I # (rand o lhs)) (dest_forall (concl WB)) in
        GEN w (EQ_MP(SYM(SPEC Bw BW)) (AP_TERM(rator Bw)(SPEC w WB))) ? 
    failwith `prove_LENGTH_BITS_thm`;;

% --------------------------------------------------------------------- %
% prove_BITS_WORD : thm -> thm 	    					%
% takes the theorem returned by define_wordn_type			%
% returns the following:    	    					%
% |- !b0 b1 b2 b3. BITS4(WORD4[b0;b1;b2;b3]) = [b0;b1;b2;b3] 		%
% --------------------------------------------------------------------- %
let prove_BITS_WORD th =
    let w = fst(dest_forall (concl(CONJUNCT1 th))) in
    let _,wty = (dest_var w) in
    let n = int_of_string (implode(fst 
    	(partition is_digit (explode(fst(dest_type wty)))))) in
    let lst = mk_list((mk_bit_list `b` n ``), ":bool") in
    let thm1 = ((GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) (CONJUNCT2 th))
    in
    GEN_ALL (MP (SPEC lst thm1) (LENGTH_CONV "LENGTH ^lst"));;

% ===================================================================== %
% Function definitions on :wordn					%
% ===================================================================== %

begin_section prove_function_defn_thm;; 

% --------------------------------------------------------------------- %
% Internal function: REV_FORALL_CONV					%
%                                                                       %
% This conversion reverses the order of the outermost universally       %
% quantified variables of a term:                                       %
%                                                                       %
%    REV_FORALL_CONV "!x1...xn. tm"                                     %
%                                                                       %
% yields:                                                               %
%                                                                       %
%   |- (!x1...xn. tm) = (!xn...x1.tm)                                   %
% --------------------------------------------------------------------- %

let REV_FORALL_CONV tm =
    (let (v1.(v2.vs)),body = strip_forall tm in
     let rvs = rev (v1.v2.vs) in
     let rtm = list_mk_forall(rvs,body) in
     let imp1 = GENL rvs (SPECL (v1.v2.vs) (ASSUME tm)) and
         imp2 = GENL (v1.v2.vs) (SPECL rvs (ASSUME rtm)) in
         IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH rtm imp2)) ? REFL tm;;

% --------------------------------------------------------------------- %
% Internal function: LENGTH_ELIM_CONV                                   %
%                                                                       %
% If n is a natural number constant (e.g. "1", "2", etc) then:          %
%                                                                       %
%    LENGTH_ELIM_CONV "!l:(bool)list. (LENGTH l = n) ==> tm[l]"         %
%                                                                       %
% returns:                                                              %
%                                                                       %
%    |- (!l. (LENGTH l = n) ==> tm[l]) = !b0...bi. tm[[b0;...;bi]/l]    %
%                                                                       %
% where i = n-1.                                                        %
% --------------------------------------------------------------------- %

let LENGTH_ELIM_CONV =
    let Pv = "P:(bool)list->bool" and ZERO = "0" and N = "n:num" in
    let lcons = let th = theorem `list` `LENGTH_EQ_CONS` in
                SPEC N (SPEC Pv (INST_TYPE [":bool",":*"] th)) in
    let lnil  = let th = theorem `list` `LENGTH_EQ_NIL` in
                SPEC Pv (INST_TYPE [":bool",":*"] th) in
    let genvs =
        let boolty = ":bool" in
        let mkvar i = mk_primed_var(`b` ^ string_of_int i,boolty) in
        letrec gvs n i = ((i=n) => [] | mkvar i . (gvs n (i+1))) in
        \n. gvs n 0 in
    letrec bconv tm = 
      (let (l,v,bd),ar = (((I # dest_forall) o dest_abs) # I)(dest_comb tm) in
       let th = FORALL_EQ v (bconv bd) in RIGHT_BETA (AP_THM (ABS l th) ar))
      ? BETA_CONV tm in
    let substfn = 
        let v = genvar ":num" in
        \eq th. let (l,imp),r = (dest_forall # I) (dest_eq (concl th)) in
                let (len,_),c = (dest_eq # I) (dest_imp imp) in
                let lh = mk_forall(l,mk_imp(mk_eq(len,v),c)) in
                         SUBST [SYM eq,v] (mk_eq(lh,r)) th in
    letrec conv P n vs = 
       if (n=ZERO) then INST [P,Pv] lnil else
       let numc = num_CONV n in
       let pre = rand(rand(concl numc)) in
       let th1 = INST [P,Pv] (substfn numc (INST [pre,N] lcons)) in
       let l,body = dest_forall(rand(concl th1)) in
       let l',x,bdy = (I # dest_forall) (dest_abs(rator(rand body))) in
       let P' = mk_abs(l',mk_forall(hd vs,subst[hd vs,x]bdy)) in
           TRANS th1 (conv P' pre (tl vs)) in
    \tm. let l,lenl,body = (I # dest_comb) (dest_forall tm) in
         let n = rand(rand lenl) in
         let vs = genvs(int_of_string(fst(dest_const n))) in
         let lam = mk_abs(l,body) in
         let bth = AP_TERM lenl (SYM(BETA_CONV (mk_comb(lam,l)))) in
         let th = TRANS (FORALL_EQ l bth) (conv lam n vs) in
             CONV_RULE (RAND_CONV (bconv THENC REV_FORALL_CONV)) th;;

% --------------------------------------------------------------------- %
% Internal function: ELS_CONV                                           %
% 									%
% Extracts the elements of a list using HD and TL:			%
% 									%
%    ELS_CONV n "[b1;b2;...;bn]"                                        %
%                                                                       %
% returns:								%
% 									%
%    [ |- HD[b1;b2;...;bn] = b1;					%
%      |- HD(TL[b1;b2;...;bn] = b2;					%
%         :								%
%      |- HD(TL(TL ... (TL[b1;b2;...;bn] = bn ]				%
% --------------------------------------------------------------------- %

let ELS_CONV =
    let H = "h:bool" and T = "t:(bool)list" in
    let Hd = SPECL [H;T] (INST_TYPE[":bool",":*"] (definition `list` `HD`)) in
    let Tl = SPECL [H;T] (INST_TYPE[":bool",":*"] (definition `list` `TL`)) in
    let HDTL = let APHD = AP_TERM "HD:(bool)list->bool" and
                   APTL = AP_TERM "TL:(bool)list->(bool)list" in
               \th. let h,t = (rand # I)(dest_comb(rand(concl th))) in
                    let Hd = TRANS (APHD th) (INST [h,H;t,T] Hd) and
                        Tl = TRANS (APTL th) (INST [h,H;t,T] Tl) in (Hd,Tl) in
    letrec gen n th = 
       if (n=1) then [fst(HDTL th)] else
          let h,t = HDTL th in h . gen (n-1) t in
    \n l. gen n (REFL l);;

% ---------------------------------------------------------------------	%
% prove_function_defn_thm: prove a theorem stating the existence of     %
% functions defined on the component bits of an n-bit word.             %
%									%
% The input is a theorem of the form returned by define_wordn_type. The %
% output for type ":wordn" is a theorem of the form:                    %
%									%
%   |- !f. ?!fn. !b0 ... bn.  fn(WORDn [b0;...;bn]) = f b0 ... bn      	%
%									%
% The theorem is stored under the supplied name and is returned.	%
% ---------------------------------------------------------------------	%

let prove_function_defn_thm = 
    let F = "f:bool list->*" and zfn = "\l:(bool)list.(e:*)" and e = "e:*" in
    let matchfn =  MATCH_MP (theorem `wordn_base` `wordn_FN_DEF_THM`) in
    let QUANT_CONV tm = RAND_CONV(ABS_CONV tm) in
    let makefun = 
        let MKHD = curry mk_comb "HD:(bool)list->bool" and
            MKTL = curry mk_comb "TL:(bool)list->(bool)list" in
        let l = "l:(bool)list" and boolty = ":bool" and endty = ":bool->*" in
        letrec mkfn n v = 
           if (n=1) then endty,[MKHD v] else 
              let ty,args = mkfn (n-1) (MKTL v) in
                  mk_type(`fun`,[boolty;ty]),((MKHD v).args) in
        \n. let ty,args = mkfn n l in
            let f = mk_primed_var(`f`,ty) in
                f,mk_abs(l,list_mk_comb(f,args)) in
    let rconv f l n = rev_itlist (C(curry MK_COMB)) (ELS_CONV n l) (REFL f) in
    \th. (let dth = SPEC F (matchfn th) in
          let fth = CONV_RULE(QUANT_CONV LENGTH_ELIM_CONV) dth in
          let body = snd(dest_abs(rand(concl fth))) in
          let vs,leq,r = (I # dest_comb) (strip_forall body) in
          let n = length vs in
          if (n=0) then
             let inst = INST [zfn,F] fth in
                 GEN e (CONV_RULE (QUANT_CONV(RAND_CONV BETA_CONV)) inst) else
             let f,fn = makefun n in
             let th1 = BETA_CONV(mk_comb(fn,rand r)) in
             let th2 = TRANS th1 (rconv f (rand r) n) in
             let recon = itlist FORALL_EQ vs (AP_TERM leq th2) in
                 GEN f (CONV_RULE (QUANT_CONV (K recon)) (INST [fn,F] fth))) 
         ? failwith `prove_function_defn_thm`;;

% --------------------------------------------------------------------- %
% Bind the rule to "it" and export it out of the section                %
% --------------------------------------------------------------------- %
prove_function_defn_thm;;

end_section prove_function_defn_thm;; 

let prove_function_defn_thm = it;;

% ===================================================================== %
% Induction on wordn 							%
% ===================================================================== %

begin_section prove_wordn_induction_thm;;

% --------------------------------------------------------------------- %
% Internal function: UNIQUENESS						%
%									%
% This function derives uniqueness from unique existence:		%
% 									%
%        |- ?!x. P[x]							%
% --------------------------------------- 				%
%  |- !v1 v2. P[v1] /\ P[v2] ==> (v1=v2)				%
% 									%
% The variables v1 and v2 are genvars.					%
% --------------------------------------------------------------------- %

let UNIQUENESS =
    let EXISTS_UNIQUE_DEF = definition `bool` `EXISTS_UNIQUE_DEF` in
    let P = "P:*->bool" and v1 = genvar ":*" and v2 = genvar ":*" in
    let th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF) in
    let th2 = CONJUNCT2(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1)))) in
    let imp = GEN P (DISCH "$?! ^P" (SPECL [v1;v2] th2)) in
    let AND = let f = "$/\" in \(e1,e2). MK_COMB((AP_TERM f e1),e2) in
    let conv tm = AND ((BETA_CONV # BETA_CONV) (dest_conj tm)) and
        check = assert \c. (fst(dest_const c) = `?!`) and 
        v = genvar ":bool" in
    \th. let _,(x,body) = (check # dest_abs) (dest_comb (concl th)) in
         let ty = type_of x in
         let uniq = MP (SPEC(mk_abs(x,body)) (INST_TYPE [ty,":*"] imp)) th in
	 let V1,V2 = let i = inst [] [ty,":*"] in (i v1,i v2) in
	 let red = conv (fst(dest_imp(concl uniq))) in
	     GEN V1 (GEN V2(SUBST [red,v] (mk_imp(v,mk_eq(V1,V2))) uniq));;

% --------------------------------------------------------------------- %
% prove_wordn_induction_thm: prove a "degenerate" structural induction  %
% theorem for a given wordn type.  The input is a theorem of the kind   %
% returned by prove_function_defn_thm.					%
%									%
% EXAMPLE: 								%
%									%
% Input: 								%
% 									%
%   |- !f. ?!fn. !b0 ... bn.  fn(WORDn [b0;...;bn]) = f b0 ... bn      	%
% 									%
% Output:								%
% 									%
%    |- !P. (!b0...bn. P(WORDn[b0;...;bn]) ==> !w. P w			%
% 									%
% --------------------------------------------------------------------- %

let prove_wordn_induction_thm = 
    let conv =
        let RT = EQT_INTRO(REFL "T") and 
            TT = CONJUNCT1(SPEC "T" AND_CLAUSES) in
        \tm. let C,[c1;c2] = strip_comb tm in
             let vs,EQ,[l;r] = (I # strip_comb) (strip_forall c1) in
             let beta = LIST_BETA_CONV r in
             let th1 = MK_COMB (AP_TERM EQ (BETA_CONV l),beta) in
             let thm1 = GENL vs (EQT_ELIM (TRANS th1 RT)) in
             let Pl = list_mk_forall(vs, lhs(snd(strip_forall c2))) in
             let th2 = TRANS (EQT_INTRO(SPECL vs (ASSUME Pl))) (SYM beta) in
                  DISCH Pl (CONJ thm1 (GENL vs th2)) in
    let cnv ty tm =
        let w = mk_primed_var(`w`,ty) in
        let beta = SYM(BETA_CONV (mk_comb(lhs tm,w))) in
        let thm = SYM(TRANS beta (AP_THM (ASSUME tm) w)) in
            DISCH tm (GEN w (EQT_ELIM thm)) in
    \th. (let fn = fst(dest_abs(rand(snd(strip_forall(concl th))))) in
          let [ty;rty] = snd(dest_type (type_of fn)) in
          let predty = mk_type(`fun`,[ty;":bool"]) in
          let inst = INST_TYPE [":bool",rty] th in
          let P = mk_primed_var(`P`,predty) in
          let Tpred = mk_abs(mk_primed_var(`l`,ty),"T") in
          let f,fn,body = (I # (dest_abs o rand)) (dest_forall(concl inst)) in
	  let thm = SPEC P (SPEC Tpred (UNIQUENESS(SPEC f inst))) in
          let spec = INST [list_mk_abs(fst(strip_forall body),"T"),f] thm in
          let ante,conc = dest_imp(concl spec) in
              GEN P (IMP_TRANS (IMP_TRANS (conv ante) spec) (cnv ty conc))) 
         ? failwith `prove_wordn_induction_thm`;;

% --------------------------------------------------------------------- %
% Bind the function prove_wordn_induction_thm to "it", so as to export  %
% it outside the current section.					%
% --------------------------------------------------------------------- %

prove_wordn_induction_thm;; 

end_section prove_wordn_induction_thm;;

% --------------------------------------------------------------------- %
% Save the exported value of prove_wordn_induction_thm.			%
% --------------------------------------------------------------------- %

let prove_wordn_induction_thm = it;;

% ===================================================================== %
% Cases theorem for wordn types.					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% prove_wordn_cases_thm : prove a cases theorem for n-bit words.        %
%									%
% The input must be a theorem of the kind returned by the rule          %
% prove_wordn_induction_thm:					        %
%									%
%   |- !P. (!b0...bn-1. P(WORDn[b0;...;bn-1])) ==> (!w. P w)		%
%									%
% The output is a cases theorem for wordn:                              %
%									%
%   |- !w. ?b0...bn-1. w = WORDN[b0;...;bn-1]                           %
% --------------------------------------------------------------------- %

let prove_wordn_cases_thm = 
    let exfn (ev,v) th =
        let vs,leq,r = (I # dest_comb) (strip_exists (concl th)) in
        let pat = list_mk_exists (ev.vs, mk_comb(leq,subst[ev,v]r)) in
            EXISTS (pat,v) th in
    let conv tm =
        let vs,f,a = (I # dest_comb) (strip_forall tm) in
        let thm = BETA_CONV(mk_comb(f,a)) in
        let pvs = fst(strip_exists(rand(concl thm))) in
        let eth = itlist exfn (combine(pvs,vs)) (REFL a) in
            GENL vs (EQ_MP (SYM thm) eth) in
    \th. (let P,hy,c = (I # dest_imp) (dest_forall (concl th)) in
          let w = fst(dest_forall c) in 
          let vs,body = (I # rand) (strip_forall hy) in
          let eta = RAND_CONV ETA_CONV c in
          let ind = DISCH hy (EQ_MP eta (UNDISCH (SPEC P th))) in
          let pred = mk_abs(w,list_mk_exists(vs,mk_eq(w,body))) in
          let thm = INST [pred,P] ind in
              MP thm (conv (fst(dest_imp(concl thm))))) 
         ? failwith `prove_wordn_cases_thm`;;

% ---------------------------------------------------------------------	%
% Function definitions on wordn						%
% ---------------------------------------------------------------------	%

begin_section prove_wordn_fn_exists;;

% derive_wordn_existence_thm th tm					%
%									%
% If th is a wordn axiom and tm is a term giving a definition,		%
% derive an existence theorem for doing the definition.			%
% The existence theorem is suitably type-instantiated.			%
%									%
% E.g. Input								%
%									%
% |- !f. ?! fn. !b0 b1 b2 b3. fn(Word4 b0 b1 b2 b3 ) = f b0 b1 b2 b3 	%
%									%
% "FN x(Word4 a b c d)y = (x + y = 7) /\ a /\ b" 			%
%									%
% Output:								%
%									%
% |- !g1. ?fn. !g2 g3 g4 g5 g6 g7.					%
%    fn (Word4 g2 g3 g4 g5) g6 g7 = g1  g2 g3 g4 g5 g6 g7		%
%									%
% Note: the g's are genvars						%

let derive_wordn_existence_thm th tm = 
    (let var = (genvar o type_of) (fst(dest_forall(concl th))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPEC var th)) in
     let e_fn = fst(dest_exists (concl exists)) in
     letrec splt l = 
	    if (is_var (hd l)) then 
	       (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	    if (is_const (hd l) or (is_comb (hd l))) then
	       [],(hd l),(tl l) else fail in
     let bv,Con,av =splt(snd(strip_comb(lhs(snd(strip_forall tm))))) in
     let rhsfn = let cv = genvar(type_of Con) in
                 let r = rhs(snd(strip_forall tm)) in
                 list_mk_abs(cv. (bv @ av),r) in
     let th_inst = INST_TYPE (snd(match e_fn rhsfn)) exists in
     let fn = fst(dest_exists(concl th_inst)) in
     let argvars = map (genvar o type_of) (bv @ av) in
     let ap_ths th = 
         let v = map (genvar o type_of) (fst(strip_forall(concl th))) in
	 let th1 = rev_itlist (C AP_THM) argvars (SPECL v th) in
	     (GENL (v @ argvars) th1) in
     let th1 = (ap_ths (SELECT_RULE th_inst)) in
     let sel = mk_select(dest_exists (concl th_inst)) in
     GEN_ALL(EXISTS(mk_exists(fn,subst [fn,sel](concl th1)),sel)th1))?
     failwith `Can't derive existence theorem`;;

% mk_fn: make the function for the rhs of a clause in the existence thm	%
% 									%
% returns:  1) the function						%
%	    2) a list of variables that the clause should be SPECl	%
%	    3) a pre-done beta-conversion of the rhs.			%

let mk_fn (cl,(Fn,bv,C,av,r)) = 
    let lcl = hd(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let lclvars = tl(snd(strip_comb(lhs(snd(strip_forall cl))))) in
    let m = (fst(match lcl C)) @ combine((bv @ av),lclvars) in
    let cl' = subst m (snd(strip_forall cl)) in
    let nonrec = snd(strip_comb(rhs cl')) in
    let varsub = map (\v. (genvar (type_of v)),v) nonrec in
    let fn = list_mk_abs(fst(split varsub),subst varsub r) in
    let specl =  map (\v.(fst(rev_assoc v m))? v) (fst(strip_forall cl)) in
    let beta = LIST_BETA_CONV(list_mk_comb(fn,snd(strip_comb(rhs cl')))) in
        (fn,specl,beta);;

% instantiate_existence_thm eth tm : instantiate eth to match tm 	%
%									%
% E.g. INPUT:								%
%									%
% |- !g1. ?fn. !g2 g3 g4 g5 g6 g7.					%
%    fn (Word4 g2 g3 g4 g5) g6 g7 = g1  g2 g3 g4 g5 g6 g7		%
%									%
% "FN x(Word4 a b c d)y = (x + y = 7) /\ a /\ b" 			%
%									%
% OUTPUT:								%
%									%
%  |- ?fn. !a b c d x y. fn(Word4 a b c d)x y = (x + y = 7) /\ a /\ b	%

let instantiate_wordn_existence_thm eth tm = 
   (let cl = snd(strip_forall tm) in
    letrec splt l = 
	   if (is_var (hd l)) then 
	      (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	   if (is_const (hd l) or (is_comb (hd l))) then
	      [],(hd l),(tl l) else fail in
    let dest tm = 
	let ((Fn,(bv,C,av)),r)=(((I # splt) o strip_comb) # I)(dest_eq tm) in
	    (Fn,bv,C,av,r) in
    let destcl = dest cl in
    let ecl = snd(dest_exists(snd(strip_forall(concl eth)))) in
    let spfn,spec,beta = mk_fn (ecl,destcl) in
    let ethsp = SPEC spfn eth in
    let SP = SPECL spec (SELECT_RULE ethsp) in
    let rule (th1,th2) = CONV_RULE (RAND_CONV (REWR_CONV th1)) th2 in
    let th = GEN_ALL(rule(beta,SP)) in
    let fn = fst(dest_exists (concl ethsp)) and
        fsel = mk_select(dest_exists(concl ethsp)) in
        (EXISTS (mk_exists(fn,subst [fn,fsel] (concl th)),fsel) th))?
    failwith `Can't instantiate existence theorem`;;

% prove_wordn_fn_exists th tm						%
%									%
% Given 1) th, a wordn type axiom.					%
%	2) tm, the specification of a function on wordn values.		%
%									%
% proves that such a function exists.					%

% Quantify the equations of the function spec.				%
let closeup tm = 
    let lvars t = subtract
		    (freesl(snd(strip_comb(lhs(snd (strip_forall t))))))
    		    (fst(strip_forall t)) in
    list_mk_conj(map (\tm.list_mk_forall(lvars tm,tm)) (conjuncts tm));;

let prove_wordn_fn_exists th tm = 
   (let eth = derive_wordn_existence_thm th tm in
    let ith = instantiate_wordn_existence_thm eth tm in
    letrec get_avars tm  = 
	   if (is_var (rand tm)) then (get_avars (rator tm)) else
	      (snd(strip_comb (rator tm)),rand tm) in
    let cl = snd(strip_forall tm) in
    let fn = fst(strip_comb(lhs cl)) and
        av,tv = (map (genvar o type_of) # (genvar o type_of))
	        (get_avars (lhs cl)) in
    let goal = ([],mk_exists(fn,closeup tm)) in 
    let etac th = 
	let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
        EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
    let fn_beta th (A,gl) = 
 	 let efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) in
         let eabs = (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
	 let epat = list_mk_comb(eabs, map (genvar o type_of) (av @ [tv])) in
	 let tms = find_terms (\tm. can (match epat) tm) gl in
	 SUBST_TAC (map LIST_BETA_CONV tms) (A,gl) in
    GEN_ALL(TAC_PROOF(goal,
            STRIP_ASSUME_TAC ith THEN FIRST_ASSUM etac THEN
            REPEAT STRIP_TAC THEN FIRST_ASSUM fn_beta THEN
            FIRST_ASSUM MATCH_ACCEPT_TAC)))?
    failwith `Can't prove that function exists`;;

prove_wordn_fn_exists;;

end_section prove_wordn_fn_exists;;

let prove_wordn_fn_exists = it;;

%-----------------------------------------------------------------------%
% The top level user function for wordn function definitions		%
%   	    	    	    	    					%
% new_wordn_definition : (bool -> thm -> string -> conv)		%
%   infix_flag --- true if the new constant is an infix			%
%   th --- the wordn function definition theorem, returned by		%
%   	prove_function_defn_thm	    					%
%   name --- under which the definition is stored 			%
%   tm --- the definition   	    					%
%-----------------------------------------------------------------------%

let new_wordn_definition infix_flag th name tm = 
    let thm = prove_wordn_fn_exists th tm in
    new_specification name
    [(infix_flag => `infix` | `constant`),
     ((fst o dest_var o fst o dest_exists o concl) thm)] thm;;

%--------------%
