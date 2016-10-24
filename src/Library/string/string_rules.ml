% ===================================================================== %
% FILE		: string_rules.ml   				        %
% DESCRIPTION   : Defines useful derived rules for strings.		%
%									%
% 		  Assumes string.th a parent of current theory.		%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 87.10.09						%
%									%
% RENAMED	: M. Gordon (from string.ml)				%
% DATE		: 23 March 1989						%
%									%
% REVISED	: 90.10.27 (melham)					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% string_EQ_CONV : determines if two string constants are equal.	%
%									%
% string_EQ_CONV "`abc` = `abc`" ---> "(`abc` = `abc`) = T"		%
% string_EQ_CONV "`abc` = `abx`" ---> "(`abc` = `abx`) = F"		%
% string_EQ_CONV "`abc` = `ab`" ---> "(`abc` = `ab`) = F"		%
%									%
% ...  etc								%
% --------------------------------------------------------------------- %

let string_EQ_CONV = 
    let Estr = "``" and a = genvar ":ascii" and s = genvar ":string" in
    let Nth = EQF_INTRO(SPECL [a;s] (theorem `string` `NOT_STRING_EMPTY`)) in
    let pat = mk_eq(mk_eq(Estr,s),"F") and b = genvar ":bool" in
    let a' = genvar ":ascii" and s' = genvar ":string" in
    let S11 = SPECL [a;s;a';s'] (theorem `string` `STRING_11`) in
    let MKeq = let c = "$=:string->string->bool" in 
    		   \t1 t2. MK_COMB(AP_TERM c t1,t2) in
    let check c = if (fst (dest_type(type_of c)) = `string`) then
                     (let c.cs = explode(fst(dest_const c)) in 
                          c = `\`` & last cs = `\``) else false in
    let Tand = CONJUNCT1 (SPEC b AND_CLAUSES) in
    let mkC =  AP_THM o (AP_TERM "/\") in
    letrec conv l r = 
       if (l=Estr) then
          let thm = string_CONV r in
	  let A,S = (rand # I) (dest_comb (rand(concl thm))) in
    	      SUBST [SYM thm,s] pat (INST [A,a;S,s] Nth) else
       if (r=Estr) then
          let thm = string_CONV l in
	  let A,S = (rand # I) (dest_comb (rand(concl thm))) in
    	  let sth = SUBST [SYM thm,s] pat (INST [A,a;S,s] Nth) in
	      TRANS (SYM(SYM_CONV (lhs(concl sth)))) sth else
       let th1 = string_CONV l and th2 = string_CONV r in 
       let a1,s1 = (rand # I) (dest_comb(rand(concl th1))) and
           a2,s2 = (rand # I) (dest_comb(rand(concl th2))) in
       let ooth = TRANS (MKeq th1 th2) (INST [a1,a;a2,a';s1,s;s2,s'] S11) in
       if (a1=a2) then
           let thm1 = TRANS ooth (mkC(EQT_INTRO(REFL a1))(mk_eq(s1,s2))) in
	   let thm2 = TRANS thm1 (INST [mk_eq(s1,s2),b] Tand) in
	       TRANS thm2 (conv s1 s2) else
       let th1 = CONJUNCT1 (EQ_MP ooth (ASSUME (mk_eq(l,r)))) in
       let th2 = EQ_MP (ascii_EQ_CONV (mk_eq(a1,a2))) th1 in
           EQF_INTRO(NOT_INTRO(DISCH (mk_eq(l,r)) th2)) in
   \tm. (let l,r = (assert check # assert check) (dest_eq tm) in
         if (l=r) then EQT_INTRO(REFL l) else conv l r) ? 
	 failwith `string_EQ_CONV` ;;


% ----- TESTS ---
string_EQ_CONV "`a` = `b`";;
string_EQ_CONV "`abc` = `abc`";;
string_EQ_CONV "`a` = `a`";;
string_EQ_CONV "`abc` = `abx`";;
string_EQ_CONV "`abc` = `ab`";;
string_EQ_CONV "`ab` = `abc`";;
string_EQ_CONV "`xab` = `abc`";;
string_EQ_CONV "`abcdefghijklmnopqrstuvwxyz` = `abcdefghijklmnopqrstuvwxyz`";;
string_EQ_CONV "`abcdefghijklmnopqrstuvwxyz` = `abcdefghijklmnopqrstuvwxyA`";;
% --------------
