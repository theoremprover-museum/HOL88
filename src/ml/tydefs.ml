%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        tydefs.ml                                             %
%                                                                             %
%     DESCRIPTION:      Recursive type definition package                     %
%     AUTHOR:           T. F. Melham (87.08.23)                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987 1990                                %
%                                                                             %
%     REVISION HISTORY: 90.09.03                                              %
%=============================================================================%

% --------------------------------------------------------------------- %
% begin a section.							%
% --------------------------------------------------------------------- %
begin_section define_type;;

% ===================================================================== %
% Parser for input grammar               				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% ignore c = true iff c is a white space character (tab, carrage return %
% line feed, space, form feed).                                         %
% --------------------------------------------------------------------- %

let ignore c = 
    let n = ascii_code c in n=9 or n=10 or n=12 or n=13 or n=32;;

% --------------------------------------------------------------------- %
% is_sing c = true iff c is one of `#`, `+`, `|`, `(`, `)`, `,` or `=`. %
% --------------------------------------------------------------------- %

let is_sing c = c=`#` or c=`+` or c=`|` or c=`(` or c=`)` or c=`=` or c=`,`;;

% --------------------------------------------------------------------- %
% getid: strip an alphanumeric token off the front of a character list. %
% --------------------------------------------------------------------- %

letrec getid tok (c.cs) = (is_alphanum c => getid (tok ^ c) cs | (tok,c.cs));;

% --------------------------------------------------------------------- %
% getid: strip a token consisting of alphanumeric characters or `*`'s   %
% off the front of a character list. 					%
% --------------------------------------------------------------------- %

letrec gettyvid tok (c.cs) = 
       (is_alphanum c or c=`*` => gettyvid (tok ^ c) cs | (tok,c.cs));;

% --------------------------------------------------------------------- %
% gnt: get next token, where tok ::= id | tyvar | other | end           %
% --------------------------------------------------------------------- %

letrec gnt (c1.c2.cs) = 
         (ignore c1)       => gnt (c2.cs)
       | (is_sing c1)      => inr(inr(inl c1)),(c2.cs)
       | (c1 = `*`)        => ((inr o inl) # I ) (gettyvid c1 (c2.cs)) 
       | (c1=`-` & c2=`>`) => (inr(inr(inl `->`))),cs
       | (is_letter c1)    => (inl # I) (getid c1 (c2.cs))
       | (c1 = ascii 1 & c2 = ascii 1 & null cs)  => inr(inr(inr())),[]
       | failwith `illegal character: "` ^ c1 ^ `"`;;

% --------------------------------------------------------------------- %
% Recognizers for tokens                                                %
% --------------------------------------------------------------------- %

let isid      = isl and
    istyvar   = can (outl o outr) and
    is tok st = st = outl(outr(outr tok)) ? false and
    end       = can (outr o outr o outr);;

% --------------------------------------------------------------------- %
% Recognizer for type operators						%
% --------------------------------------------------------------------- %

let istyop op = (not(arity(outl op) = 0)) ? false;;

% --------------------------------------------------------------------- %
% Test for presence of closing parenthesis.				%
% --------------------------------------------------------------------- %

let ckrb tok = if (is tok `)`) then tok else failwith `missing ")"`;;

% --------------------------------------------------------------------- %
% Make a type, but issue an informative error message on error.	 	%
% --------------------------------------------------------------------- %

let mk_ty(name,tys) =
    if (is_type name) 
       then if (arity name = length tys) 
               then mk_type(name,tys) 
               else let n = string_of_int (arity name) in
                    failwith `"` ^ name ^ `" has arity ` ^ n 
       else failwith `"` ^ name ^ `" is not a type constant or operator`;;

% --------------------------------------------------------------------- %
% parse_types: parse a sequence consisting of type expressions or 	%
% instances of a special (supplied) identifier, terminated by <end> or  %
% by "|".								%
% --------------------------------------------------------------------- %

let parse_types = 

   letrec getops ty rest = 
      let tok,rem = gnt rest in
      if istyop tok then getops (mk_type(outl tok,[ty])) rem else ty,rest in

   % ------------------------------------------------------------------ %
   % <type seq> ::=  <fun type>* "|" <fun type>* <end>			%
   %									%
   % <type> ::= <fun type> | <supplied name>				%
   % ------------------------------------------------------------------ %

   letrec parse_seq name cs = 
      let tok,rest = gnt cs in
      if (end tok) then [],cs else
      if (is tok `|`) then [],rest else
      if (tok = inl name) 
         then ((curry $. (inr ())) # I) (parse_seq name rest) 
         else let ty,rest = parse_fun name cs in 
	      ((curry $. (inl ty)) # I) (parse_seq name rest)

   % ------------------------------------------------------------------ %
   % <fun type> ::= <fun type> -> <sum type> | <sum type>               %
   % ------------------------------------------------------------------ %

   and parse_fun name cs =
       let ty,rest = parse_sum name cs in
       let tok,rem = gnt rest in
       if (is tok `->`)
          then let ty2,Rem = parse_fun name rem in 
               mk_type(`fun`,[ty;ty2]),Rem
          else ty,rest 

   % ------------------------------------------------------------------ %
   % <sum type> ::= <sum type> + <prod type> | <prod type>              %
   % ------------------------------------------------------------------ %

   and parse_sum name cs =
       let ty,rest = parse_prod name cs in
       let tok,rem = gnt rest in
       if (is tok `+`) 
          then let ty2,Rem = parse_sum name rem in 
	       mk_type(`sum`,[ty;ty2]),Rem
          else ty,rest 

   % ------------------------------------------------------------------ %
   % <prod type> ::= <prod type> # <comp type> | <comp type>         	%
   % ------------------------------------------------------------------ %

   and parse_prod name cs =
       let ty,rest = parse_comp1 name cs in
       let tok,rem = gnt rest in
       if (is tok `#`)
          then let ty2,Rem = parse_prod name rem in 
               mk_type(`prod`,[ty;ty2]),Rem
          else ty,rest 

   % ------------------------------------------------------------------ %
   % <comp1 type> ::= <comp1 type> op | <basic type>           		%
   % ------------------------------------------------------------------ %

   and parse_comp1 name cs = 
       let ty,rest = parse_basic name cs in getops ty rest 

   % ------------------------------------------------------------------ %
   % <basic type> ::=   (<args>) op    					%
   %                  | (<fun type>) 					%
   %                  | <id> 						%
   %                  | <tyvar>						%
   % ------------------------------------------------------------------ %

   and parse_basic name cs =
       let tok,rest = gnt cs in
       if (is tok `(`) then
          let ty,(next,rem) = (I # gnt) (parse_fun name rest) in
          if (is next `,`) then 
             let args,opl = parse_args name rem in
             let op,Rem = (gnt o snd) ((ckrb # I) (gnt opl)) in
             if (isid op & not(op = inl name)) 
                then mk_ty(outl op,ty.args),Rem 
	        else failwith `missing tyop after "(<ty>,...,<ty>)"` else
          if (is next `)`) then ty,rem else failwith `missing ")"` else
       if (isid tok & not(tok = inl name)) then mk_ty(outl tok,[]),rest else
       if (istyvar tok) then (mk_vartype(outl(outr tok))),rest else 
       failwith `ill-formed type expression(s)`

   % ------------------------------------------------------------------ %
   % <args> ::= <fun type> , <args> | <fun type>                        %
   % ------------------------------------------------------------------ %

   and parse_args name cs =
       let ty,rest = parse_fun name cs in
       let tok,rem = gnt rest in
       if (is tok `,`) 
          then ((\l.ty.l) # I) (parse_args name rem) else [ty],rest

   in parse_seq;; 


% --------------------------------------------------------------------- %
% Parse one clause in the input grammar					%
% 									%
% Bugfix: "or (tok = inl name)" deleted in third line.   [TFM 91.02.23] %
% --------------------------------------------------------------------- %

let parse_clause after name used cs = 
    let tok,rest = gnt cs in
    if (not(isid tok)) then % or (tok = inl name)) then  [TFM 91.02.23]	%
       failwith `missing constructor name after ` ^ after else
    let con = outl tok in
    if (mem con used) then
       failwith `duplicate constructor: "` ^ con ^ `"`else
    if (is_constant con) then
       failwith `"` ^ con ^ `" is already a constant` else 
       con,(parse_types name rest);;

% --------------------------------------------------------------------- %
% Parse the clauses in the input grammar				%
% --------------------------------------------------------------------- %

letrec parse_clauses name used cs = 
   let tok,rest = gnt cs in
   if (end tok) then [] else
   let con,(args,rem) = parse_clause `"|"` name used cs in
       (con,args). parse_clauses name (con.used) rem;;

% --------------------------------------------------------------------- %
% Parse the user's input grammar					%
% --------------------------------------------------------------------- %

let parse_input = 
    let endc = ascii 1 in
    let check c = (c=endc => failwith `illegal character: "` ^ c ^ `"` | c) in
    \st. let cs = (map check (explode st)) @ [endc;endc] in
         let ty,rest = gnt cs in
         if (end ty) then failwith `empty input string` else
         if (not(isid ty)) then failwith `ill-formed name for new type` else
         let name = outl ty in
         if (is_type name) then failwith `"`^name^` " is already a type` else
         let eq,rem = gnt rest in
         if (not(is eq `=`)) then failwith `missing "=" after "`^name^`"` else
         let con,(args,clcs) = parse_clause `"="` name [] rem in
         let cls = parse_clauses name [con] clcs in
             (name,((con,args).cls));;

% ===================================================================== %
% Code for constructing the type definiton subset predicate		%
% ===================================================================== %

% --------------------------------------------------------------------- %
% pargs : split the list of argument types for a constructor (returned  %
% by parse_input) into a list of types (for non-recursve arguments) and %
% a numerical constant giving a count of the number of recursive args.  %
% 									%
% For example:								%
% 									%
% pargs [inl ":ty1";inl ":ty2";inr (); inl ":ty3"]			%
%									%
% yields  1) [":ty1";":ty2";":ty3"] (types of non recursive args)	%
%	  2) "SUC 0"		    (the no. of recursive arguments)	%
%									%
% --------------------------------------------------------------------- %

let pargs = 
    let SUC = curry mk_comb "SUC" and consf h t = h.t in
    letrec argsf n as = 
       if (null as) then ([],n) else
       (let ty = outl (hd as) in (consf ty # I) (argsf n (tl as))) ?
       argsf (SUC n) (tl as) in
    argsf "0";;

% --------------------------------------------------------------------- %
% mk_tuple_ty : make a tuple type of a list of types.			%
%									%
% Special case: if the list is empty, then the output is ":one".	%
% --------------------------------------------------------------------- %
let mk_tuple_ty = 
    let mk_prod ty1 ty2 = mk_type(`prod`,[ty1;ty2]) in
    let onety = ":one" in \l. end_itlist mk_prod l ? onety;;

% --------------------------------------------------------------------- %
% mk_tuple : make a tuple of a list of terms.				%
%									%
% Special case: if the list is empty, then the output is "one:one".	%
% --------------------------------------------------------------------- %
let mk_tuple = let onec = "one" in \l. end_itlist (curry mk_pair) l ? onec;;

% --------------------------------------------------------------------- %
% mk_sum_ty : make a tum type of a list of types.			%
% --------------------------------------------------------------------- %
let mk_sum_ty = 
    let mk_sum ty1 ty2 = mk_type(`sum`,[ty1;ty2]) in end_itlist mk_sum;;

% --------------------------------------------------------------------- %
% inject : make a list of injections of a list of values, given a sum   %
% type into which they are to be injected.				%
% 									%
% For example, if ty = (ty1,(ty2,ty3))sum and vs = [v1;v2;v3] then:	%
%									%
%     inject ty vs = [INL v1; INL(INR v2); INR(INR v3)]			%
% --------------------------------------------------------------------- %

letrec inject ty (v.vs) = 
   if (null vs) then [v] else
   let _,[lty;rty] = dest_type ty in
   let inlty = mk_type(`fun`,[lty;ty]) in
   let res = mk_comb(mk_const(`INL`,inlty),v) in
   let inrty = mk_type(`fun`,[rty;ty]) in
   let Inr = curry mk_comb (mk_const(`INR`,inrty)) in
       res.(map Inr (inject rty vs));;

% --------------------------------------------------------------------- %
% mkvars : generate sensible variable names for the arguments to the 	%
% non-recursive constructors of a newly-defined type.  A call to mkvars %
% takes the form:							%
%									%
%     mkvars [t1;...;tn]						%
%									%
% where t1,...,tn are the types required for the variables.		%
% --------------------------------------------------------------------- %

let mkvars =
    let fch ty = (hd o explode o fst o dest_type) ty ? `x` in
    let suff f c l = 
        if (f c = ``) then
           if (exists (\x. fch x = c) l) then
              `0`, \ch. (ch=c) => `0` | f ch else ``,f else
           let n = string_of_int(int_of_string(f c) + 1) in 
	       n,\ch. (ch=c) => n | f ch in
    letrec mkvs fn rvs l = 
       if (null l) then [] else
          let c = fch (hd l) in
          let s,fn' = suff fn c (tl l) in
          let v = variant rvs (mk_primed_var(c^s,hd l)) in
	      v . mkvs fn' (v.rvs) (tl l) in
    \l. mkvs (\x.``) [] l;;

% --------------------------------------------------------------------- %
% mk_subset_pred : make a subset predicate from the parse of the user's %
% input. For a full description of the form of this predicate, see:	%
%									%
% Melham, T.F.								%
% "Automating Recursive Type Definitions in Higher Order Logic",	%
% in: Current Trends in Hardware Verification and Automated 		%
% Theorem Proving, edited by G. Birtwistle and P.A. Subrahmanyam,	%
% (Springer-Verlag 1989) pp. 341-386.					%
% --------------------------------------------------------------------- %

let mk_subset_pred = 
    let boolty = ":bool" in
    let zero = let Z = "0" in \n. n = Z in
    let LEN = 
        let numty = ":num" and eq = "$=:num->num->bool" in
        \tl. let lenty = mk_type(`fun`,[type_of tl;numty]) in
	     let lentl = mk_comb(eq,mk_comb(mk_const(`LENGTH`,lenty),tl)) in
                 \n. mk_comb(lentl,n) in
    \tysl. let tys,rectys = split (map pargs tysl) in
           if (not(exists zero rectys)) then
	       failwith `no non-recursive constructor` else
           let repty = mk_sum_ty (map mk_tuple_ty tys) in
           let tlty = mk_type(`list`,[mk_type(`ltree`,[repty])]) in
           let v = mk_var(`v`,repty) and tlv = mk_var(`tl`,tlty) in
           let lens = map (LEN tlv) rectys in
           let cases = 
               if (null(tl tys)) then 
     	          (let vars = mkvars (hd tys) in
                   [list_mk_exists(vars, mk_eq(v,mk_tuple vars))]) else
                  (let vsl =  map mkvars tys in
                   let tuples = (map mk_tuple vsl) in
                   let injs = inject repty tuples in
   	           let eqs = map (curry mk_eq v) injs in
                   map list_mk_exists (combine(vsl,eqs))) in
           let body = list_mk_disj (map mk_conj (combine(cases,lens))) in
               mk_abs(v,mk_abs(tlv,body));;

% ===================================================================== %
% existence proof for the subset predicate				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% splitf : split a list at a value satisfying a given predicate.	%
% --------------------------------------------------------------------- %
letrec splitf p (x.xs) = 
   if (p x) then [],x,xs else (curry $. x # I) (splitf p xs);;

% --------------------------------------------------------------------- %
% prove_existence_thm : prove the existence theorem required for making %
% the type definition.							%
% 									%
% Given a subset predicate, pred, of the form:				%
%									%
%    \v tl. (?x1 ... xn. v = INL(x1,...,xn) /\ LENGTH tl = l1) /\       %
%	    (?x1 ... xm. v = INL(INR(x1...xm)) /\ LENGTH tl = l2)	%
%		  :							%
%	         etc							%
%									%
% this function look for a case where "LENGTH tl = 0" and then proves	%
% that |- ?r. TRP pred r  						%
%									%
% --------------------------------------------------------------------- %

let prove_existence_thm = 
    let LEN0 = CONJUNCT1 (definition `list` `LENGTH`) in
    let EXTH = theorem `tydefs` `exists_TRP` in
    let zero = let Z = "0" in \tm. tm = Z in
    let efn (nv,ov) th = 
        let vs,l,r = (I # dest_eq) (strip_exists (concl th)) in
        let pat = list_mk_exists(ov.vs,mk_eq(l,subst[ov,nv]r)) in
            EXISTS (pat,nv) th in
    \pred. let rty = hd(snd(dest_type(type_of pred))) in
           let [v;tl],cs = (I # disjuncts)(strip_abs pred) in
           let b,cl,a = splitf (zero o rand o rand) cs in
           let body = rand(rator cl) in
           let vs,val = (I # rand) (strip_exists body) in
           let nvs = map (\v. variant vs v,v) vs in
           let nval = subst nvs val in
           let veth = itlist efn nvs (REFL nval) in
           let lem = EXISTS (mk_exists(v,body),nval) veth in
	   let ltrty = mk_type(`ltree`,[rty]) in
           let cth = CONJ (ASSUME body) (INST_TYPE [ltrty,":*"] LEN0) in
           let Nil = mk_const(`NIL`,mk_type(`list`,[ltrty])) in
           let app = mk_comb(mk_comb (pred,v),Nil) in
           let beta = EXISTS_EQ v (SYM(LIST_BETA_CONV app)) in
           let thm1 = if (null a) then cth else DISJ1 cth (list_mk_disj a) in
           let thm2 = INST [Nil,tl](itlist DISJ2 b thm1) in 
           let eth = CHOOSE (v,lem) (EXISTS (lhs(concl beta),v) thm2) in
    	   let exth = SPEC pred (INST_TYPE [rty,":*"] EXTH) in
               NOT_MP exth (EQ_MP beta eth);;

% ===================================================================== %
% variant_tyvar: Find the type variable with the least number of stars	%
% that doesn't occur in the given list (for instantiating TY_DEF_THM).	%
% ===================================================================== %

letrec variant_tyvar l1 l2 = 
   let ty = mk_vartype(implode l2) in
   if (exists (\t.t=ty) l1) then variant_tyvar l1 (`*`.l2) else ty;;

% ===================================================================== %
% Procedures for cleaning up the type axiom after instantiation.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% OR_IMP_CONV: eliminate disjuncts in the antecedent of an implication. %
%									%
% Given a term "(D1 \/ ... \/ Dn) ==> C", OR_IMP_CONV returns:		%
%									%
%    |- ((D1 \/ ... \/ Dn) ==> C) = (D1 ==> C /\ ... /\ Dn ==> C)	%
% --------------------------------------------------------------------- %

let OR_IMP_CONV = 
    letrec proveimp f DS = 
       (let (D1,D2) = dest_disj DS in 
        let res = DISCH D1 (f (DISJ1 (ASSUME D1) D2)) in
            CONJ res (proveimp (f o (DISJ2 D1)) D2)) ? 
       DISCH DS (f (ASSUME DS)) in
    let disjfn th1 th2 = 
        let D = mk_disj(rand(rator(concl th1)),rand(rator(concl th2))) in
            DISCH D (DISJ_CASES (ASSUME D) (UNDISCH th1) (UNDISCH th2)) in
    \tm. let DS,C = (dest_imp tm) in
         let imp1 = DISCH tm (proveimp (MP (ASSUME tm)) DS) in
	 let rtm = snd(dest_imp(concl imp1)) in
	 let imp2 = DISCH rtm (end_itlist disjfn (CONJUNCTS(ASSUME rtm))) in
             IMP_ANTISYM_RULE imp1 imp2;;

% --------------------------------------------------------------------- %
% FORALL_IN_CONV: move two universal quantifiers into a conjunction.	%
%									%
% Given a term "!x y. C1 /\ ... /\ Cn", the conversion proves:		%
%									%
%    |- (!x y. C1 /\ ... /\ Cn) = (!x y. C1) /\ ... /\ (!x y. Cn)	%
%									%
% Note: this conversion can easily be adapted to deal with more than 	%
% two universally quantified variables by using SPECL and GENL.		%
% --------------------------------------------------------------------- %

let FORALL_IN_CONV = 
    letrec mconj f th = 
       (let th1,th2 = (f # mconj f) (CONJ_PAIR th) in CONJ th1 th2) ? f th in
    \tm. let [x;y],cs = (I # conjuncts) (strip_forall tm) in
         let spec = (SPEC y) o (SPEC x) and gen = (GEN x) o (GEN y) in 
         let imp1 = DISCH tm (mconj gen (spec (ASSUME tm))) in
         let acs = snd(dest_imp(concl imp1)) in
	 let imp2 = DISCH acs (gen (mconj spec (ASSUME acs))) in
             IMP_ANTISYM_RULE imp1 imp2;;

% --------------------------------------------------------------------- %
% CONJS_CONV : apply a given conversion to a sequence of conjuncts	%
%									%
% CONJS_CONV conv "t1 /\ t2 /\ ... /\ tn" applies conv to each of the   %
% n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the   %
% results.								%
%									%
% --------------------------------------------------------------------- %

letrec CONJS_CONV conv tm = 
       (let c,cs  = (conv # CONJS_CONV conv) (dest_conj tm) in
            MK_COMB((AP_TERM "$/\" c),cs)) ? conv tm;;

% --------------------------------------------------------------------- %
% EQN_ELIM_CONV : eliminate antecedent defining equations for the node  %
% verticies (see below).						%
%									%
% The terms in question have the form:					%
%									%
%    "!v tl. ((?x1...xn. v=tm) /\ P) ==> Q"				%
%									%
% This conversion transforms this term as follows:			%
%									%
%    |- (!v tl. ((?x1...xn. v=tm) /\ P) ==> Q)				%
%         = 								%
%       !tl. P ==> !x1...xn. Q[tm/v]					%
% 									%
% --------------------------------------------------------------------- %

let EQN_ELIM_CONV = 
    let efn (nv,ov) th = 
        let vs,(l,r) = (I # dest_eq) (strip_exists(concl th)) in
	let pat = list_mk_exists(nv.vs,mk_eq(l,subst[nv,ov]r)) in
	    EXISTS (pat,ov) th in
    let chfn fn v th = 
        let asm = ASSUME (mk_exists(v,find fn (hyp th))) in
	   CHOOSE (v,asm) th in
    \tm. let [v;tl],ANTE,Q = (I # dest_imp) (strip_forall tm) in
         let (vs,def),P = (strip_exists # I) (dest_conj ANTE) in
         let thm1 = SPEC tl (SPEC (rand def) (ASSUME tm)) in
         let goal = fst(dest_conj(fst(dest_imp(concl thm1)))) in
	 let nvs = fst(strip_exists goal) in
	 let thm2 = itlist efn (combine(nvs,vs)) (REFL (rand def)) in
	 let thm3 = DISCH P (GENL vs (MP thm1 (CONJ thm2 (ASSUME P)))) in
	 let imp1 = DISCH tm (GEN tl thm3) in
	 let res = snd(dest_imp(concl imp1)) in
	 let a1,a2 = CONJ_PAIR(ASSUME ANTE) in
	 let asm = MP (SPEC tl (ASSUME res)) a2 in
	 let thm4 = SUBST [SYM (ASSUME def),v] Q (SPECL vs asm) in
         let fn tm = lhs(snd(strip_exists tm)) = v ? false in
	 let thm5 = PROVE_HYP a1 (itlist (chfn fn) vs thm4) in
	 let imp2 = DISCH res (GEN v (GEN tl (DISCH ANTE thm5))) in
	     IMP_ANTISYM_RULE imp1 imp2;;

% --------------------------------------------------------------------- %
% LENGTH_MAP_CONV : eliminate the "LENGTH (MAP REP tl) = n" terms in	%
% favour of "LENGTH tl = n".						%
%									%
% The terms in question have the form:					%
%									%
%    "!tl. (LENGTH (MAP REP tl) = n) ==> Q"				%
%									%
% The conversion is supplied with the theorem:				%
%									%
%    |- $= LENGTH (MAP REP tl) = $= LENGTH tl				%
%									%
% and transforms the input term as follows:				%
%									%
%    |- !tl. (LENGTH (MAP REP tl) = n) ==> Q				%
%         = 								%
%       !tl. (LENGTH tl = n) ==> Q					%
% 									%
% --------------------------------------------------------------------- %

let LENGTH_MAP_CONV = 
    let IMP = "==>" in
    \eq tm. let tl,n,Q = (I # ((rand # I) o dest_imp)) (dest_forall tm) in
    	    FORALL_EQ tl (AP_THM (AP_TERM IMP (AP_THM eq n)) Q);;


% --------------------------------------------------------------------- %
% LENGTH_ELIM_CONV : Eliminate "LENGTH" expressions.                    %
%                                                                       %
% If n is a number in successor notation (e.g. "0", "SUC 0", etc) then: %
%                                                                       %
%    LENGTH_ELIM_CONV ":ty" "!l:(ty)list. (LENGTH l = n) ==> tm[l]"     %
%                                                                       %
% returns:                                                              %
%                                                                       %
%    |- (!l. (LENGTH l = n) ==> tm[l]) = !x0...xi. tm[[x0;...;xi]/l]    %
%                                                                       %
% where i = n-1, and the `x`'s have sensibly-chosen names.		%
% --------------------------------------------------------------------- %

let LENGTH_ELIM_CONV =
    let ZERO = "0" and N = "n:num" in
    let lcons = theorem `list` `LENGTH_EQ_CONS` and
        lnil  = theorem `list` `LENGTH_EQ_NIL` in
    let genvs =
        let ONE = "SUC 0" in
        let mkvar ty st i = mk_primed_var(st ^ string_of_int i,ty) in
        letrec gvs bvs ty st n i = 
            if (n=ZERO) then [] else
            let v = variant bvs (mkvar ty st i) in
                v. gvs (v.bvs) ty st (rand n) (i+1) in
        \bvs ty st n. 
           if (n=ONE) then
              let v = mk_primed_var(st,ty) in [variant bvs v] else
              gvs bvs ty st n 1 in
    let pred_ty = let bty = ":bool" in \ty. mk_type(`fun`,[ty;bty]) in
    letrec bconv tm = 
      (let (l,v,bd),ar = (((I # dest_forall) o dest_abs) # I)(dest_comb tm) in
       let th = FORALL_EQ v (bconv bd) in RIGHT_BETA (AP_THM (ABS l th) ar))
      ? BETA_CONV tm in
    letrec conv (cth,nth) Pv P n vs = 
       if (n=ZERO) then INST [P,Pv] nth else
       let pre = rand n in
       let th1 = INST [P,Pv] (INST [pre,N] cth) in
       let l,body = dest_forall(rand(concl th1)) in
       let l',x,bdy = (I # dest_forall) (dest_abs(rator(rand body))) in
       let P' = mk_abs(l',mk_forall(hd vs,subst[hd vs,x]bdy)) in
           TRANS th1 (conv (cth,nth) Pv P' pre (tl vs)) in
    \tm. let l,lenl,body = (I # dest_comb) (dest_forall tm) in
         let n = rand(rand lenl) in
         let _,[ty] = dest_type(type_of l) in
	 let (st._) = explode(fst(dest_type ty)) in
	 let bvs = fst(strip_forall body) in
         let vs = genvs bvs ty st n in
         let lam = mk_abs(l,body) in
         let bth = AP_TERM lenl (SYM(BETA_CONV (mk_comb(lam,l)))) in
         let Pv = genvar (pred_ty(type_of l)) in
         let cth = SPEC N (SPEC Pv (INST_TYPE [ty,":*"] lcons)) in
         let nth = SPEC Pv (INST_TYPE [ty,":*"] lnil) in
	 let thm1 = conv (cth,nth) Pv lam n vs in
         let thm2 = TRANS (FORALL_EQ l bth) thm1 in
             CONV_RULE (RAND_CONV bconv) thm2;;

% --------------------------------------------------------------------- %
% MAP_CONV : expand "MAP f [...]" with the definition of "MAP"		%
% --------------------------------------------------------------------- %

let MAP_CONV = 
    let mnil,mcons = CONJ_PAIR (definition `list` `MAP`) in
    letrec conv (nth,cth) tm = 
       (let _,[h;t] = strip_comb tm in
        let thm = SPEC t (SPEC h cth) in
	let cfn = rator(rand(concl thm)) in
            TRANS thm (AP_TERM cfn (conv (nth,cth) t))) ? nth in
    \tm. let _,[f;l] = strip_comb tm in conv (ISPEC f mnil, ISPEC f mcons) l;;

% --------------------------------------------------------------------- %
% ELIM_MAP_CONV : use MAP_CONV where appropriate.			%
% --------------------------------------------------------------------- %

let ELIM_MAP_CONV tm = 
    let vs,(EQ,[l;r]) = (I # strip_comb) (strip_forall tm) in
    let fn,A,Na,arg = (I # ((I # dest_comb) o dest_comb)) (dest_comb l) in
    let thm1 = AP_TERM fn (AP_TERM A (AP_TERM Na (MAP_CONV arg))) in
    let f,[a1;a2;a3] = strip_comb r in 
    let thm2 = AP_THM (AP_THM (AP_TERM f (MAP_CONV a1)) a2) a3 in
    let thm = MK_COMB (AP_TERM EQ thm1, thm2) in
        itlist FORALL_EQ vs thm;;

% --------------------------------------------------------------------- %
% TRANSFORM : transform the type axiom towards its final form:		%
%									%
%       |- !f. ?!fn. !v tl. <term>					%
%   ---------------------------------					%
%     |- ?!fn.  <transformed term>					%
% 									%
% The transformations are:						%
%									%
%  (1) two beta conversions:						%
%									%
%       "(\v tl. tm) t1 t2"      --->    "tm[t1/v,t2/tl]"		%
%									%
%  (2) eliminate the antecedent disjunction:				%
%									%
%       "D1 \/ .. \/ Dn ==> Q"   --->    "D1 ==> Q /\ .. /\ Dn ==> Q"	%
%									%
%  (3) move universally quantified vars into resulting conjunction:	%
%									%
%       "!v tl. i1 /\ .. /\ in   --->    "!v tl. i1 /\ .. /\ !v tl. in" %
%									%
%  (4) apply the transfomation given by EQN_ELIM_CONV to each conjunct. %
%									%
%  (5) transform LENGTH(MAP REP tl) into LENGTH tl (as described above) %
%									%
%  (6) eliminate "LENGTH tl = n ==> P" using LENGTH_ELIM_CONV.		%
% 									%
%  (7) expand "MAP f [...]" using the definition of MAP.		%
% 									%
% 									%
% NB: the function drops the "f", and returns it.			%
% --------------------------------------------------------------------- %

let TRANSFORM = 
    let EQ = "$=:num->num->bool" in
    let lmap = theorem `list` `LENGTH_MAP` in
    let cconv lm = EVERY_CONV [EQN_ELIM_CONV;			  % (4) %
                               LENGTH_MAP_CONV lm;		  % (5) %
	                       LENGTH_ELIM_CONV;		  % (6) %
	                       ELIM_MAP_CONV] in	          % (7) %
    \REP th. 
      let f,EU,body = (I # dest_comb) (dest_forall (concl th)) in
      let fn,[v;tl],imp = (I # strip_forall) (dest_abs body) in
      let (IMP,hy),cncl = (dest_comb # I) (dest_comb imp) in
      let beta = (RATOR_CONV BETA_CONV THENC BETA_CONV) hy in     % (1) %
      let thm1 = AP_THM (AP_TERM IMP beta) cncl in
      let red  = rand (concl thm1) in
      let thm2 = TRANS thm1 (OR_IMP_CONV red) in		  % (2) %
      let thm3 = FORALL_EQ v (FORALL_EQ tl thm2) in
      let gen  = rand (concl thm3) in
      let thm4 = TRANS thm3 (FORALL_IN_CONV gen) in	  	  % (3) %
      let cs   = rand (concl thm4) in
      let lmth = AP_TERM EQ (ISPECL [tl;REP] lmap) in
      let thm5 = TRANS thm4 (CONJS_CONV (cconv lmth) cs) in 
      let thm6 = AP_TERM EU (ABS fn thm5) in
          (f,EQ_MP thm6 (SPEC f th));;


% ===================================================================== %
% Define the constructors of the recursive type.			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% part : split a list into two parts: a list of the first n elements, 	%
% and a list of the remaining elements.					%
% --------------------------------------------------------------------- %

letrec part n l = (n=0 => [],l | (curry $. (hd l) # I) (part (n-1) (tl l)));;

% --------------------------------------------------------------------- %
% define_const : define one of the constructors for the concrete 	%
% recursive type specified by the user.  The arguments are:		%
%									%
%       c   : the constructor name 					%
%       tys : its types, as returned by parse_input			%
%	tm  : the equation for that constructor, in its current state.	%
% --------------------------------------------------------------------- %

let define_const = 
    let cfn ty n = (isl ty => n+1 | n) in
    letrec combin evs rvs tys = 
       if (null tys) then [] else
          if (isl (hd tys)) then
             hd evs . combin (tl evs) rvs (tl tys) else
             hd rvs . combin evs (tl rvs) (tl tys) in
    let mkfnty v ty = mk_type(`fun`,[type_of v;ty]) in
    let geneq uovs odvs tm = 
        let imp1 = GENL odvs (SPECL uovs (ASSUME tm)) in
        let body = concl imp1 in
        let imp2 = DISCH body (GENL uovs (SPECL odvs (ASSUME body))) in
	    IMP_ANTISYM_RULE (DISCH tm imp1) imp2 in
    \(c,tys,tm).
       let vs,(EQ,[l;r]) = (I # strip_comb) (strip_forall tm) in
       let f = fst(strip_comb r) in
       let count = itlist (\ty n. isl ty => n | n+1)  tys 0 in
       let rvs,evs = (rev # I) (part count vs) in 
       let vars = combin evs rvs tys in
       let cty = itlist mkfnty vars (type_of (rand l)) in
       let Ccomb = list_mk_comb(mk_var(c,cty),vars) in
       let def = new_definition(c^`_DEF`,mk_eq(Ccomb,rand l)) in
       let dvs = fst(strip_forall(concl def)) in
       let thm1 = AP_TERM EQ (AP_TERM (rator l) (SPECL dvs def)) in
       let thm2 = itlist FORALL_EQ dvs (SYM (AP_THM thm1 r)) in
	   (TRANS (geneq vs vars tm) thm2) ;;

% --------------------------------------------------------------------- %
% DEFINE_CONSTRUCTORS : defines the constructors for the concrete 	%
% recursive type specified by the user.  This function just maps 	%
% define_const over the conjuncts of the current theorem.		%
% --------------------------------------------------------------------- %

let DEFINE_CONSTRUCTORS = 
    let mkconj = let AND = "/\" in \t1 t2. MK_COMB(AP_TERM AND t1,t2) in
    \cs atys th.
      let EU,(fn,body) = (I # dest_abs) (dest_comb (concl th)) in
      let dcs = map define_const (combine(cs,combine(atys,conjuncts body))) in
      let thm = end_itlist mkconj dcs in
          EQ_MP (AP_TERM EU (ABS fn thm)) th;;

% ===================================================================== %
% Construct the function which applies a separate function variable to  %
% the values present on the right-hand side of each defining equation	%
% in the recursive function definition.					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% mk_tests : make the discriminator tests for each clause of the type   %
% definition theorem.  A call to:					%
%									%
%   mk_tests [x1,x2...,xn] ":ty1 + ty2 + ... + tyn"			%
%									%
% returns a variable v, and a list of tests:				%
%									%
%   [ISL v; ISL (OUTR v); ... ; ISL (OUTR ... (OUTR v)..)]		%
%									%
% where v is a genvar of type ":ty1 + ty2 + ... + tyn"			%
%									%
% --------------------------------------------------------------------- %

let mk_tests = 
    let boolty = ":bool" in
    letrec make (c.cs) v ty =
       if (null cs) then [] else
       let _,[_;outty] = dest_type ty in
       let Isl = mk_const(`ISL`,mk_type(`fun`,[ty;boolty])) in
       let Outr = mk_const(`OUTR`,mk_type(`fun`,[ty;outty])) in
       let test = mk_comb(Isl,v) and out = mk_comb(Outr,v) in
           test . make cs out outty in
    \cs ty. let v = genvar ty in v, make cs v ty;;

% --------------------------------------------------------------------- %
% mk_proj : make the projections for each clause of the type definition	%
% theorem.  A call to:							%
%									%
%   mk_proj v [x1,x2...,xn] ":ty1 + ty2 + ... + tyn"			%
%									%
% returns a list of projections:			%
%									%
%   [OUTL v; OUTL(OUTR v); ... ; OUTR (OUTR ... (OUTR v)..)]		%
%									%
% where v is a supplied genvar of type ":ty1 + ty2 + ... + tyn"		%
%									%
% --------------------------------------------------------------------- %

letrec mk_proj v (c.cs) ty = 
   if (null cs) then [v] else
      let _,[ty1;ty2] = dest_type ty in
      let Outr = mk_const(`OUTR`,mk_type(`fun`,[ty;ty2])) in
      let Outl = mk_const(`OUTL`,mk_type(`fun`,[ty;ty1])) in
      let ltm = mk_comb(Outl,v) and rtm = mk_comb(Outr,v) in
          ltm . mk_proj rtm cs ty2;;

% --------------------------------------------------------------------- %
% extract_list : generate expressions that extract the components of an	%
% object-language list.  A call to:					%
%									%
%   extract_list "(ty)list" "v:ty list" "[x1:ty;...,xn]"		%
%									%
% returns a list of terms:						%
%									%
%   ["HD v"; "HD(TL v)"; ... ; "HD(TL ... (TL v)..)"]			%
%									%
% Note: the list can be empty.						%
% --------------------------------------------------------------------- %

let extract_list ty = 
    let _,[ety] = dest_type ty in
    let Hd = mk_const(`HD`,mk_type(`fun`,[ty;ety])) in
    let Tl = mk_const(`TL`,mk_type(`fun`,[ty;ty])) in
    letrec extr Hd Tl v tm = 
       (let _,[h;t] = strip_comb tm in
        let hval = mk_comb(Hd,v) in
        let tval = mk_comb(Tl,v) in 
	hval . extr Hd Tl tval t) ? [] in
    extr Hd Tl;;

% --------------------------------------------------------------------- %
% strip_inj : strip an arbitrary number of injections off a term.  A	%
% typical call to strip_inj looks like:					%
%   									%
%   strip_inj "INR(INR(INR....(INL <val>)..)				%
%									%
% and returns <val>.							%
% --------------------------------------------------------------------- %

letrec strip_inj tm = 
   (let op,arg = ((fst o dest_const) # I) (dest_comb tm) in
    if (op = `INR` or op = `INL`) then strip_inj arg else tm) ? tm;;

% --------------------------------------------------------------------- %
% extract_tuple : generate expressions that extract the components of	%
% an object-language tuple.  A call to:					%
%									%
%   extract_tuple "ty" "v:ty" "(x1,...,xn)ty"				%
%									%
% returns a list of terms:						%
%									%
%   ["FST v"; "FST(SND v)"; ... ; "FST(SND ... (SND v)..)"]		%
%									%
% Note: the list will not be empty.					%
% --------------------------------------------------------------------- %

letrec extract_tuple ty v tm = 
   (let _,[c1;c2] = strip_comb tm in
    let _,[ty1;ty2] = dest_type ty in
    let Fst = mk_const(`FST`,mk_type(`fun`,[ty;ty1])) in
    let Snd = mk_const(`SND`,mk_type(`fun`,[ty;ty2])) in
    let fval = mk_comb(Fst,v) in
        let sval = mk_comb(Snd,v) in 
	fval . extract_tuple ty2 sval c2) ? [v];;


% --------------------------------------------------------------------- %
% gen_names : generate reasonable names for the function variables on	%
% the right-hand sides of the equations in the type axiom.  There are   %
% two kinds of names: 							%
%									%
%     `e<suffix>`    and     `f<suffix>`				%
%									%
% A name has the e-form if the corresponding "function" is just a 	%
% constant (this information is obtained from the "cs" list). Otherwise %
% the name has the f-form.  Suffixes are numerical, and are generated	%
% in the order: 0,1,2...etc.  When ef is true, however, there will be   %
% only one e-type name, for which the suffix will be empty.  Likewise	%
% for functions proper when the ff flag is true.			%
% --------------------------------------------------------------------- %

let gen_names = 
    letrec gen (ef,ff) (n,m) cs = 
       if (null cs) then [] else
       if (null (hd cs)) then
          let ename = (`e` ^ (if ef then string_of_int n else ``)) in
              ename . gen (ef,ff) (n+1,m) (tl cs) else
          let fname = (`f` ^ (if ff then string_of_int m else ``)) in
              fname . gen (ef,ff) (n,m+1) (tl cs) in
    \(ef,ff) cs. gen (ef,ff) (0,0) cs;;


% --------------------------------------------------------------------- %
% mk_fun_ty : construct a function type, given a term and the type of   %
% the expected result.							%
%									%
%   mk_fun_ty "tm:ty1" ":ty2"  =  ":ty1 -> ty2"				%
% --------------------------------------------------------------------- %

let mk_fun_ty tm ty = mk_type(`fun`,[type_of tm;ty]);;

% --------------------------------------------------------------------- %
% make_rhs : make the right-hand side for one clause of the type axiom. %
% The ty argument is the resulting type of the right-hand side. The 	%
% variables rv and tv are genvars, standing for the list of results of  %
% recursive applications of the recursive function and the subtrees,	%
% respectively. The variable pv is the result of projecting out the 	%
% tuple of non-recursive values, and the flag fl indicates if any such  %
% values are actually present (this distinguishes between a constructor %
% with a single argument of the user-specified type :one and the use of %
% ":one" to represent constant constructors).  The terms rl, val, and 	%
% tl are the right-hand side values to be extracted. The string `name`	%
% gives the function name for this right-hand side.			%
% --------------------------------------------------------------------- %

let make_rhs ty rv tv (fl,pv,name,[rl;val;tl]) = 
    let exrl = extract_list (type_of rl) rv rl in
    let extl = extract_list (type_of tl) tv tl in
    let svl = strip_inj val in
    let extu = (fl => [] | extract_tuple (type_of pv) pv svl) in
    let args = exrl @ extu @ extl in
    let v = mk_var(name,itlist mk_fun_ty args ty) in
        v,list_mk_comb(v,args);;
    
% --------------------------------------------------------------------- %
% make_conditional : make an interated conditional. A call to:		%
%									%
%    make_conditional ["t1";...;"tn"] ["x1";...;"xn+1"]			%
%									%
% returns:								%
%									%
%    "(t1 => x1 | (t2 => x2 | ... | xn+1))]"				%
%									%
% Note that n can be zero, in which case the result is "x1".		%
% --------------------------------------------------------------------- %
letrec make_conditional ts rs = 
    if (null ts) then hd rs else 
        mk_cond (hd ts,hd rs,make_conditional (tl ts) (tl rs));;

% --------------------------------------------------------------------- %
% make_function : Make the function that extracts the values present on %
% the right-hand sides of each clause, and introduces separate function %
% variables for each clause.						%
% --------------------------------------------------------------------- %

let make_function = 
    let mkflag l = not(length l = 1) in
    let nonrec l = not(exists isl l) in
    \atys th.
       let cs = conjuncts(snd(dest_abs(rand(concl th)))) in
       let ef,ff = (mkflag # mkflag) (partition null atys) in
       let names = gen_names (ef,ff) atys in
       let f,[rl;val;ts] = strip_comb (rand(snd(strip_forall(hd cs)))) in
       let _,[resty] = dest_type(type_of rl) in
       let rv = genvar (type_of rl) and tv = genvar (type_of ts) in
       let vv,tests = mk_tests names (type_of val) in
       let proj = mk_proj vv names (type_of val) in
       let vs,rs = (flat # I) (split(map ((I # rand) o strip_forall) cs)) in
       let rhss = map (snd o strip_comb) rs in
       let arg = combine(map nonrec atys,combine(proj,combine(names,rhss))) in
       let vs,res = split(map (make_rhs resty rv tv) arg) in
          (vs, list_mk_abs ([rv;vv;tv],make_conditional tests res));;

% ===================================================================== %
% Procedures for simplifying the type axiom into its final form.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% PROJ_CONV : simplify right-projections of right-injections.		%
%									%
% A call to: PROJ_CONV "OUTR(OUTR ... (INR(INR x)))" returns:		%
%									%
%   |-  OUTR(OUTR ... (INR(INR x))) = x					%
% --------------------------------------------------------------------- %

let PROJ_CONV = 
    let thm = definition `sum` `OUTR` in
    let rew = \tm. REWR_CONV thm tm ? (REFL tm) in
    letrec conv tm = 
       (let C,arg = dest_comb tm in
        if (fst(dest_const C) = `OUTR`) 
           then let th = AP_TERM C (conv arg) in
	            TRANS th (rew (rand(concl th))) 
           else REFL tm) ? REFL tm in conv;;

% --------------------------------------------------------------------- %
% TEST_SIMP_CONV : repeatedly simplify conditionals as follows:		%
%									%
%   (1)  TEST_SIMP_CONV "(ISL...(INL x)) => a | b" returns:		%
%									%
%	   |- (ISL...(INL x) => a | b) = a				%
% 									%
%   (2)  TEST_SIMP_CONV "(ISL...(INR x)) => a | b" returns:		%
%									%
%	   |- (ISL...(INR x) => a | b) = b				%
%									%
% where the dots "..." stand for any number of intermediate right	%
% projections of left injections as simplified by PROJ_CONV.		%
% --------------------------------------------------------------------- %

let TEST_SIMP_CONV = 
    let thm = definition `sum` `ISL` in
    let th1,th2 = (SPEC "x:*" # SPEC "y:**") (CONJ_PAIR thm) in
    let Tth = EQT_INTRO th1 and Fth = EQF_INTRO th2 in
    let rewconv = FIRST_CONV [REWR_CONV Fth;REWR_CONV Tth] in
    letrec conv cond = 
        (let C,[test;a;b] = strip_comb cond in
             let simp = ((RAND_CONV PROJ_CONV) THENC rewconv) test in
	     let thm2 = MK_COMB(AP_THM (AP_TERM C simp) a, conv b) in
	         CONV_RULE (RAND_CONV COND_CONV) thm2) ? REFL cond 
    in conv;;


% --------------------------------------------------------------------- %
% LIST_ELS : extract the elements of a list.				%
%									%
% Given "[x1;x2;...;xn]", LIST_ELS produces a list of theorems:		%
%									%
% [|- HD [x1;x2;...;xn]      =     x1;					%
%     HD (TL [x1;x2;...;xn]) =     x2;					%
%     ... etc ...            = xn]					%
% --------------------------------------------------------------------- %

let LIST_ELS = 
    let H = definition `list` `HD` and T = definition `list` `TL` in
    letrec genels (hth,tth) (hf,tf) th = 
       (let _,[h;t] = strip_comb(rand(concl th)) in
        let thm = TRANS (hf th) (SPEC t (SPEC h hth)) in
        let tthm = TRANS (tf th) (SPEC t (SPEC h tth)) in
            thm . genels (hth,tth) (hf,tf) tthm) ? [] in
    \tm. let lty = type_of tm in
         let _,[ty] = dest_type lty in
         let hth = INST_TYPE [ty,":*"] H and tth = INST_TYPE [ty,":*"] T in
         let hf = AP_TERM(mk_const(`HD`,mk_type(`fun`,[lty;ty]))) in
         let tf = AP_TERM(mk_const(`TL`,mk_type(`fun`,[lty;lty]))) in
             genels (hth,tth) (hf,tf) (REFL tm);;


% --------------------------------------------------------------------- %
% GEN_PROJ_CONV : generate projections of sum-injections.		%
%									%
% A call to GEN_PROJ_CONV generates a theorem that projects a value	%
% which has been injected into a sum.  For example:			%
%									%
%   PROJ_CONV "INL x"     =  |- OUTL(INL x) = x				%
%   PROJ_CONV "INR(INL x)" = |- OUTL(OUTR(INR(INL x))) = x 		%
%   ... etc.								%
% --------------------------------------------------------------------- %

let GEN_PROJ_CONV = 
    let orth = definition `sum` `OUTR` in
    let olth = definition `sum` `OUTL` in
    let inst = let v1,v2 = ":*",":**" in \t1 t2. INST_TYPE [t1,v1;t2,v2] in
    letrec conv th = 
       (let inj = rand(concl th) in
	let C,arg = dest_comb inj in
        let injty = type_of inj in
        let _,[lty;rty] = dest_type injty in
        if (fst(dest_const C) = `INR`) then
	   let proj = mk_const(`OUTR`,mk_type(`fun`,[injty;rty])) in
           let thm1 = AP_TERM proj th in
	   let thm2 = SPEC arg (inst lty rty orth) in
	       conv (TRANS thm1 thm2) else
        if (fst(dest_const C) = `INL`) then
	   let proj = mk_const(`OUTL`,mk_type(`fun`,[injty;lty])) in
           let thm1 = AP_TERM proj th in
	   let thm2 = SPEC arg (inst lty rty olth) in
	       conv (TRANS thm1 thm2) else th) ? th in
    \tm. conv (REFL tm);;

% --------------------------------------------------------------------- %
% TUPLE_COMPS : extract the components of a tuple.			%
%									%
% Given a theorem of the form:						%
%									%
%   |- tm = (x1,x2,...,xn)						%
%									%
% TUPLE_COMPS produces a list of theorems:				%
%									%
% [|- FST tm = x1;							%
%     FST(SND tm) = x2;							%
%      .								%
%      .								%
%     SND(...(SND tm)...) = xn]						%
%									%
% There are two special cases:						%
%									%
%  1) when given a theorem of the form |- tm = v, where v is a variable %
%     the function returns [|- tm = v].					%
% 									%
%  2) when given a theorem of the form |- tm = one, where one is the 	%
%     constant value of type one, the function returns [].		%
% --------------------------------------------------------------------- %

let TUPLE_COMPS = 
    letrec generate th = 
       (let _,[f;s] = strip_comb(rand(concl th)) in
        let thm1 = ISPECL [f;s] FST in
        let thm = TRANS (AP_TERM (rator(lhs(concl thm1))) th) thm1 in
        let thm2 = ISPECL [f;s] SND in 
        let tthm = TRANS (AP_TERM (rator(lhs(concl thm2))) th) thm2 in
            thm . generate tthm) ? [th] in
    let onec = "one:one" in
    \th. rand(concl th) = onec => [] | generate th;;


% --------------------------------------------------------------------- %
% SIMP_CONV : simplifies the conditional expression on the right-hand  	%
% side of an equation.							%
% --------------------------------------------------------------------- %

let SIMP_CONV = 
    let itfn th1 th2 = MK_COMB(th2,th1) in
    \tm. let vs,(Leq,r) = (I # dest_comb) (strip_forall tm) in
         let thm1 = LIST_BETA_CONV r in
         let cond = rand(concl thm1) in
         let thm2 = TRANS thm1 (TEST_SIMP_CONV cond) in
         let [l1;lab;l2] = snd(strip_comb r) in
         let eqs1 = LIST_ELS l1 and eqs3 = LIST_ELS l2 in
         let eqs2 = TUPLE_COMPS (GEN_PROJ_CONV lab) in
	 let fn = fst(strip_comb(rand(concl thm2))) in
         let thm3 = rev_itlist itfn (eqs1 @ eqs2 @ eqs3) (REFL fn) in 
	 let thm = TRANS thm2 thm3 in
             itlist FORALL_EQ vs (AP_TERM Leq thm);;

% --------------------------------------------------------------------- %
% SIMPLIFY : simplifies the type axiom into its final form.		%
% --------------------------------------------------------------------- %

let SIMPLIFY = 
    let mkconj = let AND = "/\" in \t1 t2. MK_COMB(AP_TERM AND t1,t2) in
    \th. let EU,(fn,body) = (I # dest_abs) (dest_comb (concl th)) in
         let thm = CONJS_CONV SIMP_CONV body in
             EQ_MP (AP_TERM EU (ABS fn thm)) th;;

% ===================================================================== %
% Now, the main program							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define_type: construct a user-specified concrete recursive type and   %
% derive an abstract characterization of it.				%
%									%
% E.g. define_type name `ty = C1 * | C2 ty * | C3 ty ty` defines:	%
%									%
%	1) a type operator (*)ty					%
%	2) constants C1:*->(*)ty, 					%
%		     C2:(*)ty->*->(*)ty,				%
%		     C3:(*)ty->(*)ty->(*)ty				%
%									%
% and proves that ty has the following property:			%
%									%
%	|- !f0 f1 f2. ?!fn.						%
%             (!x. fn(C1 x) = f0 x) /\					%
%             (!x t. fn(C2 t x) = f1(fn t)x t) /\              		%
%	      (!t t'. fn(C3 t t') = f2(fn t)(fn t')t t')		%
%									%
% the axiom is stored under "name" and is returned.			%
% --------------------------------------------------------------------- %

let define_type = 
    let TYDEFTHM = theorem `tydefs` `TY_DEF_THM` in
    \savename spec.
      let name,cs,atys = (I # split) (parse_input spec) in
      let isodef = name ^ `_ISO_DEF` in
      if is_axiom (current_theory(),isodef) then 	
         failwith `"` ^ isodef ^ `" already an axiom or definition` else
      let ABS = `ABS_` ^ name and REP = `REP_` ^ name in
      if (is_constant ABS) then failwith ABS ^ ` is already a constant` else
      if (is_constant REP) then failwith REP ^ ` is already a constant` else
      if can (theorem (current_theory())) savename then 
         failwith `"` ^ savename ^ `" already a theorem in current thy` else
      let pred = mk_subset_pred atys in
      let eth = prove_existence_thm pred in
      let predtm = rator(snd(dest_exists(concl eth))) in
      let tyax = new_type_definition(name, predtm, eth) in
      let ARth = define_new_type_bijections isodef ABS REP tyax in
      let rty = hd(snd(dest_type(type_of pred))) in
      let newty = hd(snd(dest_type(type_of(fst(dest_exists(concl tyax)))))) in
      let resty = variant_tyvar (type_tyvars rty) [`*`] in
      let Pthm = INST_TYPE [rty,":*";newty,":**";resty,":***"] TYDEFTHM in
      let A,R = let _,AR = dest_forall(rand(rator(concl ARth))) in
   	           (I # rator) (dest_comb(lhs AR)) in
      let Sthm = MP (SPEC pred (SPEC A (SPEC R Pthm))) ARth in
      let f,trans = TRANSFORM R Sthm in
      let defns = DEFINE_CONSTRUCTORS cs atys trans in
      let fs,funct = make_function atys defns in
      let newfs = INST [funct,f] defns in
      let abstax = GENL fs (SIMPLIFY newfs) in
          save_thm(savename,abstax);;

% --------------------------------------------------------------------- %
% Bind the value of define_type to "it".				%
% --------------------------------------------------------------------- %
define_type;;

% --------------------------------------------------------------------- %
% end the section.							%
% --------------------------------------------------------------------- %
end_section define_type;; 

% --------------------------------------------------------------------- %
% Save define_type.							%
% --------------------------------------------------------------------- %
let define_type = it;;


% ===================================================================== %
%< TESTS:

new_theory `temp`;;

let void_Axiom = define_type `void_Axiom` `void = Void`;;

let pair = define_type `pair` `pair = CONST *#**`;;

let onetest = define_type `onetest` `onetest = OOOO one`;;

let tri_Axiom =  define_type `tri_Axiom` `tri = Hi | Lo | Fl`;;

let iso_Axiom =  define_type `iso_Axiom` `iso = ISO *`;;

let List_Axiom = define_type `List_Axiom` `List = Nil | Cons * List`;;

let ty_Axiom =   
    define_type `ty_Axiom` 
	        `ty = C1 * | C2 | C3 * ** ty | C4 ty *** ty * ** | C5 ty ty`;;

define_type `bintree` `bintree = LEAF * | TREE bintree bintree`;;

define_type `seven` 
     `typ = C one one#one (one->(one->(*)list)) (*,one#one,(*)list)ty`;;

								       >%
% ===================================================================== %

