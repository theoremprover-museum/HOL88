% ===================================================================== %
% FILE		: ind-defs.ml						%
% DESCRIPTION   : inductive definitions package.			%
%									%
% AUTHOR	: (c) T. F. Melham 1990					%
% DATE		: 90.11.13						%
% REVISED	: 91.10.19						%
% ===================================================================== %

% ===================================================================== %
% INDUCTIVE DEFINITIONS.						%
% ===================================================================== %

begin_section prove_inductive_relation_exists;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION: mk_predv						%
%									%
% The function mk_predv, given a list of terms:				%
%									%
%      ["t1:ty1"; "t2:ty2"; ...; "tn:tyn"]				%
%									%
% returns a variable P of type:						%
%									%
%      P : ty1 -> ty2 -> ... -> tyn -> bool				%
%									%
% The choice of name `P` is fixed; but the variable may be primed later %
% if it is found to conflict with some other variable name present in 	%
% the rules supplied by the user.				      	%
% --------------------------------------------------------------------- %

let mk_predv = 
    let itfn tm ty = mk_type(`fun`,[type_of tm;ty]) in
    \ts. mk_var(`P`,itlist itfn ts ":bool");;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION: checkfilter 					%
%									%
% The function checkfilter takes two lists "ps" and "as", where ps is a %
% sublist of as, and returns a function from lists to list. Suppose	%
% that:									%
%									%
%    ps = [u1;...;un]    and    as = [v1;...;vm]			%
%									%
% where {u1,...,un} is a subset of {v1,...,vm}.  Then checkfilter ps as %
% is a function that takes a list					%
%									%
%   l = [w1,...,wm]							%
%									%
% and fails unless l has the same length as the list as and wi=vi for 	%
% all i such that vi is an element of ps.  If checkfilter ps as l 	%
% succeeds, then it returns the sublist of l consisting of those 	%
% elements wi for which the corresponding element vi is not in ps.	%
% --------------------------------------------------------------------- %

let checkfilter = 
    letrec check ps as = 
       if (null as) then assert null else
       let cktl = check ps (tl as) in
       if (mem (hd as) ps) 
          then let v = hd as in \(h.t). (h=v) => cktl t | fail
	  else \(h.t). h . cktl t in
    \ps as. let f = check ps as in 
            \l. f l ? failwith `ill-formed membership assertion`;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION: checkside						%
%									%
% This function is used to check that the relation R being defined does %
% not occur in a side condition of a rule. It fails with an appropriate %
% error message if R occurs free in tm and otherwise returns tm.	%
% --------------------------------------------------------------------- %

let checkside R tm =
    if (free_in R tm) then
       (let name = fst(dest_var R) in
        failwith `"` ^ name ^ `" free in side-condition(s)`) else tm;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : mk_mk_pred					%
%									%
% The arguments to this function are the user-supplied pattern pat, and	%
% the list of global parameters ps (see below for a specification of 	%
% required format of these inputs).  The pattern, pat, is expected to	%
% have the form shown below:						%
%									%
%   pat = "R x1 ... xn"							%
%									%
% and mk_mk_pred fails (with an appropriate message) if:		%
%									%
%   1: pat is not a boolean term					%
%   2: any one of R, x1, ... xn is not a variable			%
%   3: the xi's are not all distinct					%
%									%
% The second argument, ps, is a list of global parameter variables:	%
%									%
%   ["y1",...,"ym"]							%
%									%
% where {"y1",...,"ym"} is expected to be a subset of {"x1",...,"xm"}.	%
% Failure occurs if:							%
%									%
%   1: any one of "y1",...,"ym" is not a variable			%
%   2: any "yi" is not an element of {"x1",...,"xm"}.			%
%   3: the "yi"'s are not all distinct					%
%									%
% A successful call to mk_mk_pred pat ps, where the inputs pat and ps	%
% are as described above, returns a function that maps applications of  %
% the form:								%
%									%
%   "R a1 ... an"							%
%									%
% to applications of the form:						%
%									%
%   "P ai ... aj"							%
%									%
% where ai,...,aj is the subsequence of a1,...,an consisting of those   %
% arguments to R whose positions correspond to the positions of the 	%
% variables in the pattern "R x1 ... xn" that do NOT occur in the 	%
% global paramter list ps. Furthermore, at all other positions (ie at 	%
% those positions that correspond to global parameters) the a's must	%
% be identical to the parameter variables y1,...,ym.			%
%									%
% For example, if:							%
%									%
%   pat = "R x1 x2 x3 x4"   and   ps = ["x1";"x3"]			%
%									%
% then the function returned by mk_mk_pred expects input terms of the 	%
% form "R x1 a1 x3 a2" and maps these to "P a1 a2". Failure occurs if	%
% the agument to this function does not have the correct form.		%
%									%
% For convenience, the function mk_mk_pred also returns the variables	%
% R and P.								%
% --------------------------------------------------------------------- %

let mk_mk_pred = 
    let chk p = \st. \x. (p x => x | failwith st) in
    let ckb = chk (\t. type_of t = ":bool") `pattern not boolean` in
    let ckv = chk is_var `non-variable in pattern` in
    let ckp = chk is_var `non-variable parameter` in
    let itfn ck st = \v l. (mem (ck v) l => failwith st | v.l) in
    let cka = C (itlist (itfn ckv `duplicate argument in pattern`)) [] in
    let ckpa = C (itlist (itfn ckp `duplicate variable in parameters`)) [] in
    \(pat,ps,vs). 
      let R,args = (ckv # cka) (strip_comb(ckb pat)) in
      if (exists ($not o C mem args) (ckpa ps)) then
         failwith `spurious parameter variable` else
      let P = variant vs (mk_predv (subtract args ps)) in
      let checkhyp = checkfilter ps args in
          R,P,\tm.
           let f,as = strip_comb tm in
           if (f = R) then
              list_mk_comb (P, checkhyp as) else checkside R tm;;
  
% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : make_rule 					%
% 									%
% The function make_rule takes a user-supplied rule specification:	%
%									%
%   (as, c)   								%
%									%
% where as are the assumptions and side conditions and c is the 	%
% conclusion, and generates the logical representation of the assertion %
% that the relation P (supplied as one of the arguments) closed under	%
% the rule.  The variable ps is the global paramter list, and the	%
% function mkp is the mapping from membership assertions:		%
%									%
%   R a1 ... an   							%
%									%
% which occur in the assumptions as and the conclusion c, to membership %
% assertions of the form:						%
%									%
%   P ai ... aj								%
%									%
% where the global parameters in ps that occur among the arguments 	%
% a1,...,an are eliminated.  In what follows, we let mkp(c) stand for	%
% the result of this operation.						%
%									%
% For an axiom of the form ([],c), the term returned is			%
%									%
%   "!xs.mkp(c)"							%
%									%
% where xs are the variables that occur free in mkp(c). For a rule with	%
% side conditions ss and premisses p1,...,pi, the result is:		%
%									%
%   "!xs. (?zs. mkp(p1) /\ ... /\ mkp(pi) /\ ss) ==> !ys. mkp(c)	%
%									%
% where ys are the variables that appear free only in mkp(c), xz are 	%
% the variables that appear free only in mkp(p1),...,mkp(pi),ss, and xs	%
% are the remaining free variables of the rule.				%
% --------------------------------------------------------------------- %

let make_rule (P,R,ps,mkp) (as,c) = 
    if (not(fst(strip_comb c)) = R) then
       failwith `ill-formed rule conclusion` else
    let getvs tm = subtract (frees tm) (P.R.ps) in
    let con = mkp c in
    if (null as) then
        list_mk_forall(getvs con,con) else
        let asm = list_mk_conj (map mkp as) in
        let pvs = getvs asm and cvs = getvs con in
        let qcon = list_mk_forall(subtract cvs pvs, con) in
        let qasm = list_mk_exists(subtract pvs cvs, asm) in
        let avs = intersect pvs cvs in
            list_mk_forall(avs,mk_imp(qasm,qcon));;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : make_definition					%
%									%
% The function make_definition creates an appropriate non-recursive	%
% defining equation for the user-specified inducively-defined predicate %
% described by the pattern pat, the parameter list ps and the rule list %
% rules. (See below for a description of the required format of these	%
% input values).  Error checking of the user input is also done here.	%
%									%
% The rules have the form (as,c), where as are a list of premisses and 	%
% side conditions and c is the conclusion.  Each rule is transformed	%
% into the logical assertion that the relation P is closed under the 	%
% rule (see make_rule above).  Let RULES[P] be the conjunction of these %
% assertions.  Then the smallest relation closed under the rules has	%
% the defining equation:						%
%									%
%   !ps xs. REL ps xs = !P. RULES(ps)[P] ==> P xs			%
%									%
% Note that the rules may depend on the global parameters ps.		%
% --------------------------------------------------------------------- %

let make_definition (pat,ps) rules = 
    let vs = freesl (flat (map (\(x,y). y.x) rules)) in
    let R,P,mkp = mk_mk_pred (pat,ps,vs) in
    let frules = map ((flat o map conjuncts) # I) rules in
    let crules = list_mk_conj(map (make_rule (P,R,ps,mkp)) frules) in
    let right = mk_forall(P,mk_imp (crules,mkp pat)) in
    let eqn = mk_eq(pat,right) in
    let args = subtract (snd(strip_comb pat)) ps in
        list_mk_forall(ps @ args, eqn);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : derive_induction					%
%									%
% This derives rule induction from the definition of an inductively	%
% defined relation REL.							%
%									%
% The input, def, has the form:						%
%									%
%    !ps xs. REL ps xs = !P. RULES(ps)[P] ==> P xs			%
%									%
% where RULES(ps)[P] states that P is closed under the set of rules	%
% RULES(ps) and ps are the global parameters to the rules.		%
%									%
% The output is the rule induction theorem:				%
%									%
%    def |- !ps. !P. RULES(ps)[P] ==> !xs. P xs ==> REL ps xs		%
%									%
% --------------------------------------------------------------------- %

let derive_induction def = 
    let vs,(left,right) = (I # dest_eq) (strip_forall def) in
    let P,(as,con) = (I # dest_imp) (dest_forall right) in
    let rvs = snd(strip_comb con) in
    let th1 = UNDISCH (fst(EQ_IMP_RULE (SPECL vs (ASSUME def)))) in
    let th2 = GENL rvs (DISCH left (UNDISCH (SPEC P th1))) in
        GENL (subtract vs rvs) (GEN P (DISCH as th2));;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : usedef 						%
%									%
% This returns functions that use the non-recursive definition of an	%
% inductively defined relation REL to abbreviate an application of REL. %
%									%
% The input has the form:						%
%									%
%    rvs = ps...xs							%
%    dth =  |- REL ps xs = !P. RULES(ps)[P] ==> P xs			%
%									%
% where RULES(ps)[P] states that P is closed under the set of rules	%
% RULES(ps) and ps are the global parameters to the rules.		%
%									%
% The result is a pair consisting of an inference rule (type thm->thm) 	%
% and a conversion (term->thm). The conversion maps terms of the form   %
% "P vs" to the theorem:						%
%									%
%   RULES(ps)[P] |- REL ps vs ==> P vs					%
%									%
% The inference rule maps a theorem of the form:			%
%									%
%   |- !P. RULES(ps)[P] ==> P vs					%
%									%
% to the theorem:							%
%									%
%   def |- REL ps vs							%
% --------------------------------------------------------------------- %

let usedef (rvs,dth) = 
    let left,right = EQ_IMP_RULE dth in
    let ante,v = (I # (fst o dest_forall)) (dest_imp (concl left)) in 
    let lth = GENL rvs (DISCH ante (UNDISCH (SPEC v (UNDISCH left)))) in
    let as tm = SPECL (snd(strip_comb tm)) lth in
    let rth = GENL rvs right in
    let ab th = 
        let ts = snd(strip_comb(rand(snd(dest_forall(concl th))))) in
	    MP (SPECL ts rth) th in
        (ab,as);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : eximp 						%
%									%
% forward proof rule for existentially quantifying variables in both 	%
% the antecedent and consequent of an implication.			%
%									%
% A call to:  								%
%   									%
%    eximp ["v1",...,"vn"]   A |- P ==> Q				%
%									%
% returns a pair (tm,th) where:						%
%									%
%    tm = "?v1...vn. P"   and   th = A,tm |- ?v1...vn. Q		%
%									%
% --------------------------------------------------------------------- %

let eximp = 
    let exfn v th = EXISTS(mk_exists(v,concl th),v)th in
    let chfn v (a,th) = 
        let tm = mk_exists(v,a) in (tm,CHOOSE (v,ASSUME tm) th) in
    \vs th. let A,C = dest_imp(concl th) in
                itlist chfn vs (A,itlist exfn vs (UNDISCH th));;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : derive_rule 					%
%									%
% This proves that a rule holds of the inductively-defined relation REL	%
% defined by the rules.  Axioms have the form:				%
%									%
%   "!ps. REL ps <args>"						%
%									%
% and rules proper have the form					%
%									%
%   "!xs. (?zs. REL ps <args> /\ ... /\ REL ps <args> /\ ss) ==>	%
%    !ys. REL ps <args>							%
%									%
% The supplied functions ab and as embody the definition:		%
%									%
%    !ps xs. REL ps xs = !P. RULES(ps)[P] ==> P xs			%
% --------------------------------------------------------------------- %

let derive_rule =     
    let check v = assert ($not o (free_in v)) # assert (free_in v) in
    \rel (ab,as).
      let mfn tm = (free_in rel tm => as tm | DISCH tm (ASSUME tm)) in
      \th. let ([R],xs,body) = (I # strip_forall) (dest_thm th) in
           let thm1 = SPECL xs th in
           (let ante,cvs,con = (I # strip_forall) (dest_imp body) in
            let evs,asms = (I # conjuncts) (strip_exists ante) in
            let ths = map mfn asms in
            let A1,th1 = eximp evs (end_itlist IMP_CONJ ths) in
            let th3 = ab (GEN rel (DISCH R (SPECL cvs (MP thm1 th1)))) in
                GENL xs (DISCH A1 (GENL cvs th3))) ?
           GENL xs (ab (GEN rel (DISCH R thm1)));;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : derive_rules.					%
%									%
% This just constructs the arguments for derive_rule and then derives	%
% a list of all the rules.						%
% --------------------------------------------------------------------- %

let derive_rules def = 
    let vs,(left,right) = (I # dest_eq) (strip_forall def) in
    let rel,(a,c) = (I # dest_imp) (dest_forall right) in
    let rvs = subtract vs (snd(strip_comb c)) in
    let ab,as = usedef (snd(strip_comb c),SPECL vs (ASSUME def)) in
    let ths = CONJUNCTS (ASSUME a) in
    let rules = map (GENL rvs o derive_rule rel (ab,as)) ths in
        LIST_CONJ rules;;
    
% --------------------------------------------------------------------- %
% prove_inductive_relation_exists					%
%									%
% This is the main function for inductively-defined relations in HOL.   %
% The first argument is expected to be a pattern:			%
%									%
%     ("REL x1 ... xn", ["p1",...,"pn"]) 				%
%									%
% where the set of variables {p1,...,pn} is a subset of {x1,...,xn} and %
% REL is a variable standing for the relation to be defined. The second %
% argument is a list of rules of the form:				%
%									%
%     ([<premisses and side conditions>], <conclusion>)			%
%									%
% Side conditions may be abitrary boolean terms, provided they do not	%
% mention the variable REL. The premisses and conclusion of a rule must	%
% be assertions of the form:						%
%									%
%     REL t1 ... tn							%
%									%
% where each ti for which the corresponding xi in the pattern appears	%
% as an element pi in the list of global parameters is just the 	%
% parameter variable pi itself. The terms ti at other positions may be	%
% arbitrary terms.							%
%									%
% The result is a theorem stating the existence of the least relation	%
% REL closed under the rules.  This consists of a conjunction which 	%
% states (1) that REL is closed under the rules, and (2) that any other	%
% relation P which is closed under the rules contains REL.		%
% --------------------------------------------------------------------- %

let prove_inductive_relation_exists (pat,ps) rules = 
    let def = make_definition (pat,ps) rules in
    let vs,(left,right) = (I # dest_eq) (strip_forall def) in
    let R,args = strip_comb left in
    let thm1 = CONJ (derive_rules def) (derive_induction def) in
    let eth = EXISTS(mk_exists(R,concl thm1),R) thm1 in
    let lam = list_mk_abs(vs,right) in
    let bth = GENL vs (LIST_BETA_CONV (list_mk_comb(lam,vs))) in
    let deth = EXISTS (mk_exists(R,def),lam) bth in
        CHOOSE (R, deth) eth;;

% --------------------------------------------------------------------- %
% Bind this value to "it".						%
% --------------------------------------------------------------------- %

prove_inductive_relation_exists;;

% --------------------------------------------------------------------- %
% end the section.							%
% --------------------------------------------------------------------- %

end_section prove_inductive_relation_exists;;

% --------------------------------------------------------------------- %
% save the function.							%
% --------------------------------------------------------------------- %

let prove_inductive_relation_exists = it;;

% --------------------------------------------------------------------- %
% new_inductive_definition 						%
%									%
% Make a new inductive definition by first proving the existence of the %
% least relation closed under the supplied rules and then introducing	%
% a constant to denote this relation.					%
% --------------------------------------------------------------------- %

let new_inductive_definition infix st (pat,ps) rules = 
    let eth = prove_inductive_relation_exists (pat,ps) rules in
    let name = fst(dest_var(fst(dest_exists(concl eth)))) in
    let fl = (infix => `infix` | `constant`) in
    let rules,ind = CONJ_PAIR (new_specification st [fl,name] eth) in
        CONJUNCTS rules, ind;;


% ===================================================================== %
% STRONGER FORM OF INDUCTION.						%
% ===================================================================== %

begin_section strong_induction;; 

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : simp_axiom					%
%									%
% This function takes an axiom of the form				%
%									%
%    |- !xs. REL ps <args>						%
%									%
% and a term of the form						%
%									%
%    !xs. (\vs. REL ps vs /\ P vs) <args>				%
%									%
% and proves that							%
%									%
%    |- (!xs. P <args>) ==> !xs. (\vs. REL ps vs /\ P vs) <args>	%
%									%
% That is, simp_axiom essentially beta-reduces the input term, and 	%
% drops the redundant conjunct "REL ps xs", this holding merely by 	%
% virtue of the axiom being true.					%
% --------------------------------------------------------------------- %

let simp_axiom (ax,tm) =
    let vs,red = strip_forall tm in
    let bth = LIST_BETA_CONV red in
    let asm = list_mk_forall(vs,rand(rand(concl bth))) in
    let th1 = SPECL vs (ASSUME asm) in
    let th2 = EQ_MP (SYM bth) (CONJ (SPECL vs ax) th1) in
        DISCH asm (GENL vs th2);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCION : reduce_asm						%
%									%
% The term asm is expected to be the antecedent of a rule in the form:	%
% 									%
%   "?zs. ... /\ (\vs. REL ps vs /\ P vs) <args> /\ ..."		%
% 									%
% in which applications of the supplied parameter fn:			%
%									%
%   "(\vs. REL ps vs /\ P vs)"						%
% 									%
% appear as conjuncts (possibly among some side conditions).  The 	%
% function reduce_asm beta-reduces these conjuncts and flattens the 	%
% resulting conjunction of terms.  The result is the theorem:		%
%									%
%   |- asm ==> ?zs. ... /\ REL ps <args> /\ P <args> /\ ...		%
%									%
% --------------------------------------------------------------------- %

let reduce_asm =
    letrec reduce fn tm =
       (let c1,imp = (I # reduce fn) (dest_conj tm) in
        if (fst(strip_comb c1) = fn) then
           let t1,t2 = CONJ_PAIR(EQ_MP (LIST_BETA_CONV c1) (ASSUME c1)) in
           let thm1 = CONJ t1 (CONJ t2 (UNDISCH imp)) in
           let asm = mk_conj(c1,rand(rator(concl imp))) in
           let h1,h2 = CONJ_PAIR(ASSUME asm) in
               DISCH asm (PROVE_HYP h1 (PROVE_HYP h2 thm1)) else
           IMP_CONJ (DISCH c1 (ASSUME c1)) imp) ?
       if (fst(strip_comb tm) = fn) then
           fst(EQ_IMP_RULE(LIST_BETA_CONV tm)) else
           DISCH tm (ASSUME tm) in
    \fn asm. let vs,body = strip_exists asm in
             itlist EXISTS_IMP vs (reduce fn body);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : prove_asm						%
%									%
% Given the term "P" and an existentially-quantified term of the form:	%
%									%
%   "?zs. C1 /\ ... /\ P <args> /\ ... /\ Cn"				%
%									%
% prove_asm filters out those conjuncts of the form "P <args>". The 	%
% theorem returned is:							%
%									%
%   |- (?zs. C1 /\ ... /\ P <args> /\ ... /\ Cn) ==>			%
%      (?zs. C1 /\ ... /\ Cn)						%
%									%
% --------------------------------------------------------------------- %

let prove_asm P tm =
    let test t = not(fst(strip_comb(concl t)) = P) in
    let vs,body = strip_exists tm in
    let newc = LIST_CONJ(filter test (CONJUNCTS(ASSUME body))) in
        itlist EXISTS_IMP vs (DISCH body newc);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : simp_concl					%
%									%
% The argument rul is a rule of the form:				%
%									%
%   |- !xs. (?zs. REL ps <args> /\ SS) ==> REL ps <args>		%
%									%
% and the term tm will be an unsimplified term of the form:		%
% 									%
%   "!xs. (?zs. REL ps <args> /\ P <args> /\ SS) ==>			%
%         (REL ps <args> /\ P <args>)					%
%									%
% The function simp_concl proves that the first conjunct of the 	%
% antecedent of tm (i.e. REL ps <args>) is unnecessary. The result is:	%
%									%
%   |- (!xs.(?zs. REL ps <args> /\ P <args> /\ SS) ==> P <args>) ==> tm %
% --------------------------------------------------------------------- %
 
let simp_concl rul tm =
    let vs,(ante,cncl) = (I # dest_imp) (strip_forall tm) in
    let srul = SPECL vs rul in
    let (cvs,a,c) = (I # dest_conj) (strip_forall cncl) in
    let simpl = prove_asm (fst(strip_comb c)) ante in
    let thm1 = SPECL cvs (UNDISCH (IMP_TRANS simpl srul)) in
    let newasm = list_mk_forall (vs, mk_imp(ante,list_mk_forall (cvs,c))) in
    let thm2 = CONJ thm1 (SPECL cvs (UNDISCH (SPECL vs (ASSUME newasm)))) in
         DISCH newasm (GENL vs (DISCH ante (GENL cvs thm2)));;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : simp_rule						%
%									%
% This function takes a rule of the form				%
%									%
%   |- !xs. (?zs. REL ps <args> /\ SS) ==> REL ps <args>		%
%									%
% and a term of the form						%
%									%
%   "!xs (?zs. (\vs. REL ps vs /\ P vs) <args> /\ SS) ==>		%
%        (!ys. (\vs. REL ps vs /\ P vs) <args>)				%
%									%
% and proves that							%
%									%
%    |- (!xs. (?zs. REL ps <args> /\ P <args> /\ SS) ==> !ys. P <args>) %
%         ==> 								%
%       (!xs (?zs. (\vs. REL ps vs /\ P vs) <args> /\ SS) ==>		%
%            (!ys. (\vs. REL ps vs /\ P vs) <args>)			%
%									%
% That is, simp_rule essentially beta-reduces the input term and 	%
% drops the redundant conjunct "REL ps <args>" in the conclusion, as	%
% this holds by virtue of the rule itself.				%
% --------------------------------------------------------------------- %

let simp_rule (rul,tm) = 
    let vs,a,c = (I # dest_imp) (strip_forall tm) in
    let cvs,red = strip_forall c in
    let basm = reduce_asm (fst(strip_comb red)) a in    
    let bth = itlist FORALL_EQ cvs (LIST_BETA_CONV red) in
    let asm = list_mk_forall(vs,mk_imp (rand(concl basm),rand(concl bth))) in
    let thm1 = UNDISCH (IMP_TRANS basm (SPECL vs (ASSUME asm))) in
    let thm2 = DISCH asm (GENL vs (DISCH a (EQ_MP (SYM bth) thm1))) in
    let thm3 = simp_concl rul (rand(rator(concl thm2))) in
        IMP_TRANS thm3 thm2;;


% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : simp.						%
%									%
% Simplify a rule or an axiom using simp_rule or simp_axiom.		%
% --------------------------------------------------------------------- %

let simp p = simp_rule p ? simp_axiom p;;

% --------------------------------------------------------------------- %
% derive_strong_induction						%
%									%
% The induction theorem for an inductively-defined relation REL has the %
% general form:								%
%									%
%    |- !ps. !P. RULES(ps)[P] ==> !xs. P xs ==> REL ps xs		%
%									%
% where the closure of P under a rule is typically expressed as:	%
%									%
%   !xs. (?zs. P <args1> /\ ... /\ P <argsn> /\ ss) ==> !ys. P <args>	%
%									%
% The function derive_strong_induction strengthens the hypotheses of 	%
% such a rule to include the assumptions that the values <argsi> are	%
% also in the relation REL:						%
%									%
%   !xs. (?zs. REL ps <args1> /\ P <args1> /\ ... /\			%
%              REL ps <argsn> /\ P <argsn> /\ ss)			%
%        ==> !ys. P <args>						%
%									%
% ===================================================================== %

let derive_strong_induction (rules,ind) = 
    (let ps,(hy,c) = (I # dest_imp) (strip_forall (concl ind)) in
     let srules = map (SPECL (butlast ps)) rules in
     let cvs,rel,pred = (I # dest_imp) (strip_forall c) in
     let newp = list_mk_abs(cvs,mk_conj(rel,pred)) in
     let pvar,args = strip_comb pred in
     let ith = INST [newp,pvar] (SPECL ps ind) in
     let as,co = dest_imp (concl ith) in
     let bth = LIST_BETA_CONV (list_mk_comb(newp,args)) in
     let sth = CONJUNCT2 (EQ_MP bth (UNDISCH (SPECL args (ASSUME co)))) in
     let thm1 = IMP_TRANS ith (DISCH co (GENL args (DISCH rel sth))) in
     let ths = map simp (combine (srules,conjuncts as)) in
         GENL ps (IMP_TRANS (end_itlist IMP_CONJ ths) thm1)) ?
     failwith `derive_strong_induction`;;

% --------------------------------------------------------------------- %
% Bind derive_strong_induction to "it".				%
% --------------------------------------------------------------------- %

derive_strong_induction;; 

% --------------------------------------------------------------------- %
% end of section.							%
% --------------------------------------------------------------------- %

end_section strong_induction;;

% --------------------------------------------------------------------- %
% Save the exported value.						%
% --------------------------------------------------------------------- %

let derive_strong_induction = it;;


% ===================================================================== %
% RULE INDUCTION 							%
% ===================================================================== %

begin_section RULE_INDUCT_THEN;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : TACF						%
%									%
% TACF is used to generate the subgoals for each case in an inductive 	%
% proof.  The argument tm is formula which states one case in the 	%
% the induction. In general, this will take one of the forms:		%
%									%
%   (1) no side condition, no assumptions:				%
%									%
%       tm = !xs. P <args>						%
%									%
%   (2) side condition and/or assumptions:				%
%      									%
%       tm = !xs. (?zs. P <args> /\ SS) ==> !ys. P <args>		%
%									%
% When TACF is applied to tm, a parameterized tactic is returned which	%
% will later be applied to the corresponding subgoal in an induction.   %
% The resulting tactic takes two theorem continuations as arguments.    %
% For a base case, like case 1 above, the resulting tactic just throws	%
% these parameters away and passes the goal on unchanged:		%
%									%
%    \ttac1 ttac2. ALL_TAC						%
%									%
% For a step case, like case 2, the tactic applies GEN_TAC to strip off %
% the xs. It then strips off and breaks into conjuncts the induction	%
% hypotheses.  The theorem continuation ttac1 is then applied to the	%
% premisses and the theorem continuation ttac2 applied to the side 	%
% conditions.								%
%									%
% The implementation of TTAC uses three auxiliary functions, namely	%
% MK_CONJ_THEN, MK_CHOOSE_THEN and MK_THEN for stripping down the 	%
% existentially-quantified conjunction of induction hypotheses.		%
% --------------------------------------------------------------------- %

letrec MK_CONJ_THEN fn tm =
   (let c1,c2 = dest_conj tm in
    let tcl1 = (fst(strip_comb c1) = fn) => \t1 t2. t1 | \t1 t2. t2 in
    let tcl2 = MK_CONJ_THEN fn c2 in
    \ttac1 ttac2. CONJUNCTS_THEN2 (tcl1 ttac1 ttac2) (tcl2 ttac1 ttac2)) ?
   if (fst(strip_comb tm) = fn) then K else C K;;

letrec MK_CHOOSE_THEN fn vs body =
   if (null vs) then MK_CONJ_THEN fn body else
   let tcl = MK_CHOOSE_THEN fn (tl vs) body in
       \ttac1 ttac2. CHOOSE_THEN (tcl ttac1 ttac2);;

let MK_THEN fn tm =
    let vs,body = strip_exists tm in
    if (free_in fn body) then
       MK_CHOOSE_THEN fn vs body else
       \ttac1 ttac2. ttac2;;

let TACF fn tm = 
    let vs,body = strip_forall tm in
    if (is_imp body) then        
       let TTAC = MK_THEN fn (fst(dest_imp body)) in
        \ttac1 ttac2. REPEAT GEN_TAC THEN DISCH_THEN (TTAC ttac1 ttac2) else
        \ttac1 ttac2. ALL_TAC;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : TACS						%
%									%
% TACS uses TACF to generate a parameterized list of tactics, one for   %
% each conjunct in the hypothesis of an induction theorem. If tm is the %
% conjunction of cases for an induction theorem:			%
%									%
%   "RULE1 /\ ... /\ RULEn"						%
% 									%
% then TACS tm yields the paremterized list of tactics:			%
%									%
%   \ttac1 ttac2.							%
%      [TACF "RULE1" ttac1 ttac2; ...; TACF "RULEn" ttac1 ttac2]	%
%									%
% Where the applications TACF "RULEi" have been pre-evaluated.		%
% --------------------------------------------------------------------- %

letrec TACS fn tm = 
   let cf,csf = ((TACF fn # TACS fn) (dest_conj tm) ? TACF fn tm,(\x y.[])) in
       \ttac1 ttac2. (cf ttac1 ttac2) . (csf ttac1 ttac2);;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : mkred						%
%									%
% This produces a conversion that selectively beta-reduces the terms in	%
% a conjunction.  Evaluating:						%
%									%
%   mkred "f" ["c1";...;"cn"]						%
% 									%
% produces a conversion that applies LIST_BETA_CONV to the conjuncts 	%
% Ci in a term of the form:						%
%									%
%  "C1 /\ ... /\ Cn"							%
%									%
% for which the corresponding "ci" is of the form "f x1 ... xn".	%
% --------------------------------------------------------------------- %

letrec mkred fn (c.cs) =
   (let cfn = (fst(strip_comb c) = fn) => LIST_BETA_CONV | REFL in
    if (null cs) then cfn else
       let rest = mkred fn cs in
       \tm. let c1,c2 = dest_conj tm in
            MK_COMB(AP_TERM cnj (cfn c1),rest c2))
   where cnj = "/\";;


% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : RED_CASE.						%
%									%
% Given the argument "fn" and a term corresponding to one of the rules  %
%									%
%   !xs. (?zs. fn <args> /\ ... /\ SS) ==> !ys. fn <args>		%
%									%
% RED_CASE produces a conversion that will apply LIST_BETA_CONV to	%
% instances of this term at the positions which correspond to 		%
% applications of fn to <args>.						%
% --------------------------------------------------------------------- %

let RED_CASE = 
    let imp = "==>" in
    \fn pat. let bdy = snd(strip_forall pat) in
        if (is_imp bdy) then
           let ante = fst(dest_imp bdy) in
           let hyps = conjuncts(snd(strip_exists(ante))) in
           let redf = mkred fn hyps in
           \tm. let vs,ant,con = (I # dest_imp) (strip_forall tm) in
                let cvs,red = strip_forall con in
                let th1 =  itlist FORALL_EQ cvs (LIST_BETA_CONV red) in
                let evs,hyp = strip_exists ant in
                let th2 = itlist EXISTS_EQ evs (redf hyp) in
                itlist FORALL_EQ vs (MK_COMB(AP_TERM imp th2,th1)) else
           \tm. let vs,con = strip_forall tm in
                itlist FORALL_EQ vs (LIST_BETA_CONV con);;


% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : APPLY_CASE 					%
%									%
% Given a list of conversions [f1;...;fn], APPLY_CASE produces a 	%
% conversion that applies fi to conjunct Ci in a term of the form:	%
%									%
%  "C1 /\ ... /\ Cn"							%
%									%
% The result is |- (C1 /\ ... /\ Cn) = (^(f C1) /\ ... /\ ^(f Cn))	%
% --------------------------------------------------------------------- %

letrec APPLY_CASE (f.fs) tm =
   (if (null fs) then f tm else
    let c1,c2 = dest_conj tm in
        MK_COMB (AP_TERM cnj (f c1),APPLY_CASE fs c2)) 
   where cnj = "/\";;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : RED_WHERE						%
%									%
% Given the argument "P" and a term corresponding to the statement of 	%
% rule induction:							%
%									%
%   RULES(ps)[P] ==> R ps vs ==> P vs					%
%									%
% RED_WHERE produces a conversion that will apply LIST_BETA_CONV to	%
% instances of this term at the positions which correspond to 		%
% applications of P.							%
% --------------------------------------------------------------------- %

let RED_WHERE fn body =
    let cs,con = (conjuncts # I) (dest_imp body) in
    let rfns = map (RED_CASE fn) cs in
    \stm. let a,c = dest_imp stm in
          let hthm = APPLY_CASE rfns a in
          let cthm = RAND_CONV LIST_BETA_CONV c in
          MK_COMB(AP_TERM "==>" hthm,cthm);;
    
% --------------------------------------------------------------------- %
% RULE_INDUCT_THEN : general rule induction tactic.			%
% 									%
% The first theorem continuation is for premisses and the second is for	%
% side conditions.							%
% --------------------------------------------------------------------- %

let is_param icvs slis arg = 
    let val = snd (assoc arg slis) ? arg in mem val icvs;;

let RULE_INDUCT_THEN th : (thm->tactic) -> (thm->tactic) -> tactic = 
    (let vs,(hy,con) = (I # dest_imp) (strip_forall (concl th)) in
     let cvs,cncl = strip_forall con in
     let thm = DISCH hy (SPECL cvs(UNDISCH(SPECL vs th))) in
     let pvar = genvar (type_of (last vs)) in
     let sthm = INST [pvar,last vs] thm in
     let RED = RED_WHERE (last vs) (mk_imp(hy,cncl)) in
     let tacs = TACS (last vs) hy in
     (\ttac1 ttac2 (A,g).
        (let gvs,body = strip_forall g in
         let slis,ilis = match (rator cncl) (rator body) in
	 let sith = INST_TY_TERM (slis,ilis) sthm in
	 let largs = snd(strip_comb (rand(rator body))) in
	 let icvs = map (inst [] ilis) cvs in
	 let params = filter (is_param icvs slis) largs in
	 let lam = list_mk_abs(params,rand body) in
         let spth = INST [lam,inst [] ilis pvar] sith in
	 let spec = GENL gvs (UNDISCH (CONV_RULE RED spth)) in
	 let subgls = map (pair A) (conjuncts (hd(hyp spec))) in
	 let tactic g = subgls,\ths.  PROVE_HYP (LIST_CONJ ths) spec in
             (tactic THENL (tacs ttac1 ttac2)) (A,g)) ? 
         failwith `RULE_INDUCT_THEN: inappropriate goal`)) ?
     failwith `RULE_INDUCT_THEN: ill-formed rule induction theorem`;;

% --------------------------------------------------------------------- %
% Bind RULE_INDUCT_THEN to "it".					%
% --------------------------------------------------------------------- %

RULE_INDUCT_THEN;; 

% --------------------------------------------------------------------- %
% end of section.							%
% --------------------------------------------------------------------- %

end_section RULE_INDUCT_THEN;;

% --------------------------------------------------------------------- %
% Save the exported value.						%
% --------------------------------------------------------------------- %

let RULE_INDUCT_THEN = it;;

% ===================================================================== %
% TACTICS FROM THEOREMS THAT STATE RULES.				%
% ===================================================================== %

begin_section RULE_TAC;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : axiom_tac 					%
%									%
% This function maps an axiom of the form:				%
%									%
%    |- R ps <args>							%
%									%
% to a tactic:								%
%									%
%             ---							%
%  ===========================						%
%   A ?- !xs. R <ps> <args'>						%
%									%
% where <ps> is an instance of ps, and <args'> an instance of <args>.	%
% --------------------------------------------------------------------- %

let axiom_tac th : tactic (A,g) = 
    (let vs,body = strip_forall g in
     let instl = match (concl th) body in
         [], K (itlist ADD_ASSUM A (GENL vs (INST_TY_TERM instl th)))) ? 
    failwith `RULE_TAC : axiom does not match goal`;;
   
% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : prove_conj					%
%									%
% Given a list of theorems [|- C1; ...; |- Cn] and a conjunction	%
%									%
%    "c1 /\ ... /\ cm"							%
%									%
% this function proves |- (c1 /\ ... /\ cm) provided each ci is equal	%
% to some Ci.								%
% --------------------------------------------------------------------- %

letrec prove_conj ths tm = 
   uncurry CONJ ((prove_conj ths # prove_conj ths) (dest_conj tm)) ? 
   find (curry $= tm o concl) ths;;
 
% --------------------------------------------------------------------- %
% RULE_TAC : maps a theorem stating a rule to a tactic.			%
% --------------------------------------------------------------------- %

let RULE_TAC : thm -> tactic = 
    let mkg A vs c = A,list_mk_forall(vs,c) in
    \th. (let vs,rule = strip_forall(concl th) in
          (let asm,cvs,cncl = (I # strip_forall) (dest_imp rule) in 
           let ith = DISCH asm (SPECL cvs (UNDISCH (SPECL vs th))) in
           \(A,g). 
            (let gvs,body = strip_forall g in
             let slis,ilis = match cncl body in
             let th1 = INST_TY_TERM (slis,ilis) ith in
 	     let svs = freesl (map (subst slis o inst [] ilis) vs) in
             let nvs = intersect gvs svs in
             let ante = fst(dest_imp(concl th1)) in
             let newgs = map (mkg A nvs) (conjuncts ante) in
     	         newgs, 
                 \thl. let ths = map (SPECL nvs o ASSUME o snd) newgs in
  	               let th2 = GENL gvs (MP th1 (prove_conj ths ante)) in
                           itlist PROVE_HYP thl th2) ? 
            failwith `RULE_TAC : rule does not match goal`) ?
          axiom_tac (SPECL vs th)) ? 
         failwith `RULE_TAC: ill-formed input theorem`;;

% --------------------------------------------------------------------- %
% Bind this value to "it".						%
% --------------------------------------------------------------------- %

RULE_TAC;;

% --------------------------------------------------------------------- %
% end the section.							%
% --------------------------------------------------------------------- %

end_section RULE_TAC;; 

% --------------------------------------------------------------------- %
% save the function.							%
% --------------------------------------------------------------------- %

let RULE_TAC = it;;

% ===================================================================== %
% REDUCTION OF A CONJUNCTION OF EQUATIONS.				%
% ===================================================================== %

begin_section REDUCE;;

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : reduce 						%
% 									%
% A call to 								%
%									%
%   reduce [v1;...;vn] ths [] []					%
%									%
% reduces the list of theorems ths to an equivalent list by removing 	%
% theorems of the form |- vi = ti where vi does not occur free in ti,   %
% first using this equation to substitute ti for vi in all the other	%
% theorems. The theorems in ths are processed sequentially, so for 	%
% example:								%
%									%
%   reduce [a;b] [|- a=1; |- b=a+2; |- c=a+b] [] []			%
%									%
% is reduced in the following stages:					%
%									%
%   [|- a=1; |- b=a+2; |- c=a+b]					%
%   									%
%   ===> [|- b=1+2; |- c=1+b]      (by the substitution [1/a])		%
%   ===> [|- c=1+(1+2)]            (by the substitution [1+2/b])	%
%									%
% The function returns the reduced list of theorems, paired with a list %
% of the substitutions that were made, in reverse order.  The result 	%
% for the above example would be [|- c = 1+(1+2)],[("1+2",b);("1",a)].	%
% --------------------------------------------------------------------- %

letrec reduce vs ths res sub =
   if (null ths) then (rev res, sub) else
   (let l,r = dest_eq(concl(hd ths)) in
    let sth,pai = mem l vs => hd ths,(r,l) |
                  mem r vs => SYM(hd ths),(l,r) | fail in
    if free_in (snd pai) (fst pai) then fail else
    let sfn = map (SUBS [sth]) in
    let ssfn = map \(x,y). (subst [pai] x),y in
        reduce vs (sfn (tl ths)) (sfn res) (pai . ssfn sub)) ? 
    (reduce vs (tl ths) (hd ths . res) sub);;

% --------------------------------------------------------------------- %
% REDUCE : simplify an existentially quantified conjuction by		%
% eliminating conjuncts of the form |- v=t, where v is among the 	%
% quantified variables and v does not appear free in t. For example 	%
% suppose:								%
% 									%
%   tm = "?vi. ?vs. C1 /\ ... /\ v = t /\ ... /\ Cn"			%
%									%
% then the result is:							%
%									%
%   |- (?vi. ?vs. C1 /\ ... /\ vi = ti /\ ... /\ Cn)			%
%          =								%
%      (?vs. C1[ti/vi] /\ ... /\ Cn[ti/vi])				%
%									%
% The equations vi = ti can appear as ti = vi, and all eliminable 	%
% equations are eliminated.  Fails unless there is at least one		%
% eliminable equation. Also flattens conjuncts. Reduces term to "T" if	%
% all variables eliminable.						%
% --------------------------------------------------------------------- %

let REDUCE =
    let chfn v (a,th) =
      let tm = mk_exists(v,a) in
      let th' =
          if (free_in v (concl th))
            then EXISTS (mk_exists(v,concl th),v) th else th in
         (tm,CHOOSE (v,ASSUME tm) th') in
    let efn ss v (pat,th) =
        let wit = fst(rev_assoc v ss) ? v in
        let epat = subst ss (mk_exists(v,pat)) in
            (mk_exists(v,pat),EXISTS(epat,wit) th) in
    letrec prove ths cs =
        (uncurry CONJ ((prove ths # prove ths) (dest_conj cs))) ? 
        (find (\t. concl t = cs) ths) ?
        (REFL (rand cs)) in
    \tm. let vs,cs = strip_exists tm in
         let rem,ss = reduce vs (CONJUNCTS (ASSUME cs)) [] [] in
         if (null ss) then failwith `REDUCE` else
         let th1 = LIST_CONJ rem ? TRUTH in
         let th2 = (uncurry DISCH) (itlist chfn vs (cs,th1)) in
         let rvs,rcs = strip_exists(rand(concl th2)) in
         let eqt = subst ss cs in
         let th3 = prove (CONJUNCTS (ASSUME rcs)) eqt in
         let _,th4 = itlist (efn ss) vs (cs,th3) in
         let th5 = (uncurry DISCH) (itlist chfn rvs (rcs,th4)) in
             IMP_ANTISYM_RULE th2 th5;;


% --------------------------------------------------------------------- %
% Bind this value to "it".						%
% --------------------------------------------------------------------- %

REDUCE;;

% --------------------------------------------------------------------- %
% end the section.							%
% --------------------------------------------------------------------- %

end_section REDUCE;;

% --------------------------------------------------------------------- %
% save the function.							%
% --------------------------------------------------------------------- %

let REDUCE = it;;


% ===================================================================== %
% CASES THEOREM								%
% ===================================================================== %

begin_section derive_cases_thm;; 

% --------------------------------------------------------------------- %
% INTERNAL FUNCTION : LIST_NOT_FORALL					%
%                                                                       %
% If:                                                                   %
%             |- ~P                                                     %
%        --------------- f : thm->thm                                   %
%         |- Q  |- R                                                    %
%                                                                       %
% Then:                                                                 %
%                                                                       %
%   |-  ~!x1 ... xi. P                                                  %
%  ----------------------------                                         %
%   |-  ?x1 ... xi. Q    |- R                                           % 
% --------------------------------------------------------------------- %

let LIST_NOT_FORALL =
    let efn v th =  EXISTS(mk_exists(v,concl th),v) th in
    \f th. let vs,body = strip_forall (dest_neg (concl th)) in
           if (null vs) then f th else
           let Q,R = f (ASSUME(mk_neg body)) in
           let nott = itlist efn vs Q in
           let thm = CCONTR body (MP (ASSUME (mk_neg (concl nott))) nott) in
               CCONTR (concl nott) (MP th (GENL vs thm)), R;;

% --------------------------------------------------------------------- %
% simp_axiom: simplify the body of an axiom.                            %
% --------------------------------------------------------------------- %

let simp_axiom sfn vs ax th =
    (let rbody = LIST_BETA_CONV (dest_neg(concl th)) in
    let fth = MP th (EQ_MP (SYM rbody) (ASSUME (rand (concl rbody)))) in
    let imp = PROVE_HYP th (CCONTR (dest_neg(rand(concl rbody))) fth) in
    let ante,eqs = (I # conjuncts) (dest_imp(concl imp)) in
    let avs,res = strip_forall (concl ax) in
    let inst = INST (fst(match res ante)) (SPECL avs ax) in
    let ths = MP imp inst in
    let thm = sfn (ASSUME(concl ths)) inst in
    let rth = (uncurry DISCH) (itlist chfn vs ((concl ths),thm)) in
        (ths,rth)) where
    chfn v (a,th) = let tm = mk_exists(v,a) in (tm,CHOOSE (v,ASSUME tm) th);;

% --------------------------------------------------------------------- %
% crul rel th : beta-reduce and simplify if rel is free in th		%
%									%
%  |- (\xs. ~(P ==> Q)) ts						%
% -------------------------- crul rel th				%
%       |- P[ts/xs]							%
% --------------------------------------------------------------------- %

let crul rel th =
    if (free_in rel (concl th)) then
       let th1 = CONV_RULE LIST_BETA_CONV th in
       CONJUNCT1 (CONV_RULE (REWR_CONV NOT_IMP) th1) else th;;

% --------------------------------------------------------------------- %
% CONJ_RUL : chain through conjunction.					%
%                                                                       %
% If:                                                                   %
%                                                                       %
%        |- Pi                                                          %
%   -------------- (crul rel) 						%
%        |- Qi                                                          %
%                                                                       %
% then:                                                                 %
%                                                                       %
%    |- P1 /\ ... /\ Pj							%
%  --------------------- CONJ_RUL rel					%
%    |- P1 /\ ... /\ Qj							%
% --------------------------------------------------------------------- %

letrec CONJ_RUL rel th =
    (uncurry CONJ ((crul rel # CONJ_RUL rel) (CONJ_PAIR th))) ? crul rel th;;

% --------------------------------------------------------------------- %
% LIST_EXIST_THEN : chain through exists.				%
%                                                                       %
% If:                                                                   %
%                                                                       %
%        |- P                                                           %
%   ------------- f 							%
%        |- Q                                                           %
%                                                                       %
% then:                                                                 %
%                                                                       %
%    |- ?x1...xi. P                                                     %
%  --------------------- LIST_EXISTS_THEN f				%
%    |- ?x1...xi. Q                                                    	%
% --------------------------------------------------------------------- %

let LIST_EXISTS_THEN f th =
    let vs,body = strip_exists(concl th) in
    let th1 = DISCH body (f (ASSUME body)) in
        MP (itlist EXISTS_IMP vs th1) th;;

% --------------------------------------------------------------------- %
% RULE									%
%                                                                       %
%           |- !xs. p xs 						%
% --------------------------------- RULE |- ?xs. p xs => q xs    	%
%           |- ?xs. q xs   						%
% --------------------------------------------------------------------- %

let RULE thm1 thm2 =
    let xs,imp = strip_exists (concl thm1) in
    let thm =  SPECL xs thm2 in
    let impth = MP (ASSUME imp) thm in
    let iimp = DISCH imp impth in
        MATCH_MP (itlist EXISTS_IMP xs iimp) thm1;;

% --------------------------------------------------------------------- %
% EXISTS_IMP : existentially quantify the antecedent and conclusion 	%
% of an implication.							%
%									%
%        A |- P ==> Q							%
% -------------------------- EXISTS_IMP "x"				%
%   A |- (?x.P) ==> (?x.Q)						%
%									%
% LIKE built-in, but doesn't quantify in Q if not free there.		%
% Actually, used only in context where x not free in Q.			%
% --------------------------------------------------------------------- %

let EXISTS_IMP2 x th =
    let ante,cncl = dest_imp(concl th) in
    if (free_in x cncl) then
       let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
       let asm = mk_exists(x,ante) in
            DISCH asm (CHOOSE (x,ASSUME asm) th1) else
       let asm = mk_exists(x,ante) in
           DISCH asm (CHOOSE (x,ASSUME asm) (UNDISCH th));;

% --------------------------------------------------------------------- %
% |- ?xs. P  |- ?ys. Q ===> ?xs ys. P /\ Q 				%
% [Primes the ys if necessary.]						%
% --------------------------------------------------------------------- %
let efn v th =
    if free_in v (concl th) 
       then EXISTS(mk_exists(v,concl th),v) th
       else th;;

let RULE2 vs thm1 thm2 =
    let xs,P = strip_exists(concl thm1) in
    let ys,Q = strip_exists(concl thm2) in
    let itfn = \v vs. let v' = variant (vs @ xs) v in (v'.vs) in
    let ys' = itlist itfn ys [] in
    let Q' = subst(combine(ys',ys)) Q in
    let asm = CONJ (ASSUME P) (ASSUME Q') in
    let ths = CONJUNCTS asm in
    let realths = ths in
    let cs = LIST_CONJ realths in
    let vs = filter (C free_in (concl cs)) (xs @ ys') in
    let eth = MP (itlist EXISTS_IMP2 xs (DISCH P (itlist efn vs cs))) thm1 in
    let eth' = MP (itlist EXISTS_IMP2 ys' (DISCH Q' eth)) thm2 in eth';;

% --------------------------------------------------------------------- %
%  |- ~~P   								%
% --------  NOT_NOT							%
%   |- P								%
% --------------------------------------------------------------------- %

let NOT_NOT th =
    CCONTR (dest_neg(dest_neg (concl th))) (UNDISCH th);;

% --------------------------------------------------------------------- %
% simp_rule: simplify the body of a non-axiom rule.                    %
% --------------------------------------------------------------------- %

let simp_rule = 
    let rule = NOT_NOT o CONV_RULE(RAND_CONV LIST_BETA_CONV) in
    \sfn set vs rul th.
     (let c1,c2 = CONJ_PAIR (CONV_RULE (REWR_CONV NOT_IMP) th) in
      let th1,_ = LIST_NOT_FORALL (\th. rule th,TRUTH) c2 in
      let th2 = LIST_EXISTS_THEN (CONJ_RUL set) c1 in
      let evs,imp = strip_exists (concl th1) in
      let gvs,cnc = (I # rand) (strip_forall(concl rul)) in
      let th3 = UNDISCH (SPECL gvs rul) in
      let pat = list_mk_forall(evs,fst(dest_imp imp)) in
      let inst = fst(match (concl th3) pat) in
      let tha = INST inst (DISCH_ALL th3) in
      let rins = MATCH_MP tha th2 in
      let erins = MATCH_MP tha (ASSUME (concl th2)) in
      let eqns = RULE th1 rins in
      let evs,eths = (I # conjuncts) (strip_exists(concl eqns)) in
      let thm = sfn (LIST_CONJ (map ASSUME eths)) (SPECL evs erins) in
      let vv,cs = (I # conjuncts) (strip_exists(concl th2)) in
      let itfn = \v vs. let v' = variant (vs @ evs) v in (v'.vs) in
      let vv' = itlist itfn vv [] in
      let cs' = map (subst(combine(vv',vv))) cs in
      let thx = PROVE_HYP (itlist efn vv' (LIST_CONJ (map ASSUME cs'))) thm in
      let simp = RULE2 vs eqns th2 in
      let nevs,cn = strip_exists(concl simp) in
      let hys = CONJUNCTS (ASSUME cn) in
      let hh,nthm = itlist chfn nevs (cn,itlist PROVE_HYP hys thx) in
      let res = (uncurry DISCH) (itlist chfn vs (hh,nthm)) in
          (PROVE_HYP th simp, res))
    where 
        chfn v (a,th) = let tm = mk_exists(v,a) in (tm,CHOOSE (v,ASSUME tm) th)
    and efn v th = EXISTS(mk_exists(v,concl th),v) th;;

% --------------------------------------------------------------------- %
% simp : simplify a case in the case analysis theorem                   %
%                                                                       %
% Each case has the form ~(!x1...xn.P).  The inference rule is:         % 
%                                                                       %
% If:                                                                   %
%                                                                       %
%       |- ~ P                                                          %
%   ------------- simp_axiom [x1;...;xn] rul                            % 
%        |- Q                                                           %
%                                                                       %
% or:                                                                   %
%                                                                       %
%       |- ~ P                                                          %
%   ------------- simp_rule [x1;...;xn] set rul                         % 
%        |- Q                                                           %
%                                                                       %
% then:                                                                 %
%                                                                       %
%    |- ~(!x1...xi. P)                                                  %
%  --------------------- simp set rul                                   %
%    |-  ?y1...yj. Q                                                    %
% --------------------------------------------------------------------- %


let simp set sfn rul th =
    let vs = fst(strip_forall (dest_neg (concl th))) in
        LIST_NOT_FORALL (simp_axiom sfn vs rul) th ?
        LIST_NOT_FORALL (simp_rule sfn set vs rul) th ? failwith `simp`;;

% --------------------------------------------------------------------- %
% LIST_DE_MORGAN: iterated inference rule.                              %
%                                                                       %
% If:                                                                   %
%                                                                       %
%      ~Pi |- ~Pi                                                       %
%   --------------------------- f (|- thi)	                        %
%      R |- Qi   |- Qi ==> R                                            %
%                                                                       %
% Then                                                                  %
%                                                                       %
%      R |- ~(P1 /\ ... /\ Pn)                                          %
%   ------------------------ LIST_DE_MORGAN f [|- th1;...;|- thn]       %
%      R |- Q1 \/ ... \/ Qn                                             %
%        |- Q1 \/ ... \/ Qn ==> R                                       %
% --------------------------------------------------------------------- %

let LIST_DE_MORGAN =
    let v1 = genvar ":bool" and v2 = genvar ":bool" in
    let thm = fst(EQ_IMP_RULE(CONJUNCT1 (SPECL [v1;v2] DE_MORGAN_THM))) in
    let IDISJ th1 th2 =
        let di = mk_disj(rand(rator(concl th1)),rand(rator(concl th2))) in
            DISCH di (DISJ_CASES (ASSUME di) (UNDISCH th1) (UNDISCH th2)) in
    let ITDISJ th1 th2 =
        let [hy1],cl1 = dest_thm th1 and [hy2],cl2 = dest_thm th2 in
        let dth = UNDISCH (INST [rand hy1,v1;rand hy2,v2] thm) in
            DISJ_CASES_UNION dth th1 th2 in
    \f ths th.
       let cs = conjuncts(dest_neg (concl th)) in
       let ts1,ts2 = split (map2 (\r,t. f r (ASSUME(mk_neg t))) (ths,cs)) in
           (PROVE_HYP th (end_itlist ITDISJ ts1)),end_itlist IDISJ ts2;;

% --------------------------------------------------------------------- %
% derive_cases_thm : prove exhaustive case analysis theorem for an      %
% inductively defined relation.                                         %
% --------------------------------------------------------------------- %

let derive_cases_thm (rules,ind) =
    let vs,(hy,c) = (I # dest_imp) (strip_forall (concl ind)) in
    let ps,P = (butlast vs, last vs) in
    let sind = SPECL ps ind and srules = map (SPECL ps) rules in
    let cvs,con = strip_forall c in
    let thm1 = DISCH hy (SPECL cvs (UNDISCH (SPEC P sind))) in
    let avs = map (genvar o type_of) cvs in
    let eqns = list_mk_conj(map2 mk_eq (cvs,avs)) in
    let asmp = subst (combine(avs,cvs)) (rator con) in
    let pred = list_mk_abs (avs,mk_neg(mk_comb(asmp,eqns))) in
    let thm2 = UNDISCH (UNDISCH (INST [pred,P] thm1)) in
    let thm3 = CONV_RULE LIST_BETA_CONV thm2 in
    let HY = rand(rator con) in
    let contr = DISCH HY (ADD_ASSUM HY (LIST_CONJ (map REFL cvs))) in
    let fthm = NOT_INTRO (DISCH (subst [pred,P] hy) (MP thm3 contr)) in
    let sfn eqs = SUBST (combine(map SYM (CONJUNCTS eqs),cvs)) HY in
    let set = fst(strip_comb HY) in
    let a,b = LIST_DE_MORGAN (simp set sfn) srules fthm in
    let th = IMP_ANTISYM_RULE (DISCH HY a) b in
    let ds = map (TRY_CONV REDUCE) (disjuncts(rand(concl th))) in
    let red = end_itlist (\t1 t2. MK_COMB (AP_TERM "\/" t1,t2)) ds in
        GENL ps (GENL cvs (TRANS th red));;



% --------------------------------------------------------------------- %
% Bind this value to "it".						%
% --------------------------------------------------------------------- %

derive_cases_thm;;

% --------------------------------------------------------------------- %
% end the section.							%
% --------------------------------------------------------------------- %

end_section derive_cases_thm;;

% --------------------------------------------------------------------- %
% save the function.							%
% --------------------------------------------------------------------- %

let derive_cases_thm = it;;

%< =====================================================================
TEST CASES

loadf `ind_defs`;;
timer true;;

let rules1,ind1 =
     let N = "N (R:num->num->bool) : num->num->bool" in 
     new_inductive_definition false `def1`
     ("^N n m", ["R:num->num->bool"])
      [ [],"^N 0 m" ;
        ["^N n m"; "R (m:num) (n:num):bool"], "^N (n+2) k"];;

derive_strong_induction (rules1,ind1);;
derive_cases_thm (rules1,ind1);;

let rules2,ind2 = 
    let RTC = "RTC1:(*->*->bool)->*->*->bool" in
    new_inductive_definition false `def2`
    ("^RTC R x y",  ["R:*->*->bool"]),
    [ [				       
      % ------------------------------ %  "R (x:*) (y:*):bool"],
                "^RTC R x y"	       ;
      [				       ],
      %------------------------------- % 
                "^RTC R x x"	       ;
      [  "^RTC R z y"         ; "(R:*->*->bool) x z"
      %------------------------------- %],
                "^RTC R x y"	       ];;

derive_strong_induction (rules2,ind2);;
derive_cases_thm (rules2,ind2);;

let rules3,ind3 = 
    let RTC = "RTC2:(*->*->bool)->*->*->bool" in
    new_inductive_definition false `def3`   
    ("^RTC R x y",  ["R:*->*->bool"]),

    [ [				       
      % ------------------------------ %  "R (x:*) (y:*):bool"],
                "^RTC R x y"	       ;

      [				       ],
      %------------------------------- % 
                "^RTC R x x"	       ;

      [ "^RTC R z y"         ; "(R:*->*->bool) x z"
      %------------------------------- %],
                "^RTC R x y"	       ];;

derive_strong_induction (rules3,ind3);;
derive_cases_thm (rules3,ind3);;

let rules4,ind4 = 
    let RTC = "RTC4:(*->*->bool)->*->*->bool" in
    new_inductive_definition false `def4`   
    ("^RTC R x y", ["R:*->*->bool"]),

    [ [				       
      % ------------------------------ %  "R (x:*) (y:*):bool"],
                "^RTC R x y"	       ;

      [				       
      %------------------------------- % ],
                "^RTC R x x"	       ;

      [  "^RTC R x z";   "^RTC R z y"  ],
      %------------------------------- % [],
                "^RTC R x y"	       ];;

derive_strong_induction (rules4,ind4);;
derive_cases_thm (rules4,ind4);;

let rules5,ind5 = 
    let ODD = "ODD:num->num->bool" in
    new_inductive_definition false `def5`   
    ("^ODD n m", []),

    [ [				       
      % ------------------------------ % ],
                "^ODD 2 3"	       ;

      [	"^ODD n m"; "(1=2) /\ (3=4)"; "^ODD 2 3"
      %------------------------------- % ],
                "^ODD (n+m) m"	       ];;

derive_strong_induction (rules5,ind5);;
derive_cases_thm (rules5,ind5);;

let rules6,ind6 = 
    let EVEN = "EVEN:num->bool" in
    new_inductive_definition false `def6`   
    ("^EVEN n", []),

    [ [				       
      % ------------------------------ % ],
                "^EVEN 0"	       ;

      [	"^EVEN n"
      %------------------------------- % ],
                "^EVEN (n+2)"	       ];;

derive_strong_induction (rules6,ind6);;
derive_cases_thm (rules6,ind6);;


===================================================================== >%
