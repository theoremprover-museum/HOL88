%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-syn.ml                                            %
%                                                                             %
%     DESCRIPTION:      This file defines the basic syntax functions of HOL.  %
%                       We use the same names as for PPLAMBDA.  The utilities %
%                       on ol-util.ml are included here.                      %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml              %
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
% this file uses things from genfns.ml                                  %
% --------------------------------------------------------------------- %
if compiling then (loadf `ml/genfns`);;

%----------------------------------------------------------------------------%
% Dynamically generated proof steps                                          %
%----------------------------------------------------------------------------%

type step = AssumeStep of term
          | ReflStep of term
          | SubstStep of (thm#term)list # term # thm
          | BetaConvStep of term
          | AbsStep of term # thm
          | InstTypeStep of (type#type)list # thm
          | DischStep of term # thm
          | MpStep of thm # thm
          | MkCombStep of thm # thm
          | MkAbsStep of thm
          | AlphaStep of term # term
          | AddAssumStep of term # thm
          | SymStep of thm
          | TransStep of thm # thm
          | ImpTransStep of thm # thm
          | ApTermStep of term # thm
          | ApThmStep of thm # term
          | EqMpStep of thm # thm
          | EqImpRuleStep of thm        % returns a pair of theorems %
          | SpecStep of term # thm
          | EqtIntroStep of thm
          | GenStep of term # thm
          | EtaConvStep of term
          | ExtStep of thm
          | ExistsStep of (term # term) # thm
          | ChooseStep of (term # thm) # thm
          | ImpAntisymRuleStep of thm # thm
          | MkExistsStep of thm
          | SubsStep of thm list # thm
          | SubsOccsStep of (int list # thm) list # thm
          | SubstConvStep of (thm # term) list # term # term
          | ConjStep of thm # thm
          | Conjunct1Step of thm
          | Conjunct2Step of thm
          | Disj1Step of thm # term
          | Disj2Step of term # thm
          | DisjCasesStep of thm # thm # thm
          | NotIntroStep of thm
          | NotElimStep of thm
          | ContrStep of term # thm
          | CcontrStep of term # thm
          | InstStep of (term # term) list # thm
          | StoreDefinitionStep of string # term
          | DefinitionStep of string # string
          | DefExistsRuleStep of term
          | NewAxiomStep of string # term
          | AxiomStep of string # string
          | TheoremStep of string # string
          | NewConstantStep of string # type
          | NewTypeStep of int # string
          | NumConvStep of term;;

% We hide the flag and the list in local variables. Four functions are
provided for the users to control the recording of proof %

begin_section `record_proof`;;

letref steplist = [] : step list;;
letref record_proof_flag = false;;
letref suspended = false;;

let is_recording_proof (():void) = record_proof_flag;;

let record_proof b = 
    (if b then (steplist := [];()); 
     record_proof_flag := b; ()) ;;

let suspend_recording () = 
    if record_proof_flag
     then (record_proof_flag := false;
       	   suspended := true; ());;

let resume_recording () =
    if (suspended & (not record_proof_flag))
     then (record_proof_flag := true;
    	   suspended := false; ());;

let RecordStep step =
    if  record_proof_flag
     then (steplist := (step.steplist); ());;

let get_steps (():void) = steplist;;

(record_proof,is_recording_proof,RecordStep,get_steps,
 suspend_recording,resume_recording);;
end_section `record_proof`;;

let (record_proof,is_recording_proof,RecordStep,get_steps,
     suspend_recording,resume_recording) = it;;

let new_constant(s,ty) =
 fst(new_constant(s,ty), RecordStep(NewConstantStep(s,ty)));;

% arb_term and ARB_THM are just arbitrary ML values of type term and thm %

let arb_term = "arb:*"
and ARB_THM  = axiom(`bool`, `ARB_THM`);;

let falsity = "F:bool" ? arb_term;;  % hack so will load in PPLAMBDA %

let bool_ty = ":bool" ? ":*";;       % hack so will load in PPLAMBDA %

% ===================================================================== %
% Derived constructors for HOL syntax.                                  %
% ===================================================================== %

let mk_forall (x,t) =
    let ty = type_of x in
    let allty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);bool_ty]) in
        mk_comb(mk_const(`!`,allty),mk_abs(x,t)) ? failwith `mk_forall`;;

let mk_exists (x,t) =
    let ty = type_of x in
    let exty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);bool_ty]) in
        mk_comb(mk_const(`?`,exty),mk_abs(x,t)) ? failwith `mk_exists`;;

let mk_select (x,t) =
    let ty = type_of x in
    let selty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);ty]) in
        mk_comb(mk_const(`@`, selty), mk_abs(x,t)) ? failwith `mk_select`;;

% NOTES:                                                                %
% mk_bool_comb `NAME` <tok> (t1,t2) --> "NAME t1 t2"                    %
% the K arb_term is a hack so it will load in pp-lambda.                %
%                                                                       %
% mk_iff deleted [TFM 91.01.20]                                         %

let mk_conj,mk_disj,mk_imp =
    let mk_bool_comb tok ftok =
        let OP = mk_const(tok,
                 mk_type(`fun`,[bool_ty;mk_type(`fun`,[bool_ty;bool_ty])])) in
       (\(t1,t2). mk_comb((mk_comb(OP,t1),t2)) ? failwith ftok) in
    ((mk_bool_comb `/\\` `mk_conj`,
      mk_bool_comb `\\/` `mk_disj`,
      mk_bool_comb `==>` `mk_imp`) ?
      (K arb_term, K arb_term, K arb_term));;

let mk_eq (t1,t2) =
    let ty1 = type_of t1 and ty2 = type_of t2 in
    if (ty1 = ty2) then
       let eqty = mk_type(`fun`,[ty1;mk_type(`fun`,[ty2;bool_ty])]) in
           mk_comb(mk_comb(mk_const(`=`,eqty),t1),t2) else failwith `mk_eq`;;

let mk_pair (t1,t2) =
    let ty1 = type_of t1 and ty2 = type_of t2 in
    let pty = mk_type(`prod`,[ty1;ty2]) in
    let cty = mk_type(`fun`,[ty1;mk_type(`fun`,[ty2;pty])]) in
        mk_comb(mk_comb(mk_const(`,`,cty),t1),t2);;

% The K arb_term is a hack so that this file will load in pp-lambda     %

let mk_neg =
    (let neg = mk_const(`~`,mk_type(`fun`,[bool_ty;bool_ty])) in
     (\t. mk_comb (neg,t) ? failwith `mk_neg`)) ? K arb_term;;

% ===================================================================== %
% Derived destructors for ML syntax.                                    %
% ===================================================================== %

let dest_forall =
    let check = assert (\c. fst(dest_const c) = `!`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_abs b) ?
         failwith `dest_forall`;;

let dest_exists =
    let check = assert (\c. fst(dest_const c) = `?`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_abs b) ?
         failwith `dest_exists`;;

let dest_select =
    let check = assert (\c. fst(dest_const c) = `@`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_abs b) ?
         failwith `dest_select`;;

let dest_conj =
    let check = assert (\c. fst(dest_const c) = `/\\`) in
    \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm) in
               (c1,c2)) ?
          failwith `dest_conj`;;

let dest_disj =
    let check = assert (\c. fst(dest_const c) = `\\/`) in
    \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm) in
               (c1,c2)) ?
          failwith `dest_disj`;;

let dest_eq =
    let check = assert (\c. fst(dest_const c) = `=`) in
    \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm) in
               (c1,c2)) ?
          failwith `dest_eq`;;

let dest_pair =
    let check = assert (\c. fst(dest_const c) = `,`) in
    \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm) in
               (c1,c2)) ?
          failwith `dest_pair`;;


% --------------------------------------------------------------------- %
% dest_imp "P ==> Q" = (P,Q).                                           %
%                                                                       %
% This also destructs negation - for compatibility with PPLAMBDA code   %
% CHANGED BY WW 24 Jan 1994 	    					%
% The PPLAMBDA compatible dest_imp is renamed to dest_neg_imp.		%
% --------------------------------------------------------------------- %

let dest_imp tm =
   (let ((c,p),q) = (dest_comb # I) (dest_comb tm) in
          if (fst (dest_const c)) = `==>` then (p,q) else fail) ?
    failwith `dest_imp`;;

let dest_neg t =
 (let t1,t2 = dest_comb t
  in
  if fst(dest_const t1)=`~` then t2 else fail)
 ? failwith `dest_neg`;;

let dest_neg_imp tm =
   ((let ((c,p),q) = (dest_comb # I) (dest_comb tm) in
          if (fst (dest_const c)) = `==>` then (p,q) else fail) ?
     let (c,b) = dest_comb tm in
         if (fst (dest_const c)) = `~` then (b,falsity) else fail) ?
    failwith `dest_neg_imp`;;

% dest_form "HOL_ASSERT t" --> "t" %

let dest_form fm =
 (let tok,t = dest_pred fm
  in
  if `HOL_ASSERT` = tok then t else fail)
 ? failwith `dest_form`;;

% mk_form "t" --> "HOL_ASSERT t" %

let mk_form t = mk_pred(`HOL_ASSERT`,t) ? failwith `mk_form`;;

% mk_pp_thm(["fm1";...;"fmn"],"fm")  -->  "fm1,...,fmn |- fm"

  It is written in Lisp and is loaded by:

   lisp  `(load '|/mnt/lcp/lcf/franz/F-macro|)` ;;
   lisp  `(load '|/mnt/lcp/lcf/franz/llmac|)`;;
   lisp  `(load '|/mnt/lcp/lcf/franz/F-dml|)`   ;;
   lisp  `(load 'mk_pp_thm)`                    ;;
  (N.B. this is probably out of date - e.g. need llmac from ~/hol)
%

% mk_thm(["t1";...;"tn"],"t") --> "t1,...,tn |- t"

   "t1,...,tn |- t"  is represented by the PPLAMBDA theorem:

     "HOL_ASSERT t1, ... , HOL_ASSERT tn |- HOL_ASSERT t"

OLD VERSION:

   let mk_thm = mk_pp_thm o (map mk_form # mk_form);;

CHANGED 21 April 1993 by JVT to get rid of "o" and "#" which cause
additional calls to "ap" in lisp.

%

let mk_thm P = mk_pp_thm (map mk_form (fst P),mk_form (snd P));;

% dest_thm "t1,...,tn |- t" --> (["t1";...;"tn"],t)

OLD VERSION:

  let dest_thm = (map dest_form # dest_form) o dest_thm;;

CHANGED 21 April 1993 by JVT to get rid of "o" and "#" which cause
additional calls to "ap" in lisp.

%

let dest_thm th = let P = dest_thm th in
                      (map dest_form (fst P),dest_form (snd P));;

let hyp   = \th. fst (dest_thm th)
and concl = \th. snd (dest_thm th);;

let hyp_union thl =
    itlist union (map hyp thl) [];;

% ===================================================================== %
% Derived discriminator functions.                                      %
% ===================================================================== %

let is_forall = can dest_forall and
    is_exists = can dest_exists and
    is_select = can dest_select and
    is_conj   = can dest_conj   and
    is_disj   = can dest_disj   and
    is_imp    = can dest_imp    and
%   is_iff    = can dest_iff    and              DELETED [TFM 91.01.20] %
    is_eq     = can dest_eq     and
    is_pair   = can dest_pair   and
    is_neg    = can dest_neg    and
    is_neg_imp= can dest_neg_imp;;

% ===================================================================== %
% Alpha-conversion, substitution, etc.                                  %
%                                                                       %
% Since HOL only has terms we can simplify the naming of various syntax %
% functions. For example, HOL just has aconv instead of aconv_term and  %
% aconv_form.                                                           %
%                                                                       %
% NB: These definitions REDEFINE previously dml'ed paired functions as  %
%     curried ones                                                      %
% ===================================================================== %

let aconv t u         = aconv (t,u) and
    subst l t         = subst (l,t) and
    subst_occs nl l t = subst_occs (nl,l,t) and
    free_in l t       = free_in (l,t) and
    variant vl v      = variant (vl,v);;

% ===================================================================== %
% Occurrences of types in terms and instantiation.                      %
%                                                                       %
% NB: These definitions REDEFINE paired functions as curried ones       %
% ===================================================================== %

let type_in_type ty1 ty2 = type_in_type (ty1,ty2) and
    type_in ty  tm       = type_in (ty, tm) and
    inst_type l ty       = inst_type (l,ty) and
    inst tml l tm        = inst (tml,l,tm);;

% ===================================================================== %
% Matching                                                              %
%                                                                       %
% NB: this REDEFINES the dml'ed paired "match" function to be curried.  %
% ===================================================================== %

let match pat ob = match (pat,ob);;

% ===================================================================== %
% Free variables.                                                       %
%                                                                       %
% dml'd functions term_frees, term_vars and term_tyvars renamed         %
% to be frees, vars and tyvars.  So this not needed     [TFM 90.06.04]  %
%                                                                       %
% let frees      = term_frees                                           %
% and vars       = term_vars                                            %
% and tyvars     = term_tyvars;;                                        %
% ===================================================================== %

% ===================================================================== %
% Syntax functions for term lists                                       %
% ===================================================================== %

let freesl  = \l. itlist (union o frees) l [] and
    varsl   = \l. itlist (union o vars) l [] and
    tyvarsl = \l. itlist (union o tyvars) l [];;

% ===================================================================== %
% Free variables of a theorem                                           %
% ===================================================================== %

let thm_frees th = let hy,c = dest_thm th in freesl (c.hy);;

% ===================================================================== %
% Discharge all assumptions w from wl                                   %
% ===================================================================== %

let disch(w,wl) = filter (\w'.not (aconv w w')) wl ;;

% ===================================================================== %
% The following definitions make code for PPLAMBDA compatible with HOL  %
%                                                                       %
% let is_equiv   = is_eq                                                %
% and mk_equiv   = mk_eq                                                %
% and dest_equiv = dest_eq;;                    [DELETED: TFM 90.09.09] %
% ===================================================================== %

% ===================================================================== %
% DELETED: TFM 90.08.16                                                 %
% let is_inequiv   = is_eq                                              %
% and mk_inequiv   = mk_eq                                              %
% and dest_inequiv = dest_eq;;                                          %
% ===================================================================== %

let is_pred t = (is_const(fst(dest_comb t))) ? false;;

let mk_pred(tk,t) =
 mk_comb(mk_const(tk, ":^(type_of t)->bool"),t) ? failwith `mk_pred `;;

let dest_pred t =
 (let t1,t2 = dest_comb t
  in
  (fst(dest_const t1),t2)
 ) ? failwith `dest_pred`;;

% ===================================================================== %
% Iterated derived constructors:                                        %
%                                                                       %
%  * list_mk_abs [x1;...;xn],t           --->   "\x1 ... xn.t"          %
%  * list_mk_comb op, [arg1; ...;argn]   --->   "op arg1 ... argn"      %
%  * list_mk_conj ["C1";...;"Cn"]        --->   "C1 /\ ... /\ Cn", n>0  %
%  * list_mk_disj ["D1"; ...; "Dn"]      --->   "D1 \/ ... \/  Dn", n>0 %
%  * list_mk_imp [t1;...;tn], t          --->   "t1==>(...(tn==>t)...)  %
%  * list_mk_forall [x1;...;xn],t        --->   "!x1 ... xn.t"          %
%  * list_mk_exists [x1;...;xn],t        --->   "?x1 ... xn.t"          %
%  * list_mk_pair ["t1";...;"tn"]        --->   "(t1,...,tn)", n>0      %
% ===================================================================== %

let list_mk_abs (vars,t) =
   (itlist (curry mk_abs) vars t) ? failwith `list_mk_abs`;;

let list_mk_comb (op,args) =
   (rev_itlist (\x f. mk_comb(f,x)) args op) ? failwith `list_mk_comb`;;

let list_mk_conj conjs =
   (end_itlist (curry mk_conj) conjs) ? failwith `list_mk_conj`;;

let list_mk_disj disjs =
   (end_itlist (curry mk_disj) disjs) ? failwith `list_mk_disj`;;

let list_mk_imp (antel,conc) =
   (itlist (curry mk_imp) antel conc) ? failwith `list_mk_imp`;;

let list_mk_forall (vars,body) =
   (itlist (curry mk_forall) vars body) ? failwith `list_mk_forall`;;

let list_mk_exists (vars,body) =
   (itlist (curry mk_exists) vars body) ? failwith `list_mk_exists`;;

% list_mk_pair added [RJB 90.10.22]. %

let list_mk_pair cmpts =
   (end_itlist (curry mk_pair) cmpts) ? failwith `list_mk_pair`;;

% ===================================================================== %
% Iterated derived destructors:                                         %
%                                                                       %
%  * strip_abs "\x1 ... xn. t"           --->   [x1; ...; xn], t        %
%  * strip_comb "t u1 ... un"            --->   t, [u1; ...; un]        %
%  * conjuncts "t1 /\ ... /\ tn"         --->   [t1; ...; tn]           %
%  * disjuncts "t1 \/ ... \/ tn"         --->   [t1; ...; tn]           %
%  * strip_imp "t1 ==> ... ==> tn ==> t" --->   [t1; ...; tn], t        %
%  * strip_forall "!x1 ... xn. t"        --->   [x1; ...; xn], t        %
%  * strip_exists "?x1 ... xn. t"        --->   [x1; ...; xn], t        %
%  * strip_pair "(t1,...,tn)"            --->   [t1; ...; tn]           %
%                                                                       %
% NOTE : because conjuncts splits both the left and right sides of a    %
% conjunction, this operation is not the inverse of list_mk_conj. It    %
% may be useful to introduce list_dest_conj, for splitting only the     %
% right tails of a conjunction. Likewise for disjunction.               %
% ===================================================================== %

letrec strip_abs tm =
    if is_abs tm
    then (let bv,t = dest_abs tm in
          let bvs, core = strip_abs t in
          bv.bvs, core)
    else [],tm;;

let strip_comb tm =
    letrec dest t rands =
        if is_comb t then
            (let rator,rand = dest_comb t in dest rator (rand.rands))
        else t, rands
    in dest tm [];;

letrec conjuncts w =
   (let a,b = dest_conj w in conjuncts a @ conjuncts b) ? [w];;

letrec disjuncts w =
   (let a,b = dest_disj w in disjuncts a @ disjuncts b) ? [w];;

letrec strip_imp fm =
    if is_imp fm  then
        (let wa,wc = dest_imp fm in
         let was,wb = strip_imp wc in
         wa.was, wb)
    else [],fm;;

letrec strip_forall fm =
    (let bv,body = dest_forall fm in
     let bvs, core = strip_forall body in
     bv.bvs, core)
    ? [],fm;;

letrec strip_exists fm =
    (let bv,body = dest_exists fm in
     let bvs, core = strip_exists body in
     bv.bvs, core)
    ? [],fm;;

% strip_pair added [RJB 90.10.22]. %

letrec strip_pair tm =
   (let x,y = dest_pair tm in x.(strip_pair y)) ? [tm];;

% ===================================================================== %
% Syntax functions for conditionals                                     %
% ===================================================================== %

let mk_cond (p,t,u) =
    (let rty = type_of t in
     let bty = type_of p in
     let ty1 = mk_type(`fun`,[rty;rty]) in
     let cty = mk_type(`fun`,[bty;mk_type(`fun`,[rty;ty1])]) in
     let cnd = mk_const(`COND`,cty) in
         mk_comb(mk_comb(mk_comb(cnd,p),t),u)) ?
    failwith `mk_cond`;;

let is_cond tm =
    (let (c,[p;x;y]) = strip_comb tm in fst(dest_const c) = `COND`) ? false;;

let dest_cond tm =
   (let (c,[p;x;y]) = strip_comb tm in
    if fst(dest_const c) = `COND` then p,x,y
    else fail)
   ? failwith `dest_cond`;;


% ===================================================================== %
% Syntax functions for let-terms:                                       %
%                                                                       %
% dest_let "LET f x" = ("f","x")                                        %
% mk_let ("f","x") = "LET f x"                                          %
% is_let tm              = equivalent to "can dest_let tm"              %
% ===================================================================== %

let dest_let =
    let check tm = fst(dest_const tm) = `LET` in
    \tm. (let (_,[f;x]) = (assert check # I) (strip_comb tm) in
              (f,x)) ? failwith `dest_let`;;

let mk_let (f,x) =
    (let fty = type_of f in
     let c = mk_const(`LET`,mk_type(`fun`,[fty;fty])) in
         mk_comb(mk_comb(c,f),x)) ? failwith `mk_let`;;

let is_let tm = can dest_let tm;;

% ===================================================================== %
% Syntax functions for lists added [RJB 90.10.24].                      %
% ===================================================================== %

% mk_cons ("t","[t1;...;tn]") ----> "[t;t1;...;tn]" %

let mk_cons (h,t) =
 (let hty = type_of h and tty = type_of t in
  let consty = mk_type(`fun`,[hty;mk_type(`fun`,[tty;tty])]) in
      mk_comb(mk_comb(mk_const(`CONS`,consty),h),t))
 ? failwith `mk_cons`;;

% dest_cons "[t;t1;...;tn]" ----> ("t","[t1;...;tn]") %

let dest_cons tm =
 (let (c,h),t = ((dest_comb # I) o dest_comb) tm in
      if fst(dest_const c) = `CONS` then (h,t) else fail)
 ? failwith `dest_cons`;;

let is_cons = can dest_cons;;


% mk_list (["t1";...;"tn"],":ty") ----> "[t1;...;tn]:(ty)list" %

let mk_list (els,ty) =
 (let nil = mk_const(`NIL`,mk_type(`list`,[ty])) in
      itlist (curry mk_cons) els nil)
 ? failwith `mk_list`;;

% dest_list "[t1;...;tn]:(ty)list" ----> (["t1";...;"tn"],":ty") %

letrec dest_list tm =
 (let h,t = dest_cons tm in
  let l,ty = dest_list t in (h.l),ty)
 ? (let `NIL`,`list`,[ty] = ((I # dest_type) o dest_const) tm in [],ty)
 ? failwith `dest_list`;;

let is_list = can dest_list;;


% If list_mk_cons were to be implemented it should behave as follows:        %
%                                                                            %
% list_mk_cons (["h1";...;"hm"],"[t1;...;tn]") ----> "[h1;...;hm;t1;...;tn]" %
%                                                                            %
% though I don't think it would be used much [RJB 90.10.24].                 %


%=============================================================================%
% Constructor, destructor and discriminator functions for paired abstractions %
% [JRH 91.07.17]                                                              %
%=============================================================================%

%--------------------------------------%
% mk_pabs - Makes a paired abstraction %
%--------------------------------------%

let mk_pabs =
  let mk_uncurry(xt,yt,zt) =
    mk_const(`UNCURRY`,mk_type(`fun`,
      [mk_type(`fun`,[xt; mk_type(`fun`,[yt;zt])]);
       mk_type(`fun`,[mk_type(`prod`,[xt;yt]); zt])])) in
  letrec mpa(varst,bod) =
    if is_var varst then mk_abs(varst, bod)
    else let (vs1,vs2) = dest_pair varst in
    let cab = mpa(vs1,mpa(vs2,bod)) in
    mk_comb(mk_uncurry(type_of vs1, type_of vs2, type_of bod),cab) in
  \(varst,bod). mpa(assert is_pair varst,bod) ? failwith `mk_pabs`;;

%-------------------------------------------------------------%
% dest_pabs - Destroys (possibly multiply) paired abstraction %
%-------------------------------------------------------------%

let dest_pabs =
  let ucheck = assert (curry$= `UNCURRY` o fst o dest_const) in
  letrec dpa tm =
    dest_abs tm ?
    let (_,unc) = (ucheck # I) (dest_comb tm) in
    let (lv,(rv,bod)) = (I # dpa) (dpa unc) in (mk_pair(lv,rv),bod) in
  \tm. (assert is_pair # I) (dpa tm) ? failwith `dest_pabs`;;

%--------------------------------------------------------%
% is_pabs - Tests whether a term is a paired abstraction %
%--------------------------------------------------------%

let is_pabs = can dest_pabs;;

% ===================================================================== %
% Lhs and rhs of an equation.                                           %
% ===================================================================== %

let lhs tm = fst(dest_eq tm) ? failwith `lhs` and
    rhs tm = snd(dest_eq tm) ? failwith `rhs`;;

% ===================================================================== %
% Search a term for a sub-term satisfying the predicate p               %
% ===================================================================== %

letrec find_term p tm =
    if (p tm) then tm else
    if (is_abs tm) then find_term p (snd (dest_abs tm)) else
    if (is_comb tm) then
       (let rator,rand = dest_comb tm in
            find_term p rator ? find_term p rand) else
       failwith `find_term`;;


% ===================================================================== %
% Operator and operand                                                  %
% ===================================================================== %

let rator tm = fst(dest_comb tm) ? failwith `rator` and
    rand  tm = snd(dest_comb tm) ? failwith `rand`;;

% ===================================================================== %
% Bound variable and body                           Added RJB 90.10.22  %
% ===================================================================== %

let bndvar tm = fst(dest_abs tm) ? failwith `bndvar` and
    body   tm = snd(dest_abs tm) ? failwith `body`;;

% ===================================================================== %
% Find all subterms in a term that satisfy a given predicate p.         %
% Added TFM 88.03.31                                                    %
% ===================================================================== %

let find_terms p tm =
    letrec accum tl p tm =
       let tl' = if p tm then tm.tl else tl in
           if is_abs tm then
              accum tl' p (snd (dest_abs tm)) else
           if is_comb tm then
              accum (accum tl' p (rator tm)) p (rand tm) else
              tl' in
     accum [] p tm;;

% ===================================================================== %
% mk_primed_var(name,ty): Makes a variable with a name that is a primed %
% variant of name and type ty.  Adds primes to the string name until it %
% is not the name of a constant in the current theory --- I.e. until    %
% mk_var (name,ty) succeeds.                                            %
%                                                                       %
% Added TFM 88.03.31                                                    %
% Modified by MJCG for HOL88 (30/11/88) as mk_var no longer fails       %
% ===================================================================== %

letrec mk_primed_var(name,ty) =
   if ascii_code(hd(explode name)) = 96 then fail
   if not(is_constant name)
      then mk_var(name,ty)
      else mk_primed_var(name ^ `'`, ty);;

% ===================================================================== %
% Some functions for theories (see also hol_thyfns.ml)                  %
% ===================================================================== %

% Introduce an axiom %

let new_axiom(tk,tm) =
    let gen_all t = list_mk_forall (frees t, t) in
    fst(new_open_axiom(tk, mk_form(gen_all tm)),
        RecordStep(NewAxiomStep(tk,tm)))
 ? failwith `new_axiom`;;

% Introduce an axiom without generalizing free variables (used for
  making definitions) %

let new_open_axiom(tk,tm) =
 new_open_axiom(tk, mk_form tm) ? failwith `new_open_axiom`;;

% --------------------------------------------------------------------- %
% Introduce a predicate - i.e. a function of type ty->bool              %
%                                                                       %
% NB: this overwrites the PPLAMBDA version of new_predicate.            %
%                                                                       %
% This line saves the PPLAMBDA version, but is commented out since this %
% function is not used anywhere                                         %
% let new_pp_predicate = new_predicate;;                                %
%                                                                       %
% Deleted: [TFM 90.09.09]                                               %
% --------------------------------------------------------------------- %

let new_predicate(tok,ty) = new_constant(tok, ":^ty -> bool");;

let mk_definition t =
 mk_comb(mk_const(`HOL_DEFINITION`,":bool->bool"),t);;

let dest_definition t =
 (let C,t1 = dest_comb t
  in
  if fst(dest_const C)=`HOL_DEFINITION` then t1 else fail
 ) ? failwith `dest_definition`;;

let is_definition = can dest_definition;;

let store_definition(name,t) =
 fst(mk_thm([],dest_definition(concl(new_open_axiom(name,mk_definition t)))),
     RecordStep(StoreDefinitionStep(name,t)));;


let theorem thy factname    = 
 fst(paired_theorem (thy,factname),  RecordStep(TheoremStep(thy,factname)))
and new_type arity tok      = 
 fst(paired_new_type (arity,tok), RecordStep(NewTypeStep(arity,tok)))
and delete_thm thy factname =
 paired_delete_thm (thy,factname);;

let pp_axiom thy factname = axiom (thy,factname);;

let axiom thy ax =
 let th = pp_axiom thy ax in
     if is_definition(concl th)
      then failwith `axiom` 
      else fst(th, RecordStep(AxiomStep(thy,ax)));;

% --------------------------------------------------------------------- %
%< Deleted by WW 6 Dec 93. A function having the same name is defined 
   in hol-thyfn.ml which will mask out this definition.
   Restored by WW 2 Jan 94 because this fiunction is needed to build
   basic-hol which does not include the file hol-thyfn.ml >%
let definition thy ax =
 fst(mk_thm([],dest_definition(concl(pp_axiom thy ax))),
     RecordStep(DefinitionStep(thy,ax)))
 ? failwith `definition`;;

% --------------------------------------------------------------------- %
% Introduce an infix                                                    %
%                                                                       %
% let new_infix = new_curried_infix;;                                   %
%                                                                       %
% Now dml-ed to be new_infix in the first place! [TFM 91.03.17]         %
% Adding RecordStep for proof recording [WW 05-07-93]			%
% --------------------------------------------------------------------- %
let new_infix(s,ty) =
 fst(new_infix(s,ty), RecordStep(NewConstantStep(s,ty)));;

% ML code for declaring and keeping track of binders %

% Modification J.Joyce Apr 87 - move lisp expression for declaring the %
% ml function "parse_as_binder" to a separate lisp source because of   %
% problems with nesting "|".                                           %
%								       %
% Modified to define parse_as_binder earlier in the build sequence.    %
% This fixes the binder inheritance bug.  TFM 92.10.01 for HOL88 2.01  %
%								       %
% lisp (concat (concat `(load "` lisp_dir_pathname) `parse_as_binder")`);; %


% ---------------------------------------------------------------------- %
% tuple operations used only for storing binders: deleted [TFM 91.02.24] %
% ["t1"; ... ;"tn"] --> "(t1, ... ,tn)"                                  %
% Function mk_tuple deleted: [TFM 91.02.24]                              %
% let mk_tuple = end_itlist (curry mk_pair);;                            %
% let mk_tuple l = itlist (curry mk_pair) l arb_term;;                   %
%   ["t1"; ... ;"tn"]  --> "(t1, ... ,tn)"                               %
% letrec dest_tuple t =                                                  %
%      (let x,y = dest_pair t in x . (dest_tuple y)) ? [t];;             %
%                                                                        %
% letrec dest_tuple t =                                                  %
%   if t = arb_term then [] else ($. o (I # dest_tuple) o dest_pair) t;; %
% ---------------------------------------------------------------------- %


% Store ["t1";...;"tn"] as the "theorem" |- BINDERS(t1,...,tn)
  (binders are stored as theorems rather than axioms as the
   list of binders needs to be deleted when extending a theory and
   axioms can't be deleted).
%

let store_binders l =
 let t = itlist (curry mk_pair) l arb_term      % was mk_tuple l %
 in
 save_thm
  (`LIST_OF_BINDERS`,
   mk_thm
   ([], mk_comb(mk_const(`BINDERS`,mk_type(`fun`,[type_of t;":bool"])), t)));;

% list of binders in the current theory %

letref list_of_binders = []:term list;;


% Introduce a binder %

let new_binder(tok,ty) =
 let tok1,tyl1 = (dest_type ty ? failwith `bad binder type`)
 in
 let tok2,tyl2 = (dest_type(hd tyl1) ? failwith `bad binder type`)
 in
 if not((tok1=`fun`) or (tok2=`fun`))
 then failwith `bad binder type`
 else
 (parse_as_binder tok;
  new_constant(tok,ty);
  list_of_binders := mk_const(tok,ty).list_of_binders;
  ());;

% Added on 25/11/1988 for HOL88:
  new_specification `flag` `name` `C` |- ?x. ... x ...
  declares C as a new constant and then does
  new_axiom(`name`, "... C ...")  `flag` must be one of `constant`,
  `infix` or `binder` and determines the syntactic stutus of C.
  To avoid Roger Jones type problems,
  it is required that there be no type variables in types of subterms of
  "... C ..." that do not occur in the type of C. This rules out, for example,
  new_specification(tok, `Wonk`, |- ?b:bool. b = !x y:*. x=y)

  The specification above was amended on 8/2/89 to the following:

     new_specification
      name
      [`flag1`,`C1`; ... ; `flagn,Cn`]
      |- ?x1 ... xn. ... x1 ... xn ...
  declares C1, ... ,Cn as a new constants and then does
  new_axiom(`name`, "... C1 ... Cn ...");  `flagi` must be one of `constant`,
  `infix` or `binder` and determines the syntactic stutus of Ci.
  To avoid Roger Jones type problems, it is required that there be no
  type variables in types of subterms of  "... C1 ... Cn ..." that do not
  occur in the types of any Ci (1 <= i <= n). This rules out, for example,

     new_specification
      (`Wonk_DEF`, [`constant`,`Wonk`,`], |- ?b:bool. b = !x y:*. x=y)

  which would define a constant "Wonk" of type ":bool" by
  the inconsistent axiom:

     |- Wonk = !x y:*. x=y

%

% Auxiliary function to strip off n quantifiers %

letrec n_strip_quant dest_fn n t =
 if n=0
  then ([],t)
  else
   let x,t' = dest_fn t
   in
   let l,t'' = n_strip_quant dest_fn (n-1) t'
   in
   (x.l,t'');;

% Auxiliary function to test whether a type is the possible type
  of an infix.
%

let is_infix_type ty =
 let op,l = dest_type ty
 in
 if op = `fun`
  then (if fst(dest_type(hd(tl l)))=`fun` then true else false)
  else false;;

% Auxiliary function to test whether a type is the possible type
  of an binder.
%

let is_binder_type ty =
 let op,l = dest_type ty
 in
 if op = `fun`
  then (if fst(dest_type(hd l))=`fun` then true else false)
  else false;;

% Auxiliary function to check the arguments to new_specification;
  fails (with useful message) or returns
  (["x1";...;"xn"], "... x1 ... xn ...")
%

let check_specification defname flag_name_list th =
 if not(draft_mode())
  then failwith `not in draft mode`
 if not(null(hyp th))
  then failwith `no assumptions to theorem allowed in specifications`
 if not(null(frees(concl th)))
  then failwith(itlist
                (\t s. fst(dest_var t)^` `^s)
                (frees(concl th))
                `is (are) unbound variable(s) in specification`)
  else
  map
   (\(flag,name).
    if is_constant name
     then failwith (`attempt to specify an existing constant: `  ^ name)
    if not(allowed_constant name)
     then failwith (name ^ ` is not an allowable constant name`)
    if not (mem flag [`constant`;`infix`;`binder`])
     then failwith(concat flag ` must be \`constant\`, \`infix\` or \`binder\``)
   )
   flag_name_list;
   let vars,body =
    (n_strip_quant dest_exists (length flag_name_list) (concl th)
     ? failwith `too few existentially quantified variables`)
   in
   map
    (\var.
     if not(null(subtract (tyvars body) (tyvars var)))
      then failwith(itlist
                    (\vty s. dest_vartype vty^` `^s)
                    (subtract (tyvars body) (tyvars var))
                    (`should occur in the type of `^(fst(dest_var var)))))
    vars;
   map2
    (\((flag,name),var).
     if (flag = `infix`) & not(is_infix_type(type_of var))
      then failwith(fst(dest_var var)^` doesn't have infix type`)
     if (flag = `binder`) & not(is_binder_type(type_of var))
      then failwith(fst(dest_var var)^` doesn't have binder type`))
    (flag_name_list,vars);
   (vars,body);;

let new_specification defname flag_name_list th =
 let vars,body =
  check_specification defname flag_name_list th
 in
 map2
  (\((flag,name),var).
   if flag = `constant`
    then new_constant(name,type_of var)
   if flag = `infix`
    then new_infix(name,type_of var)
    else new_binder(name,type_of var))
  (flag_name_list,vars);
 store_definition
  (defname,
   subst
    (map2
     (\((flag,name),var). (mk_const(name,type_of var),var))
     (flag_name_list,vars))
    body);;

%
 new_definition(tok,"C ... = t") declares C as a new constant
 and then does new_axiom(tok,"C ... = t"). "C ..." must be a <lhs>
 as described below, all free variables in t must be bound in "C ..."
 and C must not occur in t. Free variables in the definition may be
 universally quantified
%

% check that tm is a <varstruct> where:

   <varstruct> ::= <var> | (<varstruct>,...,<varstruct>)

  and that there are no repeated variables. Return list of variables.
 %

letrec check_varstruct tm =
 if is_var tm
  then [tm]
  else
  (let t1,t2 = (dest_pair tm ? failwith `bad varstruct`)
   in
   let l1 = check_varstruct t1
   and l2 = check_varstruct t2
   in
   if intersect l1 l2 = []
    then l1@l2
    else failwith `repeated variable in varstruct`);;


% check that tm is a <lhs> where:

   <lhs> ::= <var> | <lhs> <varstruct>

 and that no variables are repeated. Return list of variables.
%

letrec check_lhs tm =
 if is_var tm
 then [tm]
 if is_const tm
 then failwith(`attempt to redefine the constant ` ^
               (fst(dest_const tm)))
 if not(is_comb tm)
 then failwith`lhs not of form "x = ..." or "f x = ... "`
 else
 (let t1,t2 = dest_comb tm
  in
  let l1 = check_lhs t1
  and l2 = check_varstruct t2
  in
  if intersect l1 l2 = [] then l1@l2 else failwith `var used twice`);;

%  if "C ... = (...:ty)" then  (get_type "C ..." ty) gives the
   type of C.
%


letrec get_type left rightty =
 (if is_var left
  then rightty
  else get_type (rator left) ":^(type_of(rand left))->^rightty"
 ) ? failwith `bad lhs`;;

% The derived rule

     DEF_EXISTS_RULE : term -> thm

  proves that a function defined by a definitional equation exists.
  The implementation below uses mk_thm, but this will be changed eventually.
%

let DEF_EXISTS_RULE tm =
 let vars,(left,right) = (((I # dest_eq) o strip_forall) tm
                          ? failwith`definition not an equation`)
 in
 let leftvars  = check_lhs left
 and ty        = get_type left (type_of right)
 and rightvars = frees right
 in
 if not(set_equal(intersect leftvars rightvars)rightvars)
 then failwith`unbound var in rhs`
 if mem(hd leftvars)rightvars
 then failwith `recursive definitions not allowed`
 else
 (let name = fst(dest_var(hd leftvars))
  and v    = hd leftvars
  in
  (if not(null(subtract (tyvars right) (tyvars v)))
    then failwith(dest_vartype(hd(subtract (tyvars right) (tyvars v)))^
                  ` an unbound type variable in definition`)
   if not(allowed_constant name)
    then failwith (concat name ` is not allowed as a constant name`)
    else
     fst(mk_thm([],
                mk_exists
                 (v,
                  list_mk_forall
                   ((union vars (tl leftvars)), mk_eq(left,right)))),
         RecordStep(DefExistsRuleStep tm))));;

let new_gen_definition flag (tok,tm) =
 let def_thm = DEF_EXISTS_RULE tm
 in
 let name = (fst o dest_var o fst o dest_exists o concl) def_thm
 in
 new_specification tok [flag,name] def_thm;;

let new_definition =  new_gen_definition `constant`;;

% Old version:

let new_definition(tok,tm) =
 let vars,(left,right) = (((I # dest_eq) o strip_forall) tm
                          ? failwith`bad definition`)
 in
 let leftvars  = check_lhs left
 and ty        = get_type left (type_of right)
 and rightvars = frees right
 in
 if not(set_equal(intersect leftvars rightvars)rightvars)
 then failwith`unbound var in rhs`
 if mem(hd leftvars)rightvars
 then failwith `recursive definitions not allowed`
 else
 (let name = fst(dest_var(hd leftvars))
  and v    = hd leftvars
  in
  ((new_constant(name, ty);
    store_definition
     (tok,
      list_mk_forall(vars,mk_eq(subst[mk_const(name,ty),v]left, right))))
   ) ? failwith `disallowed constant or not in draft`);;
%

%
 new_infix_definition(tok,"C ... = t") declares C
 as a new curried infix and then does new_axiom(tok,"C ... = t").
 Note that C must appear in prefix form in the declaration.
%

let new_infix_definition = new_gen_definition `infix`;;

% Old version:

let new_infix_definition(tok,tm) =
 let vars,(left,right) = (((I # dest_eq) o strip_forall) tm
                          ? failwith`bad definition`)
 in
 let ty        = get_type left (type_of right)
 and leftvars  = check_lhs left
 and rightvars = frees right
 in
 if not(set_equal(intersect leftvars rightvars)rightvars)
 then failwith`unbound var in rhs`
 if mem(hd leftvars)rightvars
 then failwith `recursive definitions not allowed`
 else
 (let name = fst(dest_var(hd leftvars))
  and v    = hd leftvars
  in
  ((new_infix(name, ty);
    store_definition
     (tok,
      list_mk_forall(vars,mk_eq(subst[mk_const(name,ty),v]left, right))))
   ) ? failwith `disallowed infix`);;
%

% --------------------------------------------------------------------- %
% let infixes = curried_infixes;;                                       %
%                                                                       %
% Now dml-ed to be infixes in the first place! [TFM 91.03.17]           %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% new_theory                                    [revised: TFM 90.06.05] %
% NOTE this overwrites the function new_theory defined using dml.       %
% --------------------------------------------------------------------- %

let new_theory tok =
   (can store_binders list_of_binders;
    new_theory tok;
    list_of_binders := [];
    ());;

% --------------------------------------------------------------------- %
% close_theory                                                          %
%                                                                       %
% close_pp_theory made local:                           [TFM 90.06.05]  %
% NOTE this overwrites the function close_theory defined using dml.     %
% --------------------------------------------------------------------- %

let close_theory =
    let close_pp_theory = close_theory in
    \x:void.(store_binders list_of_binders;
             close_theory();
             list_of_binders := [];
             ()) ? failwith`close_theory`;;

% --------------------------------------------------------------------- %
% binders: fetch list of binders from a theory                          %
%                                                                       %
% Now fails on non-ancestor theories.                   [JRH 91.06.19]  %
% --------------------------------------------------------------------- %

let binders =
    letrec dest_tuple t =
      if t = arb_term then [] else ($. o (I # dest_tuple) o dest_pair) t in
    \thy. if thy=`-` or mem thy (ancestry()) then
            let thl = ([theorem thy `LIST_OF_BINDERS`] ? []) in
            if null thl then [] else
              (let t1,t2 = dest_comb(concl(hd thl)) in
               if fst(dest_const t1)=`BINDERS` then dest_tuple t2 else fail)
              ? failwith `binders: invalid binder list in theory `^thy
          else failwith `binders: `^thy^` is not an ancestor`;;

% --------------------------------------------------------------------- %
% activate_binders: tell the parser about binders                       %
% --------------------------------------------------------------------- %

let activate_binders thy =
 map (parse_as_binder o fst o dest_const) (binders thy);;

% --------------------------------------------------------------------- %
% ancestors --- Get the (proper) ancestors of a theory.			%
% Added by WW 05-07-93.                                                 %
% The original slow implementation was in hol-thyfn.ml.                 %
% The local function                                                    %
% all_parents = -: string list -> string list -> string list		%
% all_parents plist thyl returns a list of theory names which are the	%
% ancestors of the theories in thyl and not in plist.			%
% --------------------------------------------------------------------- %
let ancestors =
    letrec all_parents plist =
      fun [] . plist
      | (thy . thyl) .
    	if (mem thy plist) then all_parents plist thyl
    	else (
    	    let pl = parents thy in
    	    let vl = subtract pl ( (intersect pl plist)) in
    	    (all_parents (thy . plist) (vl @ thyl))) in
    (\thy'. 
    	let thy =  (thy' = `-`) => (current_theory()) | thy' in
    	let ths = all_parents [] [thy] in
          snd(remove (\th. th = thy) ths));;

% --------------------------------------------------------------------- %
% CHANGED BY WW 8 Feb 1993  	    					%
% Attempt to speed up the loading of theory				%
% 1) make the following functions local in this section:		%
%     activate_all_binders						%
% 2) add new function all_parents. It is similar to the function 	%
%    ancestors but return the argument and all ancestors,		%
%     and it runs much faster than the old ancestors().			%
% 3) add the list thy_chked to remember the theories whose binders have	%
%    been activated.	    	    					%
% --------------------------------------------------------------------- %
begin_section `load_thy`;;

% --------------------------------------------------------------------- %
% activate_all_binders: activate the binders on a theory and all its    %
% ancestor theories.                                                    %
% OLD VERSION:	    	    	    					%
%letrec activate_all_binders thy =  					%
% if thy = `HOL`    	    	    					%
% then []   	    	    	    					%
% else	    	    	    	    					%
% (let bl = activate_binders thy    					%
%  and pl = parents thy	    	    					%
%  in	    	    	    	    					%
%  itlist (\tok tokl. activate_all_binders tok @ tokl) pl bl);;		%
% Changed by WW 8 Feb 93    	    					%
% This function is reimplemented. It runs much faster.			%
% It does not repeatedly go into a ancestor theory and every theory	%
% whose binders have been activated is remembered in the list thy_chked %
% --------------------------------------------------------------------- %
letref  thy_chked = []:string list;;

let activate_all_binders thy =
    let pl = thy . (ancestors thy) in
    let nl = subtract pl thy_chked in
    (thy_chked := union pl thy_chked;
     (itlist (\l1 l2. (activate_binders l1) @ l2) nl []));;

% --------------------------------------------------------------------- %
% load_theory                                                           %
%                                                                       %
% load_pp_theory made local:                            [TFM 90.06.05]  %
% NOTE this overwrites the function load_theory defined using dml.      %
% Changed by WW 5 Feb 93    	    					%
% call the local active_all_binders to prevent 				%
% repeatedly activate binders.	    					%
% --------------------------------------------------------------------- %

let load_theory =
    \thy. (load_theory thy; activate_all_binders thy; ());;

% --------------------------------------------------------------------- %
% extend_theory                                                         %
%                                                                       %
% extend_pp_theory made local:                          [TFM 90.06.05]  %
% NOTE this overwrites the function extend_theory defined using dml.    %
% Changed by WW 5 Feb 93    	    					%
% call the local  active_all_binders to prevent 			%
% repeatedly activate binders.	    					%
% --------------------------------------------------------------------- %

let extend_theory =
    \thy. (extend_theory thy;
           activate_all_binders thy;
           list_of_binders := binders thy;
           ((delete_thm thy `LIST_OF_BINDERS`; ()) ? ());
           ());;

% --------------------------------------------------------------------- %
% new_parent                                            [TFM 92.02.22]  %
% Added so that binders in parent and its ancestors are activated.	%
% NOTE this overwrites the function new_parent defined using dml.       %
% Changed by WW 5 Feb 93    	    					%
% call the local  activate_all_binders to prevent repeatedly activate   %
% binders.	    							%
% --------------------------------------------------------------------- %

let new_parent thy =
    (new_parent thy; activate_all_binders thy; ());;

(load_theory, extend_theory, new_parent);;
end_section `load_thy`;;

let (load_theory, extend_theory, new_parent) = it;;

let new_binder_definition = new_gen_definition `binder`;;

% Old version:

let new_binder_definition(tok,tm) =
 let vars,(left,right) = (((I # dest_eq) o strip_forall) tm
                          ? failwith`bad definition`)
 in
 let ty        = get_type left (type_of right)
 and leftvars  = check_lhs left
 and rightvars = frees right
 in
 if not(set_equal(intersect leftvars rightvars)rightvars)
 then failwith`unbound var in rhs`
 if mem(hd leftvars)rightvars
 then failwith `recursive definitions not allowed`
 else
 (let name = fst(dest_var(hd leftvars))
  and v    = hd leftvars
  in
  ((new_binder(name, ty);
    store_definition
     (tok,
      list_mk_forall(vars,mk_eq(subst[mk_const(name,ty),v]left, right))))
   ) ? failwith `disallowed binder`);;
%

% ===================================================================== %
% new_type_definition: define a new logical type.                       %
%                                                                       %
% USAGE: new_type_definition(name, pred, thm)  (DRAFT MODE ONLY)        %
%                                                                       %
% ARGUMENTS: name --- a string giving the name of the new type or       %
%                     type operator that is to be defined.              %
%                                                                       %
%            pred --- a term denoting a predicate which is to           %
%                     define a subset of an existing type (ty say)      %
%                     that is to represent the new type.  The type      %
%                     of pred must be "ty -> bool" and pred must        %
%                     must contain no free variables.                   %
%                                                                       %
%            thm  --- a theorem asserting the existence of some         %
%                     object of type ty that satisfies pred.  The       %
%                     theorem must be of the form "|- ?x. pred x" for   %
%                     some variable x. The theorem must have no         %
%                     assumptions.                                      %
%                                                                       %
% SIDE EFFECTS: 1) Introduces a new type (type operator) with the       %
%                  given name. The arity of the new type operator       %
%                  is the same as the number of type variables in the   %
%                  predicate pred. Fails if name is already the name of %
%                  an existing type.                                    %
%                                                                       %
%               2) Asserts an axiom stating that there is an isomorphism%
%                  from the new type to the subset of ty defined by the %
%                  predicate pred.  The name of this axiom will be      %
%                  form `name_TY_DEF`.  If an axiom (or definition)     %
%                  with this name already exists, then the call fails.  %
%                                                                       %
%                  The form of the axiom asserted will be as follows:   %
%                                                                       %
%                     new_type_definition(`ty`, "P", |- ?x. P x)        %
%                                                                       %
%                  yields the axiom:                                    %
%                                                                       %
%                     ty_TY_DEF = |- ?rep. TYPE_DEFINITION P rep        %
%                                                                       %
%                  I.e. there is a function rep from the new type to    %
%                  the representing type ty that is one to one and onto %
%                  the subset defined by P.                             %
%                                                                       %
% RETURNS: the axiom as a theorem.                                      %
%                                                                       %
% IMPLEMENTATION NOTE: the dml'ed ML function is_axiom here tests if an %
% axiom, OR definition is already in the current theory.                %
% ===================================================================== %

let new_type_definition (name,pred,thm) =
    if not(draft_mode()) then failwith `not in draft mode` else
    if is_axiom (current_theory(),(name ^ `_TY_DEF`)) then
       failwith `"` ^ name ^ `_TY_DEF" already an axiom or definition` else
    if not(null(frees pred)) then
       failwith `subset predicate must be a closed term` else
    if not((I # tl)(dest_type(type_of pred))=(`fun`,[":bool"]) ? false) then
       failwith `subset predicate has the wrong type` else
    if not(null(hyp thm)) then
       failwith `existence theorem must have no assumptions` else
    if not((pred = rator(snd(dest_exists(concl thm))))?false) then
       failwith `existence theorem must match subset predicate` else
    if (is_type name) then
       failwith name ^ ` is already the name of a type or type operator` else
    let _,[ty;_] = dest_type(type_of pred) and
        evar       = fst(dest_exists(concl thm)) in
    let tyvarsl = tyvars pred in
     new_type (length tyvarsl) name;
     let newty  = mk_type (name,tyvarsl) in
     let repty  = mk_type (`fun`,[newty;ty]) in
     let rep    = mk_primed_var(`rep`, repty) in
     let bool   = mk_type (`bool`,[]) in
     let TYDEF_ty = mk_type (`fun`,[mk_type(`fun`,[ty;bool]);
                                    mk_type(`fun`,[repty;bool])]) in
     let TYDEF = mk_const(`TYPE_DEFINITION`,TYDEF_ty) in
     let ax = mk_exists(rep,mk_comb(mk_comb(TYDEF,pred),rep)) in
     store_definition (name ^ `_TY_DEF`,ax);;

% ===================================================================== %
% Functions for interpreting tokens as ML                               %
%                                                                       %
% space and ascii_ize made local                        [TFM 90.06.01]  %
% ===================================================================== %

let ML_eval =
    let space = ascii_code ` ` in
    let ascii_ize tok =
        itlist (\n l. map ascii_code (explode n)@[space]@l) (words tok) [] in
        (inject_input o ascii_ize);;

% ===================================================================== %
% Definition of pre terms in ML                                         %
% ===================================================================== %

rectype preterm =
    preterm_var      of string                       % Variables       %
  | preterm_const    of string                       % Constants       %
  | preterm_comb     of preterm # preterm            % Combinations    %
  | preterm_abs      of preterm # preterm            % Abstractions    %
  | preterm_typed    of preterm # type               % Explicit typing %
  | preterm_antiquot of term;;                       % Antiquotation   %

% ===================================================================== %
% Constraining the type of the Lisp defined typechecker                 %
% ===================================================================== %

let preterm_to_term = preterm_to_term : preterm -> term;;
