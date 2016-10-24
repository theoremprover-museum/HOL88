%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-rule.ml                                           %
%                                                                             %
%     DESCRIPTION:      Primitive inference rules for HOL                     %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, hol-syn.ml             %
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

% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
if compiling then (loadf `ml/hol-in-out`) else ();;

% First we load the definitions from the theory bool %

let T_DEF             = definition `bool` `T_DEF`
and F_DEF             = definition `bool` `F_DEF`
and FORALL_DEF        = definition `bool` `FORALL_DEF`
and AND_DEF           = definition `bool` `AND_DEF`
and OR_DEF            = definition `bool` `OR_DEF`
and EXISTS_DEF        = definition `bool` `EXISTS_DEF`
and NOT_DEF           = definition `bool` `NOT_DEF`
and EXISTS_UNIQUE_DEF = definition `bool` `EXISTS_UNIQUE_DEF`
and LET_DEF           = definition `bool` `LET_DEF`
and UNCURRY_DEF       = definition `bool` `UNCURRY_DEF`
and CURRY_DEF         = definition `bool` `CURRY_DEF`
and COND_DEF          = definition `bool` `COND_DEF`;;

% Deleted: TFM 91.01.20							%
% and IFF_DEF           = definition `bool` `IFF_DEF`			%
% and FCOND_DEF         = definition `bool` `FCOND_DEF`;;		%

% The definition of TYPE_DEFINITION might as well also be loaded.	%
let TYPE_DEFINITION   = definition `bool` `TYPE_DEFINITION`;;

% then the axioms %

let BOOL_CASES_AX   = axiom `bool` `BOOL_CASES_AX`
and IMP_ANTISYM_AX  = axiom `bool` `IMP_ANTISYM_AX`
and ETA_AX          = axiom `bool` `ETA_AX`
and SELECT_AX       = axiom `bool` `SELECT_AX`;;

% then the pairing theorems (the ARB_THM is there so the file
  can be loaded before the type ":prod" has been defined, see
  hol/theories/mk_bool.ml). %

% Added: PAIR_EQ (TFM 88.03.31)						%

let PAIR            = theorem `bool` `PAIR` ? ARB_THM
and FST             = theorem `bool` `FST`  ? ARB_THM
and SND             = theorem `bool` `SND`  ? ARB_THM
and PAIR_EQ         = theorem `bool` `PAIR_EQ`  ? ARB_THM;;

% Finally we define the primitive inference rules %

% Introduce an assumption
	
      ---------
        A |- A
%

let ASSUME w = 
 fst(mk_thm([w],w), RecordStep(AssumeStep w)) ? failwith`ASSUME`;;

% Reflexivity

            "t"   --->    |- t=t
%

let REFL t = 
 fst(mk_thm([], mk_eq(t,t)), RecordStep(ReflStep t)) ? failwith `REFL`;;

% Substitution

        A1 |- ti = ui  ,  A2 |- t[ti]
       -------------------------------
 	      A1 u A2 |- t[ui]

%

let SUBST thvars w lhsthm =
   (let ths,vars = split thvars in
    let ls, rs = split (map (dest_eq o concl) ths) in
    if aconv (subst (combine(ls,vars)) w) (concl lhsthm)
     then
       fst(mk_thm( hyp_union(lhsthm . ths), subst(combine(rs,vars)) w),
    	   RecordStep(SubstStep(thvars, w, lhsthm)))
    else fail
   )? failwith `SUBST` ;;

% Beta-conversion

 	"(\x.t1)t2"   --->    |- (\x.t1)t2 = t1[t2/x]
%

let BETA_CONV t =
 (let f,v = dest_comb t in
  let x,u = dest_abs f in
  fst(mk_thm([], mk_eq(t,subst[v,x]u)), RecordStep(BetaConvStep t))
 % Antiquotation removed TFM 90.07.10 %
     ) ? failwith `BETA_CONV`;;

% Abstraction

         A |- t1 = t2
     -----------------------  (provided x is not free in A)
      A |- (\x.t1) = (\x.t2)
%

% --------------------------------------------------------------------- %
% OPTIMIZED: [TFM 90.06.27]						%
% 									%
% Original code:							%
%									%
%  let ABS x th =							%
%   (let t1,t2 = dest_eq(concl th)					%
%    in									%
%    if mem x (freesl(hyp th)) 						%
%    then fail								%
%    else mk_thm(hyp th, "(\^x.^t1)=(\^x.^t2)")				%
%   ) ? failwith `ABS`;;						%
% --------------------------------------------------------------------- %

let ABS x th =
 (let hy,t1,t2 = (I # dest_eq)(dest_thm th)
  in
  if mem x (freesl hy) 
  then fail
  else fst(mk_thm(hy, mk_eq(mk_abs(x,t1),mk_abs(x,t2))),
    	   RecordStep(AbsStep(x,th)))
 ) ? failwith `ABS`;;

%Instantiate types

                A |- t
   ------------------------------------- (where type variables vtyi not in A)
     A |- t[ty1,...,tyn/vty1,...,vtyn]
%

%< Original code:

   let INST_TYPE inst_tylist th = 
    if null inst_tylist  then  th 
    else
    (let asl,w = dest_thm th
     and tyvl = map ((assert is_vartype) o snd) inst_tylist   in
         if exists (\ty. exists (type_in ty) asl) tyvl then fail
         else mk_thm(asl, inst (freesl asl) inst_tylist w)
    ) ? failwith `INST_TYPE`  ;;

This failed to check for variable capture (spotted by Roger Jones' team
at ICL Defence Systems). The new code uses a Lisp coded check:

   inst_rename_list : term -> term list

which returns a list of variables in a term that are in the scope of 
a lambda binding of a variable with the same name but different type.
Such bound variables are renamed if their type is instantiated.

As a slight optimization (to compensate for the loss of performance due to the
extra checking in inst_rename_list) the validity testing for INST_TYPE has
been efficiently coded in Lisp via a dml-ed function:

   inst_check : (type # type) list # term list -> term list

A call 

   inst_check [(ty1,v1); ... ;(tyn,vn)] [tm1; ... ;tmn]

returns the list of free variables in tm1, ..., tmn if:

   (i)  each vi is a type variable, and
   (ii) none of the vi occurs in any of the tm1, ... ,tmn

if (i) or (ii) fails to hold the call fails.

>%

let INST_TYPE inst_tylist th = 
    if null inst_tylist  then  th 
    else
    (let asl,w = dest_thm th
     in
     let vars = inst_check(inst_tylist,asl)
     in
     fst(mk_thm(asl, inst((inst_rename_list w)@vars) inst_tylist w),
    	 RecordStep(InstTypeStep(inst_tylist,th)))
    );;


% Discharging an assumption

        A |- t2
     --------------------    ("A-{t1}" is the set subtraction of {t1} from A)
      A-{t1} |- t1 ==> t2
%

let DISCH w th =
 fst(mk_thm(disch(w,hyp th), mk_imp(w,concl th)),
     RecordStep(DischStep(w,th))) ? failwith`DISCH`;;

% Modus Ponens

     A1 |- t1 ==> t2  ,   A2 |- t2
    -------------------------------
            A1 u A2 |- t2

CHANGED by WW 24 Jan 94.
Due to some historical reasons, dest_imp also destruct negation and
convert it iinto an implication with F in the conclusio. Therefore, the
old code shown below performs extra inferences. E.g. 
   MP (A1 |- ~t) (A2 |- t) = (A1,A2 |- F).
The new code implements a strict primitive MP rule. The behaviour of
the old MP rule is implemented by NOT_MP in hol-drule.ml.
OLD CODE:
let MP thi th =
   (let wa,wc = dest_imp (concl thi) in
    if aconv wa (concl th)
     then fst(mk_thm(union(hyp thi) (hyp th), wc), RecordStep(MpStep(thi,th)))
     else fail) ? failwith `MP`;;
%

let MP thi th = 
   (let ((c,wa),wc) = (dest_comb # I) (dest_comb (concl thi)) in
    if not((fst (dest_const c)) = `==>`) then  failwith `not an implication`
    else if aconv wa (concl th)
     then fst(mk_thm(union(hyp thi) (hyp th), wc), RecordStep(MpStep(thi,th)))
     else failwith `theorem does not alpha-convert to antecedent` ) 
    ?\s failwith (`MP: `^s);;

