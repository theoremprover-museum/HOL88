%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        conv.ml                                               %
%                                                                             %
%     DESCRIPTION:      Conversions and rules defined using them              %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml      %
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
% Must be compiled in the presence of the hol parser/pretty printer     %
% This loads genfns.ml and hol-syn.ml too.                              %
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml            %
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`;
                    loadf `ml/hol-rule`;
                    loadf `ml/hol-drule`;
                    loadf `ml/drul`;
                    loadf `ml/tacticals`);;


lettype conv = term -> thm;;

% --------------------------------------------------------------------- %
% Instantiate terms and types of a theorem                              %
% --------------------------------------------------------------------- %

let INST_TY_TERM(substl,insttyl) th = INST substl (INST_TYPE insttyl th);;

% --------------------------------------------------------------------- %
% |- !x y z. w   --->  |- w[g1/x][g2/y][g3/z]                           %
% --------------------------------------------------------------------- %

letrec GSPEC th =
    let wl,w = dest_thm th in
    if is_forall w then
        GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
    else th;;

%
Match a given part of "th" to a term, instantiating "th".
The part should be free in the theorem, except for outer bound variables
%

let PART_MATCH partfn th =
    let pth = GSPEC (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth;;

% --------------------------------------------------------------------- %
% MATCH_MP: Matching Modus Ponens for implications.                     %
%                                                                       %
%    |- !x1 ... xn. P ==> Q     |- P'                                   %
% ---------------------------------------                               %
%                |- Q'                                                  %
%                                                                       %
% Matches all types in conclusion except those mentioned in hypotheses. %
%                                                                       %
% Reimplemented with bug fix [TFM 91.06.17].                            %
% OLD CODE:                                                             %
%                                                                       %
% let MATCH_MP impth =                                                  %
%  let match = PART_MATCH (fst o dest_imp) impth ? failwith `MATCH_MP`  %
%     in                                                                %
%     \th. MP (match (concl th)) th;;                                   %
%                                                                       %
% --------------------------------------------------------------------- %

%----------------------------------------------------------------------------%
% Reimplemented again [JRH 92.08.25] to fix variable capture bug and         %
% keep universal quantification in the resulting equation. Old code:         %
%                                                                            %
% let MATCH_MP impth =                                                       %
%     let hy,(vs,imp) = (I # strip_forall) (dest_thm impth) in               %
%     let pat = fst(dest_imp imp)                                            %
%                 ? failwith `MATCH_MP: not an implication` in               %
%     let fvs = subtract (frees (fst(dest_imp imp))) (freesl hy) in          %
%     let gth = GSPEC (GENL fvs (SPECL vs impth)) in                         %
%     let matchfn = match (fst(dest_imp(concl gth))) in                      %
%         \th. (MP (INST_TY_TERM (matchfn (concl th)) gth) th) ?             %
%              failwith `MATCH_MP: does not match`;;                         %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% Fixed bug (found by Sten Agerholm) arising from the fact that type         %
% instantiation may cause bound variable renaming. Following documentation   %
% added. [JRH 92.11.18]                                                      %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
%           Documentation for the workings of the new MATCH_MP               %
%           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^               %
%                                                                            %
% The two argument theorems are of the form                                  %
%                                                                            %
% ith = A |- !x1..xn. s ==> t                                                %
%  th = B |- s'                                                              %
%                                                                            %
% Extract "bod" (|s|) from "ith", and using the match function "mth", match  %
% it to (|s'|); do the type instantiation (only), giving "tth", a            %
% type-instantiated version of "ith". The type instantiation may rename      %
% bound variables, so repeat the match procedure to get the term             %
% instantiations "tmin". Now set up lists of free variables in |A| ("hy1")   %
% and |B| ("hy2"). Take apart the instantiated version of "ith" to get the   %
% quantified variables |x1|..|xn| in list "avs", and the antecedent and      %
% consequent of the implication in "ant" and "cons" respectively.            %
%                                                                            %
% Partition the free variables in the antecedent into those which are        %
% ("rvs") an are not ("fvs") free in the consequent. We will only need to    %
% instantiate those in "rvs" to get a match; however we want to rename any   %
% of the "fvs" if necessary to avoid capture problems (as in the previous    %
% version of MATCH_MP). Accordingly, set up a list of `available' variables  %
% in "afvs", which we can rename if required, either because they are not    %
% free in |A|, or are included in the set |x1|..|xn|.                        %
%                                                                            %
% Now in "cvs" we collect those variables which will be free in the          %
% consequent after instantiation: if the variable isn't in the instantiation %
% list then just the variable itself, otherwise the free variables in        %
% whatever is to be instantiated for it. Now pick variant versions in "vfvs" %
% of the variables in "afvs" to avoid clashes with these or any variables in %
% either assumption list.                                                    %
%                                                                            %
% Now create a complete set of `instantiations' in "atmin" to preform both   %
% the instantiation of these variants and those needed for the original      %
% match. Now partition those into those which do ("spl") and do not ("ill")  %
% appear among the |x1|..|xn|, and consequently can be SPEC'd or must be     %
% INST'd respectively.                                                       %
%                                                                            %
% Create an actual SPEC list in "fspl" to SPEC each variable appropriately,  %
% either to the instantiation in "spl" or otherwise to itself. (This works   %
% even if there are repetitions in the list |x1|..|xn|.) INST and SPEC       %
% accordingly to get a matched theorem, and perform the Modus Ponens,        %
% getting "mth", an instance of |t|. Finally, we want to universally         %
% quantify over (the variants of) any variables originally in |x1|..|xn|;    %
% get the associated variants in "qvs" and GENL over them (possible because  %
% the variants in "vfvs" were chosen not to be free in either |A| or |B|).   %
%----------------------------------------------------------------------------%

let MATCH_MP =
  letrec variants av vs =
    if vs = [] then [] else
    let vh = variant av (hd vs) in vh.(variants (vh.av) (tl vs))
  and frev_assoc x l =
    if l = [] then x else
    let h.t = l in if x = snd(h) then fst(h) else frev_assoc x t in
  \ith. let bod = (fst o dest_imp o snd o strip_forall o concl) ith
                ? failwith `MATCH_MP: not an implication` in
   \th. (let mfn = C match (concl th) in
         let tth = INST_TYPE (snd(mfn bod)) ith in
         let tbod = (fst o dest_imp o snd o strip_forall o concl) tth in
         let tmin = fst(mfn tbod) in
         let hy1 = freesl(hyp tth) and hy2 = freesl(hyp th) in
         let avs,ant,cons = (I # dest_imp) (strip_forall (concl tth)) in
         let rvs,fvs = partition (C free_in ant) (frees cons) in
         let afvs = subtract fvs (subtract hy1 avs) in
         let cvs = freesl (map (C frev_assoc tmin) rvs) in
         let vfvs = (variants (cvs@hy1@hy2) afvs) com afvs in
         let atmin = (filter ($not o $=) vfvs)@tmin in
         let spl,ill = partition (C mem avs o snd) atmin in
         let fspl = map (C frev_assoc spl) avs in
         let mth = MP (SPECL fspl (INST ill tth)) th in
         let qvs = mapfilter (fst o C rev_assoc vfvs) avs in
         GENL qvs mth)
        ? failwith `MATCH_MP: can't instantiate theorem`;;

% --------------------------------------------------------------------- %
% Conversion for rewrite rules of the form |- !x1 ... xn. t == u        %
% Matches x1 ... xn :    t'  ---->  |- t' == u'                         %
% Matches all types in conclusion except those mentioned in hypotheses. %
%                                                                       %
% Rewritten such that the lhs of |- t' = u' is syntactically equal to   %
% the input term, not just alpha-equivalent.             [TFM 90.07.11] %
%                                                                       %
% OLD CODE:                                                             %
%                                                                       %
%   let REWR_CONV =                                                     %
%       set_fail_prefix `REWR_CONV`                                     %
%         (PART_MATCH (fst o dest_eq));;                                %
%                                                                       %
% --------------------------------------------------------------------- %

let REWR_CONV th =
     (let instth = PART_MATCH lhs th in
      \tm. (let eqn = instth tm in
            let l = lhs(concl eqn) in
            if (l = tm) then eqn else TRANS (ALPHA tm l) eqn) ?
            failwith `REWR_CONV: lhs of theorem doesn't match term`) ?
     failwith `REWR_CONV: bad theorem argument (not an equation)`;;

%Conversion that always fails;  identity element for ORELSEC %

let NO_CONV : conv = \tm. failwith `NO_CONV`;;

%
Conversion that always succeeds, using reflexive law:   t --->  |- t==t
Identity element for THENC
%

let ALL_CONV  =  REFL;;

ml_curried_infix `THENC`;;

ml_curried_infix `ORELSEC`;;

%Apply two conversions in succession;  fail if either does%

let (conv1 THENC conv2): conv =
   \t.
    let th1 = conv1 t in
    let th2 = conv2 (rhs (concl th1)) in
    th1 TRANS th2;;

%Apply conv1;  if it fails then apply conv2%

let (conv1 ORELSEC conv2): conv =
    \t. conv1 t ? conv2 t;;

%Perform the first successful conversion of those in the list%

let FIRST_CONV convl tm =
    itlist $ORELSEC convl NO_CONV tm ? failwith `FIRST_CONV`;;

%Perform every conversion in the list%

let EVERY_CONV convl tm =
 itlist $THENC convl ALL_CONV tm ? failwith `EVERY_CONV`;;

%Apply a conversion zero or more times%

letrec REPEATC conv t = ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t;;

%Cause the conversion to fail if it does not change its input%

let CHANGED_CONV (conv:term->thm) tm =
    let th = conv tm in
    let l,r = dest_eq (concl th) in
    if aconv l r then failwith `CHANGED_CONV`
    else th;;

let TRY_CONV conv =
    conv ORELSEC ALL_CONV;;

% Apply conv to all top-level subterms of a term.
  Old version with over-subtle treatment of bound variables:

let SUB_CONV conv tm =
    if is_comb tm then
       (let rator,rand = dest_comb tm in
        MK_COMB (conv rator, conv rand))
    if is_abs tm then
       (let bv,body = dest_abs tm in
        let gv = genvar(type_of bv) in
        let bodyth = conv (subst [gv,bv] body) in
        let bv' = variant (thm_frees bodyth) bv in
        MK_ABS (GEN bv' (INST [bv',gv] bodyth)))
    else (ALL_CONV tm);;
%

let SUB_CONV conv tm =
    if is_comb tm then
       (let rator,rand = dest_comb tm in
        MK_COMB (conv rator, conv rand))
    if is_abs tm then
       (let bv,body = dest_abs tm in
        let bodyth = conv body in
        MK_ABS (GEN bv bodyth))
    else (ALL_CONV tm);;

% ===================================================================== %
% Section for defining depth conversions                 [RJB 91.04.17] %
% ===================================================================== %
begin_section depth_conv;;

% ===================================================================== %
% Conversions that use failure to indicate that they have not changed   %
% their input term, and hence save the term from being rebuilt          %
% unnecessarily.                                                        %
%                                                                       %
% Based on ideas of Roger Fleming. Implemented by Richard Boulton.      %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Failure string indicating that a term has not been changed by the     %
% conversion applied to it.                                             %
% --------------------------------------------------------------------- %

let qconv = `QCONV`;;

% --------------------------------------------------------------------- %
% QCONV : conv -> conv                                                  %
%                                                                       %
% Takes a conversion that uses failure to indicate that it has not      %
% changed its argument term, and produces an ordinary conversion.       %
% --------------------------------------------------------------------- %

let QCONV conv tm = (conv tm) ??[qconv](REFL tm);;

% --------------------------------------------------------------------- %
% ALL_QCONV : conv                                                      %
%                                                                       %
% Identity conversion for conversions using failure.                    %
% --------------------------------------------------------------------- %

let ALL_QCONV:conv = \tm. failwith qconv;;

% --------------------------------------------------------------------- %
% THENQC : conv -> conv -> conv                                         %
%                                                                       %
% Takes two conversions that use failure and produces a conversion that %
% applies them in succession. The new conversion also uses failure. It  %
% fails if neither of the two argument conversions cause a change.      %
% --------------------------------------------------------------------- %

let THENQC conv1 conv2 tm =
 (let th1 = conv1 tm
  in  ((th1 TRANS (conv2 (rhs (concl th1)))) ??[qconv] th1))
 ??[qconv] (conv2 tm);;

% --------------------------------------------------------------------- %
% ORELSEQC : conv -> conv -> conv                                       %
%                                                                       %
% Takes two conversions that use failure and produces a conversion that %
% tries the first one, and if this fails for a reason other than that   %
% the term is unchanged, it tries the second one.                       %
%                                                                       %
% Modified to use the ?\ construct, 92.03.03 by RJB.                    %
% --------------------------------------------------------------------- %

let ORELSEQC conv1 conv2 (tm:term) =
 (conv1 tm) ?\s if (s = qconv) then (failwith qconv) else (conv2 tm);;

% --------------------------------------------------------------------- %
% REPEATQC : conv -> conv                                               %
%                                                                       %
% Applies a conversion zero or more times.                              %
% --------------------------------------------------------------------- %

letrec REPEATQC conv tm =
 (ORELSEQC (THENQC conv (REPEATQC conv)) ALL_QCONV) tm;;

% --------------------------------------------------------------------- %
% CHANGED_QCONV : conv -> conv                                          %
%                                                                       %
% Causes the conversion given to fail if it does not change its input.  %
% Alpha convertibility is only tested for if the term is changed in     %
% some way.                                                             %
% --------------------------------------------------------------------- %

let CHANGED_QCONV conv (tm:term) =
 let th = (conv tm) ??[qconv] failwith `CHANGED_QCONV`
 in  let (l,r) = dest_eq (concl th)
 in  if (aconv l r)
     then failwith `CHANGED_QCONV`
     else th;;

% --------------------------------------------------------------------- %
% TRY_QCONV : conv -> conv                                              %
%                                                                       %
% Applies a conversion, and if it fails, raises a `qconv' failure       %
% indicating that the term is unchanged.                                %
% --------------------------------------------------------------------- %

let TRY_QCONV conv = ORELSEQC conv ALL_QCONV;;

% --------------------------------------------------------------------- %
% SUB_QCONV : conv -> conv                                              %
%                                                                       %
% Applies conv to all top-level subterms of a term. Set up to detect    %
% `qconv' failures when dealing with a combination. If neither the      %
% rator nor the rand are modified the `qconv' failure is propagated.    %
% Otherwise, the failure information is used to avoid unnecessary       %
% processing.                                                           %
%		                                                        %
% Optimized: MK_ABS(GEN bv bodyth) --> ABS bv bodyth     [TFM 93.07.22] %
% --------------------------------------------------------------------- %

let SUB_QCONV conv tm =
 if (is_comb tm) then
    (let (rator,rand) = dest_comb tm
     in  (let th = conv rator
          in  ((MK_COMB (th, conv rand)) ??[qconv](AP_THM th rand)))
         ??[qconv](AP_TERM rator (conv rand)))
 else if (is_abs tm) then
    (let (bv,body) = dest_abs tm
     in  let bodyth = conv body
     in  ABS bv bodyth)             % old: MK_ABS (GEN bv bodyth)) %
 else (ALL_QCONV tm);;

% --------------------------------------------------------------------- %
% SUB_ALPHA_QCONV : conv -> conv                                        %
%                                                                       %
% Modified version of SUB_QCONV for use in rewriting.                   %
% If the application of ABS fails, the conversion is attempted again    %
% on an alpha-converted version of the abstraction. This is to catch    %
% those rare cases in which a valid rewrite is rejected because one of  %
% the hypotheses has a free occurrence of the bound variable.           %
% An alternative would be to always genvar the abstraction, but the     %
% problem is sufficiently rare that it is probably more efficient on    %
% average to repeat the application of the conversion even though this  %
% may be very expensive.                                 [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let SUB_ALPHA_QCONV conv tm =
 if (is_comb tm) then
    (let (rator,rand) = dest_comb tm
     in  (let th = conv rator
          in  ((MK_COMB (th, conv rand)) ??[qconv](AP_THM th rand)))
         ??[qconv](AP_TERM rator (conv rand)))
 else if (is_abs tm) then
    (let (bv,body) = dest_abs tm
     in  let bodyth = conv body
     in  (ABS bv bodyth ?
          let v = genvar (type_of bv)
          in  let th1 = ALPHA_CONV v tm
          in  let body' = snd (dest_abs (rhs (concl th1)))
          in  let eq_thm' = ABS v (conv body')
          in  let th2 = ALPHA_CONV bv (rhs (concl eq_thm'))
          in  TRANS (TRANS th1 eq_thm') th2))
 else (ALL_QCONV tm);;

% --------------------------------------------------------------------- %
% Apply a conversion recursively to a term and its parts.               %
% The abstraction around "t" avoids infinite recursion.                 %
%                                                                       %
% Old version:                                                          %
%                                                                       %
% letrec DEPTH_CONV conv t =                                            %
%    (SUB_CONV (DEPTH_CONV conv) THENC (REPEATC conv))                  %
%    t;;                                                                %
%                                                                       %
% Parameterised over SUB_QCONV.                          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

letrec DEPTH_QCONV subconv conv tm =
 THENQC (subconv (DEPTH_QCONV subconv conv)) (REPEATQC conv) tm;;

% --------------------------------------------------------------------- %
% Optimized 13.5.93 by JVT to remove the function composition to        %
% enhance speed.                                                        %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
%    let DEPTH_CONV = QCONV o DEPTH_QCONV;;                             %
%                                                                       %
% SUB_QCONV added to instantiate new parameter.          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let DEPTH_CONV = \conv. (QCONV (DEPTH_QCONV SUB_QCONV conv));;

% --------------------------------------------------------------------- %
% Like DEPTH_CONV, but re-traverses term after each conversion          %
% Loops if the conversion function never fails                          %
%                                                                       %
% Old version:                                                          %
%                                                                       %
% letrec REDEPTH_CONV conv t =                                          %
%    (SUB_CONV (REDEPTH_CONV conv) THENC                                %
%     ((conv THENC (REDEPTH_CONV conv)) ORELSEC ALL_CONV))              %
%    t;;                                                                %
%                                                                       %
% Parameterised over SUB_QCONV.                          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

letrec REDEPTH_QCONV subconv conv tm =
 THENQC
 (subconv (REDEPTH_QCONV subconv conv))
 (ORELSEQC (THENQC conv (REDEPTH_QCONV subconv conv)) ALL_QCONV)
 tm;;

% --------------------------------------------------------------------- %
% Optimized 13.5.93 by JVT to remove the function composition to        %
% enhance speed.                                                        %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
%    let REDEPTH_CONV = QCONV o REDEPTH_QCONV;;                         %
%                                                                       %
% SUB_QCONV added to instantiate new parameter.          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let REDEPTH_CONV = \conv. (QCONV (REDEPTH_QCONV SUB_QCONV conv));;

% --------------------------------------------------------------------- %
% Rewrite the term t trying conversions at top level before descending  %
% Not true Normal Order evaluation, but may terminate where             %
% REDEPTH_CONV would loop.  More efficient than REDEPTH_CONV for        %
% rewrites that throw away many of their pattern variables.             %
%                                                                       %
% Old version:                                                          %
%                                                                       %
% letrec TOP_DEPTH_CONV conv t =                                        %
%    (REPEATC conv  THENC                                               %
%     (TRY_CONV                                                         %
%         (CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC          %
%          TRY_CONV(conv THENC TOP_DEPTH_CONV conv))))                  %
%    t;;                                                                %
%                                                                       %
% Slower, simpler version (tries conv even if SUB_CONV does nothing)    %
%                                                                       %
% letrec TOP_DEPTH_CONV conv t =                                        %
%    (REPEATC conv  THENC                                               %
%     SUB_CONV (TOP_DEPTH_CONV conv) THENC                              %
%     ((conv THENC TOP_DEPTH_CONV conv)  ORELSEC ALL_CONV))             %
%    t;;                                                                %
%                                                                       %
% Parameterised over SUB_QCONV.                          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

letrec TOP_DEPTH_QCONV subconv conv tm =
 THENQC
 (REPEATQC conv)
 (TRY_QCONV
     (THENQC (CHANGED_QCONV (subconv (TOP_DEPTH_QCONV subconv conv)))
             (TRY_QCONV (THENQC conv (TOP_DEPTH_QCONV subconv conv)))))
 tm;;

% --------------------------------------------------------------------- %
% Optimized 13.5.93 by JVT to remove the function composition to        %
% enhance speed.                                                        %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
%    let TOP_DEPTH_CONV = QCONV o TOP_DEPTH_QCONV;;                     %
%                                                                       %
% SUB_QCONV added to instantiate new parameter.          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let TOP_DEPTH_CONV = \conv. (QCONV (TOP_DEPTH_QCONV SUB_QCONV conv));;

% --------------------------------------------------------------------- %
% ONCE_DEPTH_CONV conv tm: applies conv ONCE to the first suitable      %
% sub-term(s) encountered in top-down order.                            %
%                                                                       %
% Old Version:                                                          %
%                                                                       %
% letrec ONCE_DEPTH_CONV conv tm =                                      %
%        (conv ORELSEC (SUB_CONV (ONCE_DEPTH_CONV conv))) tm;;          %
%                                                                       %
%                                                                       %
% Reimplemented: TFM 90.07.04 (optimised for speed)                     %
%                                                                       %
% This version uses failure to avoid rebuilding unchanged subterms      %
% (now superseded by more general use of failure for optimisation).     %
%                                                                       %
% let ONCE_DEPTH_CONV =                                                 %
%     letrec ODC conv tm =                                              %
%        conv tm ?                                                      %
%        (let l,r = dest_comb tm in                                     %
%             (let lth = ODC conv l in                                  %
%                (MK_COMB(lth,ODC conv r)) ? AP_THM lth r) ?            %
%             AP_TERM l (ODC conv r)) ?                                 %
%        let v,body = dest_abs tm in                                    %
%        let bodyth = ODC conv body in                                  %
%            MK_ABS (GEN v bodyth) in                                   %
%        \conv tm. ODC conv tm ? REFL tm;;                              %
%                                                                       %
%                                                                       %
% It has been discovered that TFM's optimised version had a different   %
% (and more desirable) behaviour to the original version. The version   %
% below has been modified to behave as TFM's did by the addition of the %
% call to TRY_QCONV. ONCE_DEPTH_CONV cannot now fail, whereas the       %
% original version could.                                [RJB 92.03.03] %
%                                                                       %
% Parameterised over SUB_QCONV.                          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

letrec ONCE_DEPTH_QCONV subconv conv tm =
 TRY_QCONV (ORELSEQC conv (subconv (ONCE_DEPTH_QCONV subconv conv))) tm;;

% --------------------------------------------------------------------- %
% Optimized 13.5.93 by JVT to remove the function composition to        %
% enhance speed.                                                        %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
%    let ONCE_DEPTH_CONV = QCONV o ONCE_DEPTH_QCONV;;                   %
%                                                                       %
% SUB_QCONV added to instantiate new parameter.          [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let ONCE_DEPTH_CONV = \conv. (QCONV (ONCE_DEPTH_QCONV SUB_QCONV conv));;

% --------------------------------------------------------------------- %
% Depth conversions for use in rewriting.          Added [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let REW_DEPTH_CONV = \conv. (QCONV (TOP_DEPTH_QCONV SUB_ALPHA_QCONV conv));;

let ONCE_REW_DEPTH_CONV =
   \conv. (QCONV (ONCE_DEPTH_QCONV SUB_ALPHA_QCONV conv));;

% --------------------------------------------------------------------- %
% Export depth conversions outside of section.                          %
% --------------------------------------------------------------------- %
(DEPTH_CONV,REDEPTH_CONV,TOP_DEPTH_CONV,ONCE_DEPTH_CONV,
 REW_DEPTH_CONV,ONCE_REW_DEPTH_CONV);;
end_section depth_conv;;
let (DEPTH_CONV,REDEPTH_CONV,TOP_DEPTH_CONV,ONCE_DEPTH_CONV,
     REW_DEPTH_CONV,ONCE_REW_DEPTH_CONV) = it;;


% Convert a conversion to a rule %

let CONV_RULE conv th = EQ_MP (conv(concl th)) th;;

% Convert a conversion to a tactic %

let CONV_TAC conv :tactic (asl,w) =
 let th = conv w
 in
 let left,right = dest_eq(concl th)
 in
 if right="T"
 then ([], \[]. EQ_MP (SYM th) TRUTH)
 else ([asl,right], \[th']. EQ_MP (SYM th) th');;

% Rule and tactic for beta-reducing on all beta-redexes %

let BETA_RULE = CONV_RULE(DEPTH_CONV BETA_CONV)
and BETA_TAC  = CONV_TAC (DEPTH_CONV BETA_CONV);;

% ===================================================================== %
% The stuff in boxes below is mostly from Tom Melham (tfm)              %
% ===================================================================== %

% ===================================================================== %
% What follows is a complete set of conversions for moving ! and ? into %
% and out of the basic logical connectives ~, /\, \/, ==>, and =.       %
%                                                                       %
% Naming scheme:                                                        %
%                                                                       %
%   1: for moving quantifiers inwards:  <quant>_<conn>_CONV             %
%                                                                       %
%   2: for moving quantifiers outwards: [dir]_<conn>_<quant>_CONV       %
%                                                                       %
% where                                                                 %
%                                                                       %
%   <quant> := FORALL | EXISTS                                          %
%   <conn>  := NOT | AND | OR | IMP | EQ                                %
%   [dir]   := LEFT | RIGHT                     (optional)              %
%                                                                       %
%                                                                       %
% [TFM 90.11.09]                                                        %
% ===================================================================== %

% --------------------------------------------------------------------- %
% NOT_FORALL_CONV, implements the following axiom scheme:               %
%                                                                       %
%      |- (~!x.tm) = (?x.~tm)                                           %
%                                                                       %
% --------------------------------------------------------------------- %

let NOT_FORALL_CONV tm =
    (let x,t = dest_forall(dest_neg tm) in
     let all = mk_forall(x,t) and exists = mk_exists(x,mk_neg t) in
     let nott = ASSUME (mk_neg t) in
     let th1 = DISCH all (NOT_MP nott (SPEC x (ASSUME all))) in
     let imp1 = DISCH exists (CHOOSE (x, ASSUME exists) (NOT_INTRO th1)) in
     let th2 = CCONTR t (NOT_MP (ASSUME(mk_neg exists)) (EXISTS(exists,x)nott)) in
     let th3 = CCONTR exists (NOT_MP (ASSUME (mk_neg all)) (GEN x th2)) in
     let imp2 = DISCH (mk_neg all) th3 in
         IMP_ANTISYM_RULE imp2 imp1) ?
    failwith `NOT_FORALL_CONV: argument must have the form "~!x.tm"`;;

% --------------------------------------------------------------------- %
% NOT_EXISTS_CONV, implements the following axiom scheme.               %
%                                                                       %
%       |- (~?x.tm) = (!x.~tm)                                          %
%                                                                       %
% --------------------------------------------------------------------- %

let NOT_EXISTS_CONV tm =
    (let x,t = dest_exists (dest_neg tm) in
     let all = mk_forall(x,mk_neg t) in
     let asm1 = ASSUME t in
     let thm1 = NOT_MP (ASSUME tm) (EXISTS (rand tm, x) asm1) in
     let imp1 = DISCH tm (GEN x (NOT_INTRO (DISCH t thm1))) in
     let asm2 = ASSUME  all and asm3 = ASSUME (rand tm) in
     let thm2 = DISCH (rand tm) (CHOOSE (x,asm3) (NOT_MP (SPEC x asm2) asm1)) in
     let imp2 = DISCH all (NOT_INTRO thm2) in
     IMP_ANTISYM_RULE imp1 imp2 ) ?
    failwith `NOT_EXISTS_CONV: argument must have the form "~?x.tm"`;;

% --------------------------------------------------------------------- %
% EXISTS_NOT_CONV, implements the following axiom scheme.               %
%                                                                       %
%       |- (?x.~tm) = (~!x.tm)                                          %
%                                                                       %
% --------------------------------------------------------------------- %

let EXISTS_NOT_CONV tm =
    (let xtm = mk_forall ((I # dest_neg) (dest_exists tm)) in
     SYM(NOT_FORALL_CONV (mk_neg xtm))) ?
    failwith `EXISTS_NOT_CONV: argument must have the form "?x.~tm"`;;

% --------------------------------------------------------------------- %
% FORALL_NOT_CONV, implements the following axiom scheme.               %
%                                                                       %
%       |- (!x.~tm) = (~?x.tm)                                          %
%                                                                       %
% --------------------------------------------------------------------- %

let FORALL_NOT_CONV tm =
    (let xtm = mk_exists ((I # dest_neg) (dest_forall tm)) in
     SYM(NOT_EXISTS_CONV (mk_neg xtm))) ?
    failwith `FORALL_NOT_CONV: argument must have the form "!x.~tm"`;;

% --------------------------------------------------------------------- %
% FORALL_AND_CONV : move universal quantifiers into conjunction.        %
%                                                                       %
% A call to FORALL_AND_CONV "!x. P /\ Q"  returns:                      %
%                                                                       %
%   |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)                                  %
% --------------------------------------------------------------------- %

let FORALL_AND_CONV tm =
    (let x,(P,Q) = (I # dest_conj) (dest_forall tm) in
     let Pth,Qth = CONJ_PAIR (SPEC x (ASSUME tm)) in
     let imp1 = DISCH tm (CONJ (GEN x Pth) (GEN x Qth)) in
     let xtm = rand(concl imp1) in
     let t1,t2 = (SPEC x # SPEC x) (CONJ_PAIR (ASSUME xtm)) in
     let imp2 = DISCH xtm (GEN x (CONJ t1 t2)) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `FORALL_AND_CONV: argument must have the form "!x.P/\\Q"`;;

% --------------------------------------------------------------------- %
% EXISTS_OR_CONV : move existential quantifiers into disjunction.       %
%                                                                       %
% A call to EXISTS_OR_CONV "?x. P \/ Q"  returns:                       %
%                                                                       %
%   |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)                                  %
% --------------------------------------------------------------------- %

let EXISTS_OR_CONV tm =
    (let x,(P,Q) = (I # dest_disj) (dest_exists tm) in
     let ep = mk_exists(x,P) and eq = mk_exists(x,Q) in
     let Pth = EXISTS(ep,x)(ASSUME P) and Qth = EXISTS(eq,x)(ASSUME Q) in
     let thm1 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth in
     let imp1 = DISCH tm (CHOOSE (x,ASSUME tm) thm1) in
     let t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) in
     let th1 = EXISTS(tm,x) t1 and th2 = EXISTS(tm,x) t2 in
     let e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2 in
     let thm2 = DISJ_CASES (ASSUME(mk_disj(ep,eq))) e1 e2 in
     let imp2 = DISCH (mk_disj(ep,eq)) thm2 in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `EXISTS_OR_CONV: argument must have the form "?x.P\\/Q"`;;

% --------------------------------------------------------------------- %
% AND_FORALL_CONV : move universal quantifiers out of conjunction.      %
%                                                                       %
% A call to AND_FORALL_CONV "(!x. P) /\ (!x. Q)"  returns:              %
%                                                                       %
%   |- (!x.P) /\ (!x.Q) = (!x. P /\ Q)                                  %
% --------------------------------------------------------------------- %

let AND_FORALL_CONV tm =
    (let (x,P),(y,Q) = (dest_forall # dest_forall) (dest_conj tm) in
     if (not (x=y)) then fail else
     let t1,t2 = (SPEC x # SPEC x) (CONJ_PAIR (ASSUME tm)) in
     let imp1 = DISCH tm (GEN x (CONJ t1 t2)) in
     let rtm = rand(concl imp1) in
     let Pth,Qth = CONJ_PAIR (SPEC x (ASSUME rtm)) in
     let imp2 = DISCH rtm (CONJ (GEN x Pth) (GEN x Qth)) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `AND_FORALL_CONV: expecting "(!x.P) /\\ (!x.Q)"`;;

% --------------------------------------------------------------------- %
% LEFT_AND_FORALL_CONV : move universal quantifier out of conjunction.  %
%                                                                       %
% A call to LEFT_AND_FORALL_CONV "(!x.P) /\  Q"  returns:               %
%                                                                       %
%   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)                                %
%                                                                       %
% Where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let LEFT_AND_FORALL_CONV tm =
    (let (x,P),Q = (dest_forall # I) (dest_conj tm) in
     let x' = variant (frees tm) x in
     let t1,t2 = (SPEC x' # I) (CONJ_PAIR (ASSUME tm)) in
     let imp1 = DISCH tm (GEN x' (CONJ t1 t2)) in
     let rtm = rand(concl imp1) in
     let Pth,Qth = CONJ_PAIR (SPEC x' (ASSUME rtm)) in
     let imp2 = DISCH rtm (CONJ (GEN x' Pth)  Qth) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `LEFT_AND_FORALL_CONV: expecting "(!x.P) /\\ Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_AND_FORALL_CONV : move universal quantifier out of conjunction. %
%                                                                       %
% A call to RIGHT_AND_FORALL_CONV "P /\ (!x.Q)"  returns:               %
%                                                                       %
%   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x])                               %
%                                                                       %
% where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let RIGHT_AND_FORALL_CONV tm =
    (let P,(x,Q) = (I # dest_forall) (dest_conj tm) in
     let x' = variant (frees tm) x in
     let t1,t2 = (I # SPEC x') (CONJ_PAIR (ASSUME tm)) in
     let imp1 = DISCH tm (GEN x' (CONJ t1 t2)) in
     let rtm = rand(concl imp1) in
     let Pth,Qth = CONJ_PAIR (SPEC x' (ASSUME rtm)) in
     let imp2 = DISCH rtm (CONJ Pth (GEN x' Qth)) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `RIGHT_AND_FORALL_CONV: expecting "P /\\ (!x.Q)"`;;

% --------------------------------------------------------------------- %
% OR_EXISTS_CONV : move existential quantifiers out of disjunction.     %
%                                                                       %
% A call to OR_EXISTS_CONV "(?x. P) \/ (?x. Q)"  returns:               %
%                                                                       %
%   |- (?x.P) \/ (?x.Q) = (?x. P \/ Q)                                  %
% --------------------------------------------------------------------- %

let OR_EXISTS_CONV tm =
    (let ep,eq = dest_disj tm in
     let (x,P),(y,Q) = (dest_exists # dest_exists) (ep,eq) in
     if (not (x=y)) then fail else
     let otm = mk_exists (x,(mk_disj(P,Q))) in
     let t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) in
     let th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2 in
     let e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2 in
     let thm1 = DISJ_CASES (ASSUME(mk_disj(ep,eq))) e1 e2 in
     let imp1 = DISCH (mk_disj(ep,eq)) thm1 in
     let Pth = EXISTS(ep,x)(ASSUME P) and Qth = EXISTS(eq,x)(ASSUME Q) in
     let thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth in
     let imp2 = DISCH otm (CHOOSE (x,ASSUME otm) thm2) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `OR_EXISTS_CONV: expecting "(?x.P) \\/ (?x.Q)"`;;

% --------------------------------------------------------------------- %
% LEFT_OR_EXISTS_CONV : move existential quantifier out of disjunction. %
%                                                                       %
% A call to LEFT_OR_EXISTS_CONV "(?x.P) \/  Q"  returns:                %
%                                                                       %
%   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)                                %
%                                                                       %
% Where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let LEFT_OR_EXISTS_CONV tm =
    (let ep,Q = dest_disj tm in
     let (x,P) = dest_exists ep in
     let x' = variant (frees tm) x in
     let newp = subst[x',x] P in
     let otm = mk_exists (x',(mk_disj(newp,Q))) in
     let t1 = DISJ1 (ASSUME newp) Q and t2 = DISJ2 newp (ASSUME Q) in
     let th1 = EXISTS(otm,x') t1 and th2 = EXISTS(otm,x') t2 in
     let thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x',ASSUME ep)th1) th2 in
     let imp1 = DISCH tm thm1 in
     let Pth = EXISTS(ep,x')(ASSUME newp) and Qth = ASSUME Q in
     let thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(newp,Q))) Pth Qth in
     let imp2 = DISCH otm (CHOOSE (x',ASSUME otm) thm2) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `LEFT_OR_EXISTS_CONV: expecting "(?x.P) \\/ Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_OR_EXISTS_CONV: move existential quantifier out of disjunction. %
%                                                                       %
% A call to RIGHT_OR_EXISTS_CONV "P \/ (?x.Q)"  returns:                %
%                                                                       %
%   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x])                               %
%                                                                       %
% where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let RIGHT_OR_EXISTS_CONV tm =
    (let P,eq = dest_disj tm in
     let (x,Q) = dest_exists eq in
     let x' = variant (frees tm) x in
     let newq = subst[x',x] Q in
     let otm = mk_exists (x',(mk_disj(P,newq))) in
     let t1 = DISJ2 P (ASSUME newq)  and t2 = DISJ1 (ASSUME P) newq in
     let th1 = EXISTS(otm,x') t1 and th2 = EXISTS(otm,x') t2 in
     let thm1 = DISJ_CASES (ASSUME tm) th2 (CHOOSE(x',ASSUME eq)th1) in
     let imp1 = DISCH tm thm1 in
     let Qth = EXISTS(eq,x')(ASSUME newq) and Pth = ASSUME P in
     let thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,newq))) Pth Qth in
     let imp2 = DISCH otm (CHOOSE (x',ASSUME otm) thm2) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `RIGHT_OR_EXISTS_CONV: expecting "P \\/ (?x.Q)"`;;

% --------------------------------------------------------------------- %
% EXISTS_AND_CONV : move existential quantifier into conjunction.       %
%                                                                       %
% A call to EXISTS_AND_CONV "?x. P /\ Q"  returns:                      %
%                                                                       %
%    |- (?x. P /\ Q) = (?x.P) /\ Q        [x not free in Q]             %
%    |- (?x. P /\ Q) = P /\ (?x.Q)        [x not free in P]             %
%    |- (?x. P /\ Q) = (?x.P) /\ (?x.Q)   [x not free in P /\ Q]        %
% --------------------------------------------------------------------- %

let EXISTS_AND_CONV tm =
    (let x,(P,Q) = (I # dest_conj) (dest_exists tm) ?
                   failwith `expecting "?x. P /\\ Q"` in
     let fP = free_in x P and fQ =  free_in x Q in
     if (fP & fQ) then
         failwith `"` ^ (fst(dest_var x)) ^ `" free in both conjuncts` else
     let t1,t2 = CONJ_PAIR(ASSUME (mk_conj(P,Q))) in
     let eP = (fQ => t1 | EXISTS (mk_exists(x,P),x) t1) and
         eQ = (fP => t2 | EXISTS (mk_exists(x,Q),x) t2) in
     let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (CONJ eP eQ)) in
     let th = EXISTS (tm,x) (CONJ(ASSUME P) (ASSUME Q)) in
     let th1 = (fP or not fQ => CHOOSE(x,ASSUME(mk_exists(x,P)))th | th) in
     let thm1 = (fQ or not fP => CHOOSE(x,ASSUME(mk_exists(x,Q)))th1 | th1) in
     let otm = rand(concl imp1) in
     let t1,t2 = CONJ_PAIR(ASSUME otm) in
     let thm2 = PROVE_HYP t1 (PROVE_HYP t2 thm1) in
         IMP_ANTISYM_RULE imp1 (DISCH otm thm2)) ?\st
    failwith `EXISTS_AND_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% AND_EXISTS_CONV : move existential quantifier out of conjunction.     %
%                                                                       %
%   |- (?x.P) /\ (?x.Q) = (?x. P /\ Q)                                  %
%                                                                       %
% provided x is free in neither P nor Q.                                %
% --------------------------------------------------------------------- %

let AND_EXISTS_CONV tm =
    (let (x,P),(y,Q) = (dest_exists # dest_exists) (dest_conj tm) ?
                       failwith `expecting "(?x.P) /\\ (?x.Q)"` in
     if (not(x=y)) then failwith `expecting "(?x.P) /\\ (?x.Q)"` else
     if (free_in x P or free_in x Q) then
         failwith `"` ^ (fst(dest_var x)) ^ `" free in conjunct(s)` else
         SYM (EXISTS_AND_CONV(mk_exists(x,mk_conj(P,Q))))) ?\st
    failwith `AND_EXISTS_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% LEFT_AND_EXISTS_CONV: move existential quantifier out of conjunction  %
%                                                                       %
% A call to LEFT_AND_EXISTS_CONV "(?x.P) /\  Q"  returns:               %
%                                                                       %
%   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q)                                %
%                                                                       %
% Where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let LEFT_AND_EXISTS_CONV tm =
    (let ep,Q = dest_conj tm in
     let (x,P) = dest_exists ep in
     let x' = variant (frees tm) x in
     let newp = subst[x',x]P in
     let otm = mk_exists(x',mk_conj(newp,Q)) in
     let EP,Qth = CONJ_PAIR(ASSUME tm) in
     let thm1 = EXISTS(otm,x')(CONJ(ASSUME newp)(ASSUME Q)) in
     let imp1 = DISCH tm (MP (DISCH Q (CHOOSE(x',EP)thm1)) Qth) in
     let t1,t2 = CONJ_PAIR (ASSUME (mk_conj(newp,Q))) in
     let thm2 = CHOOSE (x',ASSUME otm) (CONJ (EXISTS (ep,x') t1) t2) in
         IMP_ANTISYM_RULE imp1 (DISCH otm thm2)) ?
    failwith `LEFT_AND_EXISTS_CONV: expecting "(?x.P) /\\ Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_AND_EXISTS_CONV: move existential quantifier out of conjunction %
%                                                                       %
% A call to RIGHT_AND_EXISTS_CONV "P /\ (?x.Q)"  returns:               %
%                                                                       %
%   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x])                               %
%                                                                       %
% where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let RIGHT_AND_EXISTS_CONV tm =
    (let P,eq = dest_conj tm in
     let (x,Q) = dest_exists eq in
     let x' = variant (frees tm) x in
     let newq = subst[x',x]Q in
     let otm = mk_exists(x',mk_conj(P,newq)) in
     let Pth,EQ = CONJ_PAIR(ASSUME tm) in
     let thm1 = EXISTS(otm,x')(CONJ(ASSUME P)(ASSUME newq)) in
     let imp1 = DISCH tm (MP (DISCH P (CHOOSE(x',EQ)thm1)) Pth) in
     let t1,t2 = CONJ_PAIR (ASSUME (mk_conj(P,newq))) in
     let thm2 = CHOOSE (x',ASSUME otm) (CONJ t1 (EXISTS (eq,x') t2)) in
         IMP_ANTISYM_RULE imp1 (DISCH otm thm2)) ?
    failwith `RIGHT_AND_EXISTS_CONV: expecting "P /\\ (?x.Q)"`;;


% --------------------------------------------------------------------- %
% FORALL_OR_CONV : move universal quantifier into disjunction.          %
%                                                                       %
% A call to FORALL_OR_CONV "!x. P \/ Q"  returns:                       %
%                                                                       %
%   |- (!x. P \/ Q) = (!x.P) \/ Q        [if x not free in Q]           %
%   |- (!x. P \/ Q) = P \/ (!x.Q)        [if x not free in P]           %
%   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)   [if x free in neither P nor Q] %
% --------------------------------------------------------------------- %

let FORALL_OR_CONV tm =
    (let x,(P,Q) = (I # dest_disj) (dest_forall tm) ?
                   failwith `expecting "!x. P \\/ Q"` in
     let fP = free_in x P and fQ =  free_in x Q in
     if (fP & fQ) then
         failwith `"` ^ (fst(dest_var x)) ^ `" free in both disjuncts` else
     let thm1 = SPEC x (ASSUME tm) in
     let imp1 =
         if fP then
            let thm2 = CONTR P (NOT_MP (ASSUME (mk_neg Q)) (ASSUME Q)) in
            let thm3 = DISJ1 (GEN x (DISJ_CASES thm1 (ASSUME P) thm2)) Q in
            let thm4 = DISJ2 (mk_forall(x,P)) (ASSUME Q) in
                DISCH tm (DISJ_CASES (SPEC Q EXCLUDED_MIDDLE) thm4 thm3) else
         if fQ then
            let thm2 = CONTR Q (NOT_MP (ASSUME (mk_neg P)) (ASSUME P)) in
            let thm3 = DISJ2 P (GEN x (DISJ_CASES thm1 thm2 (ASSUME Q))) in
            let thm4 = DISJ1 (ASSUME P) (mk_forall(x,Q)) in
                DISCH tm (DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm4 thm3) else
            let t1,t2 = (GEN x(ASSUME P), GEN x(ASSUME Q)) in
                DISCH tm (DISJ_CASES_UNION thm1 t1 t2) in
        let otm = rand(concl imp1) in
        let op,oq = dest_disj otm in
        let thm5 = (fP or not fQ => SPEC x | I) (ASSUME op) in
        let thm6 = (fQ or not fP => SPEC x | I) (ASSUME oq) in
        let imp2 = GEN x (DISJ_CASES_UNION (ASSUME otm) thm5 thm6) in
            IMP_ANTISYM_RULE imp1 (DISCH otm imp2))  ?\st
    failwith `FORALL_OR_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% OR_FORALL_CONV : move existential quantifier out of conjunction.      %
%                                                                       %
%   |- (!x.P) \/ (!x.Q) = (!x. P \/ Q)                                  %
%                                                                       %
% provided x is free in neither P nor Q.                                %
% --------------------------------------------------------------------- %

let OR_FORALL_CONV tm =
    (let (x,P),(y,Q) = (dest_forall # dest_forall) (dest_disj tm) ?
                       failwith `expecting "(!x.P) \\/ (!x.Q)"` in
     if (not(x=y)) then failwith `expecting "(!x.P) \\/ (!x.Q)"` else
     if (free_in x P or free_in x Q) then
         failwith `"` ^ (fst(dest_var x)) ^ `" free in disjuncts(s)` else
         SYM (FORALL_OR_CONV(mk_forall(x,mk_disj(P,Q))))) ?\st
    failwith `OR_FORALL_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% LEFT_OR_FORALL_CONV : move universal quantifier out of conjunction.   %
%                                                                       %
% A call to LEFT_OR_FORALL_CONV "(!x.P) \/  Q"  returns:                %
%                                                                       %
%   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q)                                %
%                                                                       %
% Where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let LEFT_OR_FORALL_CONV tm =
    (let (x,P),Q = (dest_forall # I) (dest_disj tm) in
     let x' = variant (frees tm) x in
     let newp = subst[x',x]P in
     let Pth = DISJ1 (SPEC x' (ASSUME (mk_forall(x,P)))) Q in
     let Qth = DISJ2 newp (ASSUME Q) in
     let imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth)) in
     let otm = rand(concl imp1) in
     let thm1 = SPEC x' (ASSUME otm) in
     let thm2 = CONTR newp (NOT_MP(ASSUME(mk_neg Q))(ASSUME Q)) in
     let thm3 = DISJ1 (GEN x' (DISJ_CASES thm1 (ASSUME newp) thm2)) Q in
     let thm4 = DISJ2 (mk_forall(x,P)) (ASSUME Q) in
     let imp2 = DISCH otm(DISJ_CASES(SPEC Q EXCLUDED_MIDDLE)thm4 thm3) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `LEFT_OR_FORALL_CONV: expecting "(!x.P) \\/ Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_OR_FORALL_CONV : move universal quantifier out of conjunction.  %
%                                                                       %
% A call to RIGHT_OR_FORALL_CONV "P \/ (!x.Q)"  returns:                %
%                                                                       %
%   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x])                               %
%                                                                       %
% where x' is a primed variant of x not free in the input term          %
% --------------------------------------------------------------------- %

let RIGHT_OR_FORALL_CONV tm =
    (let P,(x,Q) = (I # dest_forall) (dest_disj tm) in
     let x' = variant (frees tm) x in
     let newq = subst[x',x]Q in
     let Qth = DISJ2 P (SPEC x' (ASSUME (mk_forall(x,Q)))) in
     let Pth = DISJ1 (ASSUME P) newq in
     let imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth)) in
     let otm = rand(concl imp1) in
     let thm1 = SPEC x' (ASSUME otm) in
     let thm2 = CONTR newq (NOT_MP(ASSUME(mk_neg P))(ASSUME P)) in
     let thm3 = DISJ2 P (GEN x' (DISJ_CASES thm1 thm2 (ASSUME newq))) in
     let thm4 = DISJ1 (ASSUME P) (mk_forall(x,Q)) in
     let imp2 = DISCH otm(DISJ_CASES(SPEC P EXCLUDED_MIDDLE)thm4 thm3) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `RIGHT_OR_FORALL_CONV: expecting "P \\/ (!x.Q)"`;;

% --------------------------------------------------------------------- %
% FORALL_IMP_CONV, implements the following axiom schemes.              %
%                                                                       %
%       |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))     [x not free in P]     %
%                                                                       %
%       |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)     [x not free in Q]     %
%                                                                       %
%       |- (!x. P==>Q) = ((?x.P) ==> (!x.Q))      [x not free in P==>Q] %
% --------------------------------------------------------------------- %

let FORALL_IMP_CONV tm =
    (let x,(P,Q) = (I # dest_imp) (dest_forall tm) ?
                   failwith `expecting "!x. P ==> Q"` in
     let fP = free_in x P and fQ =  free_in x Q in
     if (fP & fQ) then
         failwith `"`^(fst(dest_var x))^`" free on both sides of "==>"` else
     if fP then
        let asm = mk_exists(x,P) in
        let th1 = CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm))) in
        let imp1 = DISCH tm (DISCH asm th1) in
        let cncl = rand(concl imp1) in
        let th2 = MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P)) in
        let imp2 = DISCH cncl (GEN x (DISCH P th2)) in
            IMP_ANTISYM_RULE imp1 imp2 else
     if fQ then
        let imp1 = DISCH P(GEN x(UNDISCH(SPEC x(ASSUME tm)))) in
        let cncl = concl imp1 in
        let imp2 = GEN x (DISCH P(SPEC x(UNDISCH (ASSUME cncl)))) in
            IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2) else
        let asm = mk_exists(x,P) in
        let th1 = GEN x (CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm)))) in
        let imp1 = DISCH tm (DISCH asm th1) in
        let cncl = rand(concl imp1) in
        let th2 = SPEC x (MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P))) in
        let imp2 = DISCH cncl (GEN x (DISCH P th2)) in
            IMP_ANTISYM_RULE imp1 imp2) ?\st
    failwith `FORALL_IMP_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% LEFT_IMP_EXISTS_CONV, implements the following theorem-scheme:        %
%                                                                       %
%    |- (?x. t1[x]) ==> t2  =  !x'. t1[x'] ==> t2                       %
%                                                                       %
% where x' is a variant of x chosen not to be free in (?x.t1[x])==>t2   %
%                                                                       %
% Author: Tom Melham                                                    %
% Revised: [TFM 90.07.01]                                               %
%---------------------------------------------------------------------- %

let LEFT_IMP_EXISTS_CONV tm =
    (let t1,t2 = dest_imp tm in
     let x,t = dest_exists t1 in
     let x' = variant (frees tm) x in
     let t' = subst [x',x] t in
     let th1 = GEN x' (DISCH t'(MP(ASSUME tm)(EXISTS(t1,x')(ASSUME t')))) in
     let rtm = concl th1 in
     let th2 = CHOOSE (x',ASSUME t1) (UNDISCH(SPEC x'(ASSUME rtm))) in
         IMP_ANTISYM_RULE (DISCH tm th1) (DISCH rtm (DISCH t1 th2))) ?
    failwith `LEFT_IMP_EXISTS_CONV: expecting "(?x.P) ==> Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_IMP_FORALL_CONV, implements the following theorem-scheme:       %
%                                                                       %
%    |- (t1 ==> !x. t2)  =  !x'. t1 ==> t2[x'/x]                        %
%                                                                       %
% where x' is a variant of x chosen not to be free in the input term.   %
%---------------------------------------------------------------------- %

let RIGHT_IMP_FORALL_CONV tm =
    (let t1,t2 = dest_imp tm in
     let x,t = dest_forall t2 in
     let x' = variant (frees tm) x in
     let t' = subst [x',x] t in
     let imp1 = DISCH tm (GEN x' (DISCH t1(SPEC x'(UNDISCH(ASSUME tm))))) in
     let ctm = rand(concl imp1) in
     let alph = GEN_ALPHA_CONV x (mk_forall(x',t')) in
     let thm1 = EQ_MP alph (GEN x'(UNDISCH (SPEC x' (ASSUME ctm)))) in
     let imp2 = DISCH ctm (DISCH t1 thm1) in
         IMP_ANTISYM_RULE imp1 imp2) ?
    failwith `RIGHT_IMP_FORALL_CONV: expecting "P ==> (!x.Q)"`;;


% --------------------------------------------------------------------- %
% EXISTS_IMP_CONV, implements the following axiom schemes.              %
%                                                                       %
%       |- (?x. P==>Q[x]) = (P ==> (?x.Q[x]))     [x not free in P]     %
%                                                                       %
%       |- (?x. P[x]==>Q) = ((!x.P[x]) ==> Q)     [x not free in Q]     %
%                                                                       %
%       |- (?x. P==>Q) = ((!x.P) ==> (?x.Q))      [x not free in P==>Q] %
% --------------------------------------------------------------------- %

let EXISTS_IMP_CONV tm =
    (let x,(P,Q) = (I # dest_imp) (dest_exists tm) ?
                   failwith `expecting "?x. P ==> Q"` in
     let fP = free_in x P and fQ =  free_in x Q in
     if (fP & fQ) then
         failwith `"`^(fst(dest_var x))^`" free on both sides of "==>"` else
     if fP then
        let allp = mk_forall(x,P) in
        let th1 = SPEC x (ASSUME allp) in
        let thm1 = MP (ASSUME(mk_imp(P,Q))) th1 in
        let imp1 = DISCH tm (CHOOSE(x,ASSUME tm)(DISCH allp thm1)) in
        let otm = rand(concl imp1) in
        let thm2 = EXISTS(tm,x)(DISCH P (UNDISCH(ASSUME otm))) in
        let nex =  mk_exists(x,mk_neg P) in
        let asm1 = EXISTS (nex, x) (ASSUME (mk_neg P)) in
        let th2 = CCONTR P (NOT_MP (ASSUME (mk_neg nex)) asm1) in
        let th3 = CCONTR nex (NOT_MP (ASSUME (mk_neg allp)) (GEN x th2)) in
        let thm4 = DISCH P (CONTR Q (UNDISCH (ASSUME (mk_neg P)))) in
        let thm5 = CHOOSE(x,th3)(EXISTS(tm,x)thm4) in
        let thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5 in
            IMP_ANTISYM_RULE imp1 (DISCH otm thm6) else
     if fQ then
        let thm1 = EXISTS (mk_exists(x,Q),x) (UNDISCH(ASSUME(mk_imp(P,Q)))) in
        let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (DISCH P thm1)) in
        let thm2 = UNDISCH (ASSUME (rand(concl imp1))) in
        let thm3 = CHOOSE (x,thm2) (EXISTS (tm,x) (DISCH P (ASSUME Q))) in
        let thm4 = EXISTS(tm,x)(DISCH P(CONTR Q(UNDISCH(ASSUME(mk_neg P)))))in
        let thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4 in
            IMP_ANTISYM_RULE imp1 (DISCH(rand(concl imp1)) thm5) else
        let eQ = mk_exists(x,Q) and aP = mk_forall(x,P) in
        let thm1 = EXISTS(eQ,x)(UNDISCH(ASSUME(mk_imp(P,Q)))) in
        let thm2 = DISCH aP (PROVE_HYP (SPEC x (ASSUME aP)) thm1) in
        let imp1 = DISCH tm (CHOOSE(x,ASSUME tm) thm2) in
        let thm2 = CHOOSE(x,UNDISCH (ASSUME (rand(concl imp1)))) (ASSUME Q) in
        let thm3 = DISCH P (PROVE_HYP (GEN x (ASSUME P)) thm2) in
        let imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,x) thm3) in
            IMP_ANTISYM_RULE imp1 imp2) ?\st
    failwith `EXISTS_IMP_CONV: ` ^ st;;

% --------------------------------------------------------------------- %
% LEFT_IMP_FORALL_CONV, implements the following theorem-scheme:        %
%                                                                       %
%    |- (!x. t1[x]) ==> t2  =  ?x'. t1[x'] ==> t2                       %
%                                                                       %
% where x' is a variant of x chosen not to be free in the input term    %
%---------------------------------------------------------------------- %

let LEFT_IMP_FORALL_CONV tm =
    (let allt1,t2 = dest_imp tm in
     let (x,t1) = dest_forall allt1 in
     let x' = variant (frees tm) x in
     let t1' = subst [x',x] t1 in
     let th1 = SPEC x' (ASSUME allt1) in
     let thm1 = MP (ASSUME(mk_imp(t1',t2))) th1 in
     let otm = mk_exists(x',mk_imp(t1',t2)) in
     let imp1 = DISCH otm (CHOOSE(x',ASSUME otm)(DISCH allt1 thm1)) in
     let thm2 = EXISTS(otm,x') (DISCH t1' (UNDISCH(ASSUME tm))) in
     let nex =  mk_exists(x',mk_neg t1') in
     let asm1 = EXISTS (nex, x') (ASSUME (mk_neg t1')) in
     let th2 = CCONTR t1' (NOT_MP (ASSUME (mk_neg nex)) asm1) in
     let th3 = CCONTR nex (NOT_MP (ASSUME (mk_neg allt1)) (GEN x' th2)) in
     let thm4 = DISCH t1' (CONTR t2 (UNDISCH (ASSUME (mk_neg t1')))) in
     let thm5 = CHOOSE(x',th3)(EXISTS(mk_exists(x',concl thm4),x')thm4) in
     let thm6 = DISJ_CASES (SPEC allt1 EXCLUDED_MIDDLE) thm2 thm5 in
         IMP_ANTISYM_RULE (DISCH tm thm6) imp1) ?
    failwith `LEFT_IMP_FORALL_CONV: expecting "(!x.P) ==> Q"`;;

% --------------------------------------------------------------------- %
% RIGHT_IMP_EXISTS_CONV, implements the following theorem-scheme:       %
%                                                                       %
%    |- (t1 ==> ?x. t2)  =  ?x'. t1 ==> t2[x'/x]                        %
%                                                                       %
% where x' is a variant of x chosen not to be free in the input term.   %
%---------------------------------------------------------------------- %

let RIGHT_IMP_EXISTS_CONV tm =
    (let t1,(x,t2) = (I # dest_exists) (dest_imp tm) in
     let x' = variant (frees tm) x in
     let t2' = subst [x',x] t2 in
     let otm = mk_exists(x',mk_imp(t1,t2')) in
     let thm1 = EXISTS(mk_exists(x,t2),x')(UNDISCH(ASSUME(mk_imp(t1,t2')))) in
     let imp1 = DISCH otm (CHOOSE(x',ASSUME otm) (DISCH t1 thm1)) in
     let thm2 = UNDISCH (ASSUME tm) in
     let thm3 = CHOOSE (x',thm2) (EXISTS (otm,x') (DISCH t1 (ASSUME t2'))) in
     let thm4 = DISCH t1 (CONTR t2'(UNDISCH(ASSUME(mk_neg t1)))) in
     let thm5 = EXISTS(otm,x') thm4 in
     let thm6 = DISJ_CASES (SPEC t1 EXCLUDED_MIDDLE) thm3 thm5 in
         IMP_ANTISYM_RULE (DISCH tm thm6) imp1) ?
    failwith `RIGHT_IMP_EXISTS_CONV: expecting "Q ==> (?x.P)"`;;

% --------------------------------------------------------------------- %
% X_SKOLEM_CONV : introduce a skolem function.                          %
%                                                                       %
%   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                  %
%        =                                                              %
%      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]                          %
%                                                                       %
% The first argument is the function f.                                 %
%                                                                       %
% Changed to fail unless there is at least one variable x1..xn.         %
%                                                     [JRH 93.02.05]    %
% --------------------------------------------------------------------- %

let X_SKOLEM_CONV v =
    if (not(is_var v)) then
       failwith `X_SKOLEM_CONV: first argument not a variable` else
    \tm. (let xs,(y,P) = (assert($not o null) # dest_exists) (strip_forall tm) ?
              failwith `expecting "!x1...xn. ?y.tm"` in
          let fx = list_mk_comb(v,xs) ?
              failwith `function variable has the wrong type` in
          if (free_in v tm) then
              failwith `"`^(fst(dest_var v))^`" free in the input term` else
          let pat = mk_exists(v,list_mk_forall(xs,subst[fx,y]P)) in
          let fn = list_mk_abs(xs,mk_select(y,P)) in
          let bth = SYM(LIST_BETA_CONV (list_mk_comb(fn,xs))) in
          let thm1 = SUBST [bth,y] P (SELECT_RULE (SPECL xs (ASSUME tm))) in
          let imp1 = DISCH tm (EXISTS (pat,fn) (GENL xs thm1)) in
          let thm2 = SPECL xs (ASSUME (snd(dest_exists pat))) in
          let thm3 = GENL xs (EXISTS (mk_exists(y,P),fx) thm2) in
          let imp2 = DISCH pat (CHOOSE (v,ASSUME pat) thm3) in
              IMP_ANTISYM_RULE imp1 imp2) ?\st
          failwith `X_SKOLEM_CONV: ` ^st;;

% --------------------------------------------------------------------- %
% SKOLEM_CONV : introduce a skolem function.                            %
%                                                                       %
%   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                  %
%        =                                                              %
%      (?y'. !x1...xn. tm[x1,..,xn,y' x1 ... xn]                        %
%                                                                       %
% Where y' is a primed variant of y not free in the input term.         %
% --------------------------------------------------------------------- %

let SKOLEM_CONV =
    let mkfty tm ty = mk_type(`fun`,[type_of tm;ty]) in
    \tm. (let xs,(y,P) = (I # dest_exists) (strip_forall tm) in
          let fv = mk_var(fst(dest_var y), itlist mkfty xs (type_of y)) in
              X_SKOLEM_CONV (variant (frees tm) fv) tm) ?
         failwith `expecting "!x1...xn. ?y.tm"`;;

% --------------------------------------------------------------------- %
% SYM_CONV : a conversion for symmetry of equality.                     %
%                                                                       %
% e.g. SYM_CONV "x=y"   ---->   (x=y) = (y=x).                          %
%                                                                       %
% Replaced by version below: TFM 88.03.31                               %
% --------------------------------------------------------------------- %

let SYM_CONV tm =
    (let lhs,rhs = dest_eq tm in
     SPECL [lhs;rhs] (INST_TYPE [type_of lhs,":*"] EQ_SYM_EQ)) ?
    failwith `SYM_CONV`;;

% First a function for converting a conversion to a rule %

%
    A |- t1 = t2
   --------------   (t2' got from t2 using a conversion)
    A |- t1 = t2'
%

let RIGHT_CONV_RULE conv th = th TRANS (conv(rhs(concl th)));;

% --------------------------------------------------------------------- %
% FUN_EQ_CONV "f = g"  returns:  |- (f = g) = !x. (f x = g x).          %
%                                                                       %
% Notes: f and g must be functions. The conversion choses an "x" not    %
% free in f or g. This conversion just states that functions are equal  %
% IFF the results of applying them to an arbitrary value are equal.     %
%                                                                       %
% New version: TFM 88.03.31                                             %
% --------------------------------------------------------------------- %

let FUN_EQ_CONV tm =
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = `fun`
       then let varnm =
                if (is_vartype ty1) then `x` else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_primed_var(varnm,ty1)) in
            let imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x)) in
            let asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x))) in
            IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
       else failwith `FUN_EQ_CONV`;;

% --------------------------------------------------------------------- %
% X_FUN_EQ_CONV "x" "f = g"                                             %
%                                                                       %
% yields |- (f = g) = !x. f x = g x                                     %
%                                                                       %
% fails if x free in f or g, or x not of the right type.                %
% --------------------------------------------------------------------- %

let X_FUN_EQ_CONV x tm =
    (if not(is_var x) then failwith ` first arg is not a variable` else
     if (mem x (frees tm)) then
        failwith fst(dest_var x) ^ ` is a free variable` else
     let l = (lhs tm ? failwith `not an equation`) in
     let check = assert (\x. x = `fun`) in
     let _,[ty1;ty2] = ((check # I) (dest_type(type_of l)) ?
                        failwith `lhs and rhs not functions`) in
     if not (ty1 = type_of x) then
        failwith fst(dest_var x) ^ ` has the wrong type` else
     let imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x)) in
     let asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x))) in
               IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))) ?\st
    failwith `X_FUN_EQ_CONV: ` ^ st;;



% --------------------------------------------------------------------- %
% CONTRAPOS_CONV: convert an implication to its contrapositive.         %
%                                                                       %
% CONTRAPOS_CONV "a ==> b" --> |- (a ==> b) = (~b ==> ~a)               %
%                                                                       %
% Added: TFM 88.03.31                                                   %
% Revised: TFM 90.07.13                                                 %
% Changed: WW 24 Jan 94 Due to changes in dest_imp and MP		%
% --------------------------------------------------------------------- %

let CONTRAPOS_CONV tm =
    (let a,c = dest_imp tm in
     let negc = mk_neg c and contra = mk_imp(mk_neg c,mk_neg a) in
     let imp1 = DISCH negc (NOT_INTRO
    	    	(IMP_TRANS(ASSUME tm)(NOT_ELIM(ASSUME negc)))) and
         imp2 = DISCH a (CCONTR c (UNDISCH (UNDISCH (ASSUME contra)))) in
         IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH contra imp2)) ?
    failwith `CONTRAPOS_CONV: input term not an implication`;;

% --------------------------------------------------------------------- %
% ANTE_CONJ_CONV: convert an implication with conjuncts in its          %
%                 antecedant to a series of implications.               %
%                                                                       %
% ANTE_CONJ_CONV "a1 /\ a2 ==> c"                                       %
%       ----> |- a1 /\ a2 ==> c = (a1 ==> (a2 ==> c))                   %
%                                                                       %
% Added: TFM 88.03.31                                                   %
% --------------------------------------------------------------------- %

let ANTE_CONJ_CONV tm =
    let (a1,a2),c = (dest_conj # I) (dest_imp tm) in
    let imp1 = MP (ASSUME tm) (CONJ (ASSUME a1) (ASSUME a2)) and
        imp2 = LIST_MP [CONJUNCT1 (ASSUME "^a1 /\ ^a2");
                        CONJUNCT2 (ASSUME "^a1 /\ ^a2")]
                       (ASSUME "^a1 ==> (^a2 ==> ^c)") in
    IMP_ANTISYM_RULE (DISCH_ALL (DISCH a1 (DISCH a2 imp1)))
                     (DISCH_ALL (DISCH "^a1 /\ ^a2" imp2))?
    failwith `ANTE_CONJ_CONV`;;

% --------------------------------------------------------------------- %
% SWAP_EXISTS_CONV: swap the order of existentially quantified vars.    %
%                                                                       %
% SWAP_EXISTS_CONV "?x y.t[x,y]" ---> |- ?x y.t[x,y] = ?y x.t[x,y]      %
%                                                                       %
% AUTHOR: Paul Loewenstein 3 May 1988                                   %
% --------------------------------------------------------------------- %

let SWAP_EXISTS_CONV xyt =
    (let x,yt = dest_exists (xyt) in
     let y, t = dest_exists (yt) in
     let xt = mk_exists (x, t) in
     let yxt = mk_exists (y, xt) in
       IMP_ANTISYM_RULE
         (DISCH xyt (CHOOSE (x,ASSUME xyt) (CHOOSE (y, (ASSUME yt))
          (EXISTS (yxt,y) (EXISTS (xt,x) (ASSUME t))))))
         (DISCH yxt (CHOOSE (y,ASSUME yxt) (CHOOSE (x, (ASSUME xt))
         (EXISTS (xyt,x) (EXISTS (yt,y) (ASSUME t))))))) ?
      failwith `SWAP_EXISTS_CONV`;;

% --------------------------------------------------------------------- %
% RAND_CONV conv "t1 t2" applies conv to t2                             %
%                                                                       %
% Added TFM 88.03.31                                                    %
% Revised TFM 91.03.08                                                  %
% Revised RJB 91.04.17                                                  %
% --------------------------------------------------------------------- %

let RAND_CONV conv tm =
    let rator,rand = (dest_comb tm ? failwith `RAND_CONV`) in
    let randth = conv rand in
        (AP_TERM rator randth ? failwith `RAND_CONV`);;

% --------------------------------------------------------------------- %
% RATOR_CONV conv "t1 t2" applies conv to t1                            %
%                                                                       %
% Added TFM 88.03.31                                                    %
% Revised TFM 91.03.08                                                  %
% Revised RJB 91.04.17                                                  %
% --------------------------------------------------------------------- %

let RATOR_CONV conv tm =
    let rator,rand = (dest_comb tm ? failwith `RATOR_CONV`) in
    let ratorth = conv rator in
        (AP_THM ratorth rand ? failwith `RATOR_CONV`);;

% --------------------------------------------------------------------- %
% ABS_CONV conv "\x. t[x]" applies conv to t[x]                         %
%                                                                       %
% Added TFM 88.03.31                                                    %
% Revised RJB 91.04.17                                                  %
% --------------------------------------------------------------------- %

let ABS_CONV conv tm =
    let bv,body = (dest_abs tm ? failwith `ABS_CONV`) in
    let bodyth = conv body in
        (ABS bv bodyth ? failwith `ABS_CONV`);;

% --------------------------------------------------------------------- %
% SELECT_CONV: a conversion for introducing "?" when P [@x.P[x]].       %
%                                                                       %
% SELECT_CONV "P [@x.P [x]]" ---> |- P [@x.P [x]] = ?x. P[x]            %
%                                                                       %
% Added: TFM 88.03.31                                                   %
%                                                                       %
% let SELECT_CONV tm =                                                  %
%    (let epsl = find_terms is_select tm in                             %
%     let findfn t =                                                    %
%         subst [t, fst (dest_select t)] (snd (dest_select t)) = tm in  %
%     let sel = find findfn epsl in                                     %
%     let ex  = mk_exists(dest_select sel) in                           %
%     let imp1 = DISCH_ALL (SELECT_RULE (ASSUME ex)) and                %
%         imp2 = DISCH_ALL (EXISTS (ex,sel) (ASSUME tm)) in             %
%     IMP_ANTISYM_RULE imp2 imp1) ? failwith `SELECT_CONV`;;            %
%                                                                       %
% Optimised     [JG 92.04.24]                                           %
% Bugfix        [TFM 92.05.07]                                          %
% Generalised   [JG 93.10.19]                                           %
% --------------------------------------------------------------------- %

let SELECT_CONV =
    let SELECT_THM =
        let f = "f:*->bool" in
        let tyv = mk_vartype `*` in
        let th1 = AP_THM EXISTS_DEF f in
        let th2 = (CONV_RULE (RAND_CONV BETA_CONV)) th1 in
			GEN f (SYM th2) in
	\tm. 
		let right t =
			is_select t &
			let (v,b) = dest_select t in aconv tm (subst[t,v] b) in
		let fn = rand (find_term right tm) in
		let th1 = ISPEC fn SELECT_THM in
		let th2 = SYM (BETA_CONV(lhs(concl th1))) in
		let th3 = ALPHA tm (lhs(concl th2)) in
			  th3 TRANS th2 TRANS th1 ? failwith `SELECT_CONV` ;;

% --------------------------------------------------------------------- %
% bool_EQ_CONV: conversion for boolean equality.                        %
%                                                                       %
% bool_EQ_CONV "b1 = b2" returns:                                       %
%                                                                       %
%    |- (b1 = b2) = T      if b1 and b2 are identical boolean terms     %
%    |- (b1 = b2)  = b2    if b1 = "T"                                  %
%    |- (b1 = b2)  = b1    if b2 = "T"                                  %
%                                                                       %
% Added TFM 88.03.31                                                    %
% Revised TFM 90.07.24                                                  %
% --------------------------------------------------------------------- %

let bool_EQ_CONV =
    let check = let boolty = ":bool" in assert \tm. type_of tm = boolty in
    let Tb.bT._ = map (GEN "b:bool") (CONJUNCTS(SPEC "b:bool" EQ_CLAUSES)) in
    let T = "T" and F = "F" in
    \tm. (let l,r = (I # check) (dest_eq tm) in
          if (l=r) then EQT_INTRO (REFL l) else
          if (l=T) then SPEC r Tb else
          if (r=T) then SPEC l bT else fail) ?
         failwith `bool_EQ_CONV`;;

% --------------------------------------------------------------------- %
% EXISTS_UNIQUE_CONV: expands with the definition of unique existence.  %
%                                                                       %
%                                                                       %
% EXISTS_UNIQUE_CONV "?!x.P[x]" yields the theorem:                     %
%                                                                       %
%     |- ?!x.P[x] = ?x.P[x] /\ !x y. P[x] /\ P[y] ==> (x=y)             %
%                                                                       %
% ADDED: TFM 90.05.06                                                   %
%                                                                       %
% REVISED: now uses a variant of x for y in 2nd conjunct [TFM 90.06.11] %
% --------------------------------------------------------------------- %

let EXISTS_UNIQUE_CONV =
    let check = assert \c. (fst(dest_const c) = `?!`) in
    let MK_BIN f (e1,e2) = MK_COMB((AP_TERM f e1),e2) and
        MK_ALL x y tm = let rule = CONV_RULE o RAND_CONV o GEN_ALPHA_CONV in
                        rule y (FORALL_EQ x tm) and
        AND = "/\" and IMP = "==>" in
    let conv (nx,ny) t =
        let [ox;oy],A,C = (I # dest_imp) (strip_forall t) in
        let A' = MK_BIN AND ((BETA_CONV # BETA_CONV) (dest_conj A)) in
                 MK_ALL ox nx (MK_ALL oy ny (MK_BIN IMP (A',REFL C))) and
        v = genvar ":bool" in
    \tm. (let _,(x,body) = (check # dest_abs) (dest_comb tm) in
          let def = INST_TYPE [type_of x,":*"] EXISTS_UNIQUE_DEF in
          let exp = RIGHT_BETA(AP_THM def (mk_abs(x,body))) and
                y = variant (vars body) x in
          let eqn = conv (x,y) (rand(rand(concl exp))) in
              SUBST [eqn,v] (mk_eq(tm,mk_conj(mk_exists(x,body),v))) exp) ?
          failwith `EXISTS_UNIQUE_CONV: arg must have the form "?!x. P[x]"`;;

% --------------------------------------------------------------------- %
% COND_CONV: conversion for simplifying conditionals:                   %
%                                                                       %
%   --------------------------- COND_CONV "T => u | v"                  %
%     |- (T => u | v) = u                                               %
%                                                                       %
%                                                                       %
%   --------------------------- COND_CONV "F => u | v"                  %
%     |- (F => u | v) = v                                               %
%                                                                       %
%                                                                       %
%   --------------------------- COND_CONV "b => u | u"                  %
%     |- (b => u | u) = u                                               %
%                                                                       %
%   --------------------------- COND_CONV "b => u | v"  (u =alpha v)    %
%     |- (b => u | v) = u                                               %
%                                                                       %
% COND_CONV "P=>u|v" fails if P is neither "T" nor "F" and u =/= v.     %
% --------------------------------------------------------------------- %

let COND_CONV =
    let T = "T" and F = "F" and vt = genvar ":*" and vf =  genvar ":*" in
    let gen = GENL [vt;vf] in
    let CT,CF = (gen # gen) (CONJ_PAIR (SPECL [vt;vf] COND_CLAUSES)) in
    \tm. let P,u,v = dest_cond tm ? failwith `COND_CONV: not a conditional` in
         let ty = type_of u in
         if (P=T) then SPEC v (SPEC u (INST_TYPE [ty,":*"] CT)) else
         if (P=F) then SPEC v (SPEC u (INST_TYPE [ty,":*"] CF)) else
         if (u=v) then SPEC u (SPEC P (INST_TYPE [ty,":*"] COND_ID)) else
         if (aconv u v) then
            let cnd = AP_TERM (rator tm) (ALPHA v u) in
            let thm = SPEC u (SPEC P (INST_TYPE [ty,":*"] COND_ID)) in
                TRANS cnd thm else
    failwith `COND_CONV: can't simplify conditional` ;;


% --------------------------------------------------------------------- %
% PAIRED_BETA_CONV: Generalized beta conversions for tupled lambda      %
%                   abstractions applied to tuples (i.e. redexes)       %
%                                                                       %
% Given the term:                                                       %
%                                                                       %
%   "(\(x1, ... ,xn).t) (t1, ... ,tn)"                                  %
%                                                                       %
% PAIRED_BETA_CONV proves that:                                         %
%                                                                       %
%   |- (\(x1, ... ,xn).t) (t1, ... ,tn) = t[t1, ... ,tn/x1, ... ,xn]    %
%                                                                       %
% where t[t1,...,tn/x1,...,xn] is the result of substituting ti for xi  %
% in parallel in t, with suitable renaming of variables to prevent      %
% free variables in t1,...,tn becoming bound in the result.             %
%                                                                       %
% The conversion works for arbitrarily nested tuples.  For example:     %
%                                                                       %
%   PAIRED_BETA_CONV "(\((a,b),(c,d)).t) ((1,2),(3,4))"                 %
%                                                                       %
% gives:                                                                %
%                                                                       %
%  |- (\((a,b),(c,d)).t) ((1,2),(3,4)) = t[1,2,3,4/a,b,c,d]             %
%                                                                       %
% Bugfix: INST used instead of SPEC to avoid priming.    [TFM 91.04.17] %
% --------------------------------------------------------------------- %

let PAIRED_BETA_CONV =
    let vs = map genvar [":* -> (** -> ***)";":*";":**"] in
    let DEF = SPECL vs UNCURRY_DEF in
    let check = assert \t.(fst(dest_const t)) = `UNCURRY` in
    let RBCONV = RATOR_CONV BETA_CONV THENC BETA_CONV in
    letrec conv tm =
       let (_,f),x,y = (((check # I)o dest_comb) # dest_pair)(dest_comb tm) in
       let [t1;ty'] = snd(dest_type (type_of f)) in
       let [t2;t3] = snd(dest_type ty') in
       let inst = INST_TYPE [t1,":*";t2,":**";t3,":***"] DEF in
       let fv,[xv;yv] = strip_comb(rand(concl inst)) in
       let def = INST [y,yv;x,xv;f,fv] inst in
       if (is_abs f) then
          if (is_abs (snd(dest_abs f))) then
             TRANS def (RBCONV (rhs(concl def))) else
             let thm = AP_THM (BETA_CONV (mk_comb(f,x))) y in
                 TRANS def (CONV_RULE (RAND_CONV conv) thm) else
          let rec = conv (rator(rand(concl def))) in
          if (is_abs (rhs(concl rec))) then
             TRANS def (RIGHT_BETA (AP_THM rec y)) else
             let thm = conv(mk_comb(rhs(concl rec),y)) in
                 TRANS def (TRANS (AP_THM rec y) thm) in
    \tm. conv tm ? failwith `PAIRED_BETA_CONV`;;

%-------------------------------------------------------%
% PAIRED_ETA_CONV "\(x1,.(..).,xn). P (x1,.(..).,xn)" = %
%       |- \(x1,.(..).,xn). P (x1,.(..).,xn) = P        %
% [JRH 91.07.17]                                        %
%-------------------------------------------------------%

let PAIRED_ETA_CONV =
  let pthm = GEN_ALL (SYM (SPEC_ALL PAIR)) in
  letrec pairify tm =
    (let step = ISPEC tm pthm in
     let res = rhs (concl step) in
     let ((pop,l),r) = (dest_comb #I) (dest_comb res) in
     TRANS step (MK_COMB(AP_TERM pop (pairify l),pairify r)))
    ? REFL tm in
  \tm. (let (vs,bod) = dest_pabs tm in
        let (f,_) = (I # assert (curry $= vs)) (dest_comb bod) in
        let xv = mk_var(`x`,type_of vs) in
        let peq = pairify xv in
        let par = rhs (concl peq) in
        let bth = PAIRED_BETA_CONV (mk_comb(tm,par)) in
        EXT (GEN xv (SUBS [SYM peq] bth))) ? failwith `PAIRED_ETA_CONV`;;

%--------------------------------------------------------------------%
% GEN_BETA_CONV - reduces single or paired abstractions, introducing %
% arbitrarily nested "FST" and "SND" if the rand is not sufficiently %
% paired. Example:                                                   %
%                                                                    %
%   #GEN_BETA_CONV "(\(x,y). x + y) numpair";;                       %
%   |- (\(x,y). x + y)numpair = (FST numpair) + (SND numpair)        %
% [JRH 91.07.17]                                                     %
%--------------------------------------------------------------------%

let GEN_BETA_CONV =
  let ucheck = assert (curry$= `UNCURRY` o fst o dest_const)
  and pair = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) PAIR
  and uncth = SPEC_ALL UNCURRY_DEF in
  letrec gbc tm =
    let (abst,arg) = dest_comb tm in
    if is_abs abst then BETA_CONV tm else
    let (unc,ran) = (ucheck # I) (dest_comb abst) in
    let eqv = (is_pair arg) => REFL arg | ISPEC arg pair in
    let (l,r) = dest_pair (rhs (concl eqv)) in
    let res = AP_TERM abst eqv in
    let rt0 = TRANS res (PART_MATCH lhs uncth (rhs (concl res))) in
    let (tm1a,tm1b) = dest_comb (rhs (concl rt0)) in
    let rt1 = AP_THM (gbc tm1a) tm1b in
    let tm2 = rhs (concl rt1) in let rt2 = gbc tm2 in
    rt0 TRANS rt1 TRANS rt2 in
  \tm. gbc tm ? failwith `GEN_BETA_CONV`;;


begin_section let_CONV;;

% --------------------------------------------------------------------- %
% Internal function: ITER_BETA_CONV (iterated, tupled beta-conversion). %
%                                                                       %
% The conversion ITER_BETA_CONV reduces terms of the form:              %
%                                                                       %
%     (\v1 v2...vn.tm) x1 x2 ... xn xn+1 ... xn+i                       %
%                                                                       %
% where the v's can be varstructs. The behaviour is similar to          %
% LIST_BETA_CONV, but this function also does paired abstractions.      %
% --------------------------------------------------------------------- %

letrec ITER_BETA_CONV tm =
   (let rat,rnd = dest_comb tm in
    let thm = AP_THM (ITER_BETA_CONV rat) rnd in
    let redex = rand(concl thm) in
    let red = TRY_CONV(BETA_CONV ORELSEC PAIRED_BETA_CONV) redex in
        TRANS thm red) ? REFL tm;;

% --------------------------------------------------------------------- %
% Internal function: ARGS_CONV (apply a list of conversions to the      %
% arguments of a curried function application).                         %
%                                                                       %
% ARGS_CONV [conv1;...;convn] "f a1 ... an" applies convi to ai.        %
% --------------------------------------------------------------------- %

let ARGS_CONV =
    letrec appl fs as =
       if (null fs) then (null as => [] | failwith `appl`) else
          ((hd fs)(hd as)) . appl (tl fs) (tl as) in
    \cs tm. let f,ths = (I # appl cs) (strip_comb tm) in
                rev_itlist (C (curry MK_COMB)) ths (REFL f);;

% --------------------------------------------------------------------- %
% Internal function RED_WHERE.                                          %
%                                                                       %
% Given the arguments "f" and "tm[f]", this function produces a         %
% conversion that will apply ITER_BETA_CONV to its argument at all      %
% subterms that correspond to occurrences of f (bottom-up).             %
% --------------------------------------------------------------------- %

letrec RED_WHERE fn body =
   if ((is_var body) or (is_const body)) then REFL else
   ((let _,bd = dest_abs body in ABS_CONV (RED_WHERE fn bd)) ?
    let f,args = strip_comb body in
    if (f=fn)
       then ARGS_CONV (map(RED_WHERE fn)args) THENC ITER_BETA_CONV
       else let f,a = dest_comb body in
            (RAND_CONV(RED_WHERE fn a)) THENC (RATOR_CONV (RED_WHERE fn f)));;


% --------------------------------------------------------------------- %
% Internal function: REDUCE                                             %
%                                                                       %
% This function does the appropriate beta-reductions in the result of   %
% expanding a let-term.  For terms of the form:                         %
%                                                                       %
%      "let f x1 ... xn = t in tm[f]"                                   %
%                                                                       %
% we have that:                                                         %
%                                                                       %
%      th |- <let term> = tm[\x1 ... xn. t/f]                           %
%                                                                       %
% And the arguments x and f will be:                                    %
%                                                                       %
%       x = \x1 ... xn. t                                               %
%       f = \f. tm[f]                                                   %
%                                                                       %
% REDUCE searches in tm[f] for places in which f occurs, and then does  %
% an iterated beta-reduction (possibly of varstruct-abstractions) in    %
% the right-hand side of the input theorem th, at the places that       %
% correspond to occurrences of f in tm[f].                              %
% --------------------------------------------------------------------- %

let REDUCE =
    let is_uncurry tm = (fst(dest_const(rator tm)) = `UNCURRY`) ? false in
    \f x th. if (not((is_abs x) or (is_uncurry x))) then th else
             let (fn,body) = dest_abs f in
             CONV_RULE (RAND_CONV (RED_WHERE fn body)) th;;

% --------------------------------------------------------------------- %
% let_CONV: conversion for reducing "let" terms.                        %
%                                                                       %
% Given a term:                                                         %
%                                                                       %
%   "let v1 = x1 and ... and vn = xn in tm[v1,...,vn]"                  %
%                                                                       %
% let_CONV proves that:                                                 %
%                                                                       %
%   |- let v1 = x1 and ... and vn = xn in tm[v1,...,vn]                 %
%       =                                                               %
%      tm[x1,...,xn/v1,...,vn]                                          %
%                                                                       %
% where t[t1,...,tn/x1,...,xn] is the result of "substituting" the      %
% value xi for vi  in parallel in tm (see below).                       %
%                                                                       %
% Note that the vi's can take any one of the following forms:           %
%                                                                       %
%    Variables:    "x" etc.                                             %
%    Tuples:       "(x,y)" "(a,b,c)" "((a,b),(c,d))" etc.               %
%    Applications: "f (x,y) z" "f x" etc.                               %
%                                                                       %
% Variables are just substituted for. With tuples, the substitution is  %
% done component-wise, and function applications are effectively        %
% rewritten in the body of the let-term.                                %
% --------------------------------------------------------------------- %

let let_CONV =
    let v1 = ":*" and v2 = ":**" in
    let def = definition `bool` `LET_DEF` in
    let ista tm = ((fst(dest_const(rator tm)) = `UNCURRY`) ? false) in
    letrec conv tm =
       let f,x = (dest_let tm) in
       let _,[ty1;ty2] = dest_type(type_of f) in
       let defn = INST_TYPE [ty1,v1; ty2,v2] def in
       let thm = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM defn f))x) in
       if (is_abs f) then REDUCE f x (RIGHT_BETA thm) else
       if (ista f) then CONV_RULE (RAND_CONV PAIRED_BETA_CONV) thm else
           let thm1 = AP_THM(AP_TERM (rator(rator tm)) (conv f))x in
               CONV_RULE (RAND_CONV conv) thm1 in
    \tm. conv tm ? failwith `let_CONV: cannot reduce the let`;;

let_CONV;;

end_section let_CONV;;

let let_CONV  = it;;

% ===================================================================== %
% Rules defined using conversions.                                      %
% ===================================================================== %


% --------------------------------------------------------------------- %
% EXISTENCE: derives existence from unique existence:                   %
%                                                                       %
%    |- ?!x. P[x]                                                       %
% --------------------                                                  %
%    |- ?x. P[x]                                                        %
%                                                                       %
% --------------------------------------------------------------------- %

let EXISTENCE =
    let EXISTS_UNIQUE_DEF = definition `bool` `EXISTS_UNIQUE_DEF` in
    let P = "P:*->bool" in
    let th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF) in
    let th2 = CONJUNCT1(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1)))) in
    let imp = GEN P (DISCH "$?! ^P" th2) in
    let dest = let check = assert \c. (fst(dest_const c) = `?!`) in
               (dest_abs o snd) o (check # I) o dest_comb in
    \th. (let (x,P) = dest (concl th) in
          let ty = type_of x in
              MP (SPEC(mk_abs(x,P)) (INST_TYPE [ty,":*"] imp)) th) ?
         failwith `EXISTENCE: input thm have the form |- ?!x. tm`;;


%------------------------------------------------------------------------%
% AC_CONV - Prove equality using associative + commutative laws          %
%                                                                        %
% The conversion is given an associative and commutative law (it deduces %
% the relevant operator and type from these) in the form of the inbuilt  %
% ones, and an equation to prove. It will try to prove this. Example:    %
%                                                                        %
%  AC_CONV(ADD_ASSOC,ADD_SYM) "(1 + 3) + (2 + 4) = 4 + (3 + (2 + 1))"    %
% [JRH 91.07.17]                                                         %
%------------------------------------------------------------------------%

let AC_CONV(associative,commutative) tm =
  (let op = (rator o rator o lhs o snd o strip_forall o concl) commutative in
   let ty = (hd o snd o dest_type o type_of) op in
   let x = mk_var(`x`,ty) and y = mk_var(`y`,ty) and z = mk_var(`z`,ty) in
   let xy = mk_comb(mk_comb(op,x),y) and yz = mk_comb(mk_comb(op,y),z)
   and yx = mk_comb(mk_comb(op,y),x) in
   let comm = PART_MATCH I commutative (mk_eq(xy,yx))
   and ass = PART_MATCH I (SYM (SPEC_ALL associative))
              (mk_eq(mk_comb(mk_comb(op,xy),z),mk_comb(mk_comb(op,x),yz))) in
   let asc = TRANS (SUBS [comm] (SYM ass)) (INST[(x,y); (y,x)] ass) in
   let init = TOP_DEPTH_CONV (REWR_CONV ass) tm in
   let gl = rhs (concl init) in

   letrec bubble head expr =
     let ((xop,l),r) = (dest_comb # I) (dest_comb expr) in
     if xop = op then
       if l = head then REFL expr else
       if r = head then INST [(l,x); (r,y)] comm
       else let subb = bubble head r in
            let eqv =  AP_TERM (mk_comb(xop,l)) subb
            and ((yop,l'),r') = (dest_comb # I)
                     (dest_comb (snd (dest_eq (concl subb)))) in
            TRANS eqv (INST[(l,x); (l',y); (r',z)] asc)
     else fail in

   letrec asce (l,r) =
     if l = r then REFL l
     else let ((zop,l'),r') = (dest_comb # I) (dest_comb l) in
          if zop = op then
            let beq = bubble l' r in
            let rt = snd (dest_eq (concl beq)) in
              TRANS (AP_TERM (mk_comb(op,l'))
                      (asce ((snd (dest_comb l)),(snd (dest_comb rt)))))
                    (SYM beq)
          else fail in

   EQT_INTRO (EQ_MP (SYM init) (asce (dest_eq gl))))
  ? failwith `AC_CONV`;;

%------------------------------------------------------------------------%
% GSYM - General symmetry rule                                           %
%                                                                        %
% Reverses the first equation(s) encountered in a top-down search.       %
%                                                                        %
% [JRH 92.03.28]                                                         %
%------------------------------------------------------------------------%

let GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);;
