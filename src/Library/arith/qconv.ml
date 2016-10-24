%****************************************************************************%
% FILE          : qconv.ml                                                   %
% DESCRIPTION   : Conversions that use failure to avoid rebuilding unchanged %
%                 subterms.                                                  %
%                 Based on ideas of Roger Fleming and Tom Melham.            %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 15th March 1991                                            %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%----------------------------------------------------------------------------%
% Failure string indicating that a term has not been changed by the          %
% conversion applied to it.                                                  %
%----------------------------------------------------------------------------%

let qconv = `QCONV`;;

%----------------------------------------------------------------------------%
% qfailwith : string -> string -> *                                          %
%                                                                            %
% Function for trapping all failures except qconv. To be used as follows:    %
%                                                                            %
%    (...) ?\s qfailwith s `new_failure_string`                              %
%----------------------------------------------------------------------------%

let qfailwith s s' = if (s = qconv) then failwith qconv else failwith s';;

%----------------------------------------------------------------------------%
% QCONV : conv -> conv                                                       %
%                                                                            %
% Takes a conversion that uses failure to indicate that it has not changed   %
% its argument term, and produces an ordinary conversion.                    %
%----------------------------------------------------------------------------%

let QCONV conv tm = (conv tm) ??[qconv](REFL tm);;

%----------------------------------------------------------------------------%
% ALL_QCONV : conv                                                           %
%                                                                            %
% Identity conversion for conversions using failure.                         %
%----------------------------------------------------------------------------%

let ALL_QCONV:conv = \tm. failwith qconv;;

%----------------------------------------------------------------------------%
% THENQC : conv -> conv -> conv                                              %
%                                                                            %
% Takes two conversions that use failure and produces a conversion that      %
% applies them in succession. The new conversion also uses failure. It fails %
% if neither of the two argument conversions cause a change.                 %
%----------------------------------------------------------------------------%

ml_curried_infix `THENQC`;;

let THENQC conv1 conv2 tm =
 (let th1 = conv1 tm
  in  ((th1 TRANS (conv2 (rhs (concl th1)))) ??[qconv] th1))
 ??[qconv] (conv2 tm);;

%----------------------------------------------------------------------------%
% ORELSEQC : conv -> conv -> conv                                            %
%                                                                            %
% Takes two conversions that use failure and produces a conversion that      %
% tries the first one, and if this fails for a reason other than that the    %
% term is unchanged, it tries the second one.                                %
%----------------------------------------------------------------------------%

ml_curried_infix `ORELSEQC`;;

let ORELSEQC (conv1:conv) conv2 tm =
 (conv1 tm) ?\s if (s = qconv) then (failwith qconv) else (conv2 tm);;

%----------------------------------------------------------------------------%
% REPEATQC : conv -> conv                                                    %
%                                                                            %
% Applies a conversion zero or more times.                                   %
%----------------------------------------------------------------------------%

letrec REPEATQC conv tm =
 ((conv THENQC (REPEATQC conv)) ORELSEQC ALL_QCONV) tm;;

%----------------------------------------------------------------------------%
% CHANGED_QCONV : conv -> conv                                               %
%                                                                            %
% Causes the conversion given to fail if it does not change its input. Alpha %
% convertibility is only tested for if the term is changed in some way.      %
%----------------------------------------------------------------------------%

let CHANGED_QCONV conv (tm:term) =
 let th = (conv tm) ??[qconv] failwith `CHANGED_QCONV`
 in  let (l,r) = dest_eq (concl th)
 in  if (aconv l r)
     then failwith `CHANGED_QCONV`
     else th;;

%----------------------------------------------------------------------------%
% TRY_QCONV : conv -> conv                                                   %
%                                                                            %
% Applies a conversion, and if it fails, raises a `qconv' failure indicating %
% that the term is unchanged.                                                %
%----------------------------------------------------------------------------%

let TRY_QCONV conv =
 ORELSEQC conv ALL_QCONV;;

%----------------------------------------------------------------------------%
% QCONV_RULE : conv -> thm -> thm                                            %
%                                                                            %
% Generates a rule from a conversion that uses failure to avoid rebuilding   %
% unchanged subterms.                                                        %
%----------------------------------------------------------------------------%

let QCONV_RULE = CONV_RULE o QCONV;;

%----------------------------------------------------------------------------%
% RAND_QCONV : conv -> conv                                                  %
%                                                                            %
% Applies a conversion to the rand of a term, propagating any failure that   %
% indicates that the subterm is unchanged.                                   %
%----------------------------------------------------------------------------%

let RAND_QCONV conv tm =
 let (rator,rand) = dest_comb tm ? failwith `RAND_QCONV`
 in  AP_TERM rator (conv rand);;

%----------------------------------------------------------------------------%
% RATOR_QCONV : conv -> conv                                                 %
%                                                                            %
% Applies a conversion to the rator of a term, propagating any failure that  %
% indicates that the subterm is unchanged.                                   %
%----------------------------------------------------------------------------%

let RATOR_QCONV conv tm =
 let (rator,rand) = dest_comb tm ? failwith `RATOR_QCONV`
 in  AP_THM (conv rator) rand;;

%----------------------------------------------------------------------------%
% ABS_QCONV : conv -> conv                                                   %
%                                                                            %
% Applies a conversion to the body of an abstraction, propagating any        %
% failure that indicates that the subterm is unchanged.                      %
%----------------------------------------------------------------------------%

let ABS_QCONV conv tm =
 let (bv,body) = dest_abs tm ? failwith `ABS_QCONV`
 in  let bodyth = conv body
 in  ABS bv bodyth ? failwith `ABS_QCONV`;;

%----------------------------------------------------------------------------%
% ARGS_QCONV : conv -> conv                                                  %
%                                                                            %
% Applies conv to the arguments of a binary operator.                        %
% Set up to detect `qconv' failures. If neither argument is modified the     %
% `qconv' failure is propagated. Otherwise, the failure information is used  %
% to avoid unnecessary processing.                                           %
%----------------------------------------------------------------------------%

let ARGS_QCONV conv tm =
   let (fx,y) = dest_comb tm ? failwith `ARGS_QCONV`
   in  let (f,x) = dest_comb fx ? failwith `ARGS_QCONV`
   in  (let th = AP_TERM f (conv x)
        in  ((MK_COMB (th, conv y)) ??[qconv](AP_THM th y)))
       ??[qconv](AP_TERM fx (conv y));;
