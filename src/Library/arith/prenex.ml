%****************************************************************************%
% FILE          : prenex.ml                                                  %
% DESCRIPTION   : Putting formulae in Prenex Normal Form                     %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 19th June 1992                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 24th June 1992                                             %
%****************************************************************************%

%----------------------------------------------------------------------------%
% QUANT_EQ_IMP_CONV : conv                                                   %
%----------------------------------------------------------------------------%

let QUANT_EQ_IMP_CONV tm =
 (let (l,r) = dest_eq tm
  in  if (is_forall l) or (is_exists l) or
         (is_forall r) or (is_exists r)
      then SPECL [l;r] EQ_IMP_THM
      else fail
 ) ? failwith `QUANT_EQ_IMP_CONV`;;

%----------------------------------------------------------------------------%
% is_prenex : term -> bool                                                   %
%----------------------------------------------------------------------------%

letrec is_prenex tm =
   letrec contains_quant tm =
      if (is_forall tm) or (is_exists tm)
      then true
      else (let (f,x) = dest_comb tm
            in  (contains_quant f) or (contains_quant x))
         ? (contains_quant (body tm))
         ? false
   in is_prenex (snd (dest_forall tm))
    ? is_prenex (snd (dest_exists tm))
    ? not (contains_quant tm);;

%----------------------------------------------------------------------------%
% PRENEX_CONV : conv                                                         %
%----------------------------------------------------------------------------%

let PRENEX_CONV tm =
 if (is_prenex tm)
 then ALL_CONV tm
 else
 TOP_DEPTH_CONV
  (\tm.
   if (is_neg tm) then (NOT_FORALL_CONV ORELSEC NOT_EXISTS_CONV) tm
   if (is_conj tm) then
      (AND_FORALL_CONV ORELSEC
       LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV ORELSEC
       AND_EXISTS_CONV ORELSEC
       LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV) tm
   if (is_disj tm) then
      (OR_FORALL_CONV ORELSEC
       LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV ORELSEC
       OR_EXISTS_CONV ORELSEC
       LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV) tm
   if (is_imp tm) then
      (LEFT_IMP_FORALL_CONV ORELSEC RIGHT_IMP_FORALL_CONV ORELSEC
       LEFT_IMP_EXISTS_CONV ORELSEC RIGHT_IMP_EXISTS_CONV) tm
   if (is_eq tm) then QUANT_EQ_IMP_CONV tm
   else fail)
 tm;;
