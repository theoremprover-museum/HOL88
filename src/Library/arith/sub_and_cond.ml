%****************************************************************************%
% FILE          : sub_and_cond.ml                                            %
% DESCRIPTION   : Elimination of subtraction from natural number formulae    %
%                 and elimination of conditionals.                           %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 9th April 1992                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 24th June 1992                                             %
%****************************************************************************%

%----------------------------------------------------------------------------%
% COND_ABS_CONV : conv                                                       %
%----------------------------------------------------------------------------%

let COND_ABS_CONV tm =
 (let (v,bdy) = dest_abs tm
  in  let (b,x,y) = ((assert ($not o mem v o frees)) # I) (dest_cond bdy)
  in  let xf = mk_abs (v,x)
      and yf = mk_abs (v,y)
  in  let th1 = INST_TYPE [(type_of v,":*");(type_of x,":**")] COND_ABS
  in  let th2 = SPECL [b;xf;yf] th1
  in  CONV_RULE (RATOR_CONV (RAND_CONV (ABS_CONV
         (RATOR_CONV (RAND_CONV BETA_CONV) THENC RAND_CONV BETA_CONV) THENC
         ALPHA_CONV v))) th2
 ) ? failwith `COND_ABS_CONV`;;

%----------------------------------------------------------------------------%
% SUB_AND_COND_ELIM_CONV : conv                                              %
%                                                                            %
% Subtraction cannot be eliminated without eliminating conditionals that     %
% enclose the subtraction operator. This function is not as delicate as it   %
% could be: it eliminates all conditionals in arithmetic formulae as well as %
% eliminating natural number subtraction.                                    %
%                                                                            %
% Care has to be taken with the conditional lifting theorems because they    %
% can loop if they try to move a conditional past another conditional, e.g., %
%                                                                            %
%    b1 => x | (b2 => y | z)                                                 %
%                                                                            %
% Note also that these theorems are specialised for natural numbers. This    %
% prevents them from pulling the conditionals higher up the term than        %
% necessary prior to elimination.                                            %
%----------------------------------------------------------------------------%

let SUB_AND_COND_ELIM_CONV =
 letrec op_of_app tm = op_of_app (rator tm) ? tm
 in
 \tm.
 TOP_DEPTH_CONV
  (SUB_NORM_CONV ORELSEC
   COND_EXPAND_CONV ORELSEC
   NUM_COND_RATOR_CONV ORELSEC
   (\tm. if ((fst (dest_const (op_of_app tm)) = `COND`) ? false)
         then fail
         else NUM_COND_RAND_CONV tm) ORELSEC
   COND_ABS_CONV
  )
 tm;;

%----------------------------------------------------------------------------%
% COND_ELIM_CONV : conv                                                      %
%                                                                            %
% This function eliminates all conditionals in a term that it can. If the    %
% term is a formula, only an abstraction can prevent the elimination, e.g.:  %
%                                                                            %
%    COND_ELIM_CONV "(\m. (m = 0) => 0 | (m - 1)) (SUC n) = n" --->          %
%    |- ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n) =                          %
%       ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n)                            %
%                                                                            %
% Care has to be taken with the conditional lifting theorems because they    %
% can loop if they try to move a conditional past another conditional, e.g., %
%                                                                            %
%    b1 => x | (b2 => y | z)                                                 %
%                                                                            %
%----------------------------------------------------------------------------%

let COND_ELIM_CONV =
 letrec op_of_app tm = op_of_app (rator tm) ? tm
 in
 \tm.
 TOP_DEPTH_CONV
  (COND_EXPAND_CONV ORELSEC
   COND_RATOR_CONV ORELSEC
   (\tm. if ((fst (dest_const (op_of_app tm)) = `COND`) ? false)
         then fail
         else COND_RAND_CONV tm) ORELSEC
   COND_ABS_CONV
  )
 tm;;
