%****************************************************************************%
% FILE          : thm_convs.ml                                               %
% DESCRIPTION   : Conversions for rewriting with arithmetic theorems.        %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 8th October 1992                                           %
%****************************************************************************%

%============================================================================%
% Conversions for rewriting Boolean terms                                    %
%============================================================================%

CONJ_ASSOC_NORM_CONV := REWR_CONV (GSYM CONJ_ASSOC);;

DISJ_ASSOC_NORM_CONV := REWR_CONV (GSYM DISJ_ASSOC);;

EQ_EXPAND_CONV := REWR_CONV EQ_EXPAND;;

IMP_EXPAND_CONV := REWR_CONV IMP_DISJ_THM;;

IMP_F_EQ_F_CONV := REWR_CONV IMP_F_EQ_F;;

IMP_IMP_CONJ_IMP_CONV := REWR_CONV AND_IMP_INTRO;;

LEFT_DIST_NORM_CONV := REWR_CONV LEFT_AND_OVER_OR;;

NOT_CONJ_NORM_CONV :=
 REWR_CONV
  (GEN_ALL (CONJUNCT1 (SPECL ["t1:bool";"t2:bool"] DE_MORGAN_THM)));;

NOT_DISJ_NORM_CONV :=
 REWR_CONV
  (GEN_ALL (CONJUNCT2 (SPECL ["t1:bool";"t2:bool"] DE_MORGAN_THM)));;

NOT_NOT_NORM_CONV := REWR_CONV (CONJUNCT1 NOT_CLAUSES);;

OR_F_CONV := REWR_CONV (el 3 (CONJUNCTS (SPEC "x:bool" OR_CLAUSES)));;

RIGHT_DIST_NORM_CONV := REWR_CONV RIGHT_AND_OVER_OR;;

%============================================================================%
% Conversions for rewriting arithmetic terms                                 %
%============================================================================%

ADD_ASSOC_CONV := REWR_CONV (theorem `arithmetic` `ADD_ASSOC`);;

ADD_SYM_CONV := REWR_CONV (theorem `arithmetic` `ADD_SYM`);;

GATHER_BOTH_CONV :=
 REWR_CONV
  (SYM (SPECL ["a:num";"b:num";"x:num"]
         (theorem `arithmetic` `RIGHT_ADD_DISTRIB`)));;

GATHER_LEFT_CONV :=
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL ["x:num";"n:num"]
                           (theorem `arithmetic` `MULT_CLAUSES`)))]
    (SYM (SPECL ["a:num";"1";"x:num"]
           (theorem `arithmetic` `RIGHT_ADD_DISTRIB`))));;

GATHER_NEITHER_CONV := REWR_CONV (GSYM (theorem `arithmetic` `TIMES2`));;

GATHER_RIGHT_CONV :=
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL ["x:num";"n:num"]
                           (theorem `arithmetic` `MULT_CLAUSES`)))]
    (SYM (SPECL ["1";"b:num";"x:num"]
           (theorem `arithmetic` `RIGHT_ADD_DISTRIB`))));;

GEQ_NORM_CONV := REWR_CONV (theorem `arithmetic` `GREATER_EQ`);;

GREAT_NORM_CONV :=
 REWR_CONV
  (SUBS [SYM (SPECL ["m:num";"n:num"] (definition `arithmetic` `GREATER`));
         SPEC "n:num" (theorem `arithmetic` `SUC_ONE_ADD`)]
    (SPECL ["n:num";"m:num"] (theorem `arithmetic` `LESS_EQ`)));;

LEFT_ADD_DISTRIB_CONV := REWR_CONV (theorem `arithmetic` `LEFT_ADD_DISTRIB`);;

LESS_NORM_CONV :=
 REWR_CONV
  (SUBS [SPEC "m:num" (theorem `arithmetic` `SUC_ONE_ADD`)]
    (SPECL ["m:num";"n:num"] (theorem `arithmetic` `LESS_EQ`)));;

MULT_ASSOC_CONV := REWR_CONV (theorem `arithmetic` `MULT_ASSOC`);;

MULT_COMM_CONV := REWR_CONV MULT_COMM;;

NOT_GEQ_NORM_CONV :=
 REWR_CONV
  (SUBS [SPEC "m:num" (theorem `arithmetic` `SUC_ONE_ADD`)]
    (SPECL ["m:num";"n:num"] (theorem `arithmetic` `NOT_GREATER_EQ`)));;

NOT_GREAT_NORM_CONV := REWR_CONV (theorem `arithmetic` `NOT_GREATER`);;

NOT_LEQ_NORM_CONV :=
 REWR_CONV
  (SUBS [SPEC "n:num" (theorem `arithmetic` `SUC_ONE_ADD`)]
    (SPECL ["m:num";"n:num"] (theorem `arithmetic` `NOT_LEQ`)));;

NOT_LESS_NORM_CONV := REWR_CONV (theorem `arithmetic` `NOT_LESS`);;

NOT_NUM_EQ_NORM_CONV :=
 REWR_CONV
  (SUBS [SPEC "m:num" (theorem `arithmetic` `SUC_ONE_ADD`);
         SPEC "n:num" (theorem `arithmetic` `SUC_ONE_ADD`)]
    (SPECL ["m:num";"n:num"] (theorem `arithmetic` `NOT_NUM_EQ`)));;

NUM_EQ_NORM_CONV := REWR_CONV (theorem `arithmetic` `EQ_LESS_EQ`);;

PLUS_ZERO_CONV := REWR_CONV PLUS_ZERO;;

SYM_ADD_ASSOC_CONV := REWR_CONV (GSYM (theorem `arithmetic` `ADD_ASSOC`));;

SYM_ONE_MULT_CONV := REWR_CONV (GEN_ALL (SYM (SPEC_ALL ONE_MULT)));;

ZERO_MULT_CONV := REWR_CONV ZERO_MULT;;

ZERO_MULT_PLUS_CONV :=
 REWR_CONV
  (SUBS [SYM (CONJUNCT1
              (SPECL ["a:num";"b:num"] (theorem `arithmetic` `MULT_CLAUSES`)))]
   (SPEC "b:num" (GEN_ALL (CONJUNCT1 (theorem `arithmetic` `ADD_CLAUSES`)))));;

ZERO_PLUS_CONV := REWR_CONV ZERO_PLUS;;

%============================================================================%
% Conversions for rewriting inequalities                                     %
%============================================================================%

LEQ_PLUS_CONV := REWR_CONV (theorem `arithmetic` `ADD_MONO_LESS_EQ`);;

%============================================================================%
% Conversions for final simplification                                       %
%============================================================================%

FORALL_SIMP_CONV := REWR_CONV FORALL_SIMP;;

%============================================================================%
% Conversions for normalising and eliminating subtraction                    %
%============================================================================%

NUM_COND_RATOR_CONV := REWR_CONV (INST_TYPE [":num",":*"] COND_RATOR);;
NUM_COND_RAND_CONV := REWR_CONV (INST_TYPE [":num",":*"] COND_RAND);;
SUB_NORM_CONV :=
 let REWRITES_CONV thl =
    let net = mk_conv_net thl
    in  \tm. FIRST_CONV (lookup_term net tm) tm
 in
 (REWRITES_CONV o (map (theorem `arithmetic`)))
  [`SUB_LEFT_ADD`;          `SUB_RIGHT_ADD`;
   `SUB_LEFT_SUB`;          `SUB_RIGHT_SUB`;
   `LEFT_SUB_DISTRIB`;      `RIGHT_SUB_DISTRIB`;
   `SUB_LEFT_SUC`;
   `SUB_LEFT_LESS_EQ`;      `SUB_RIGHT_LESS_EQ`;
   `SUB_LEFT_LESS`;         `SUB_RIGHT_LESS`;
   `SUB_LEFT_GREATER_EQ`;   `SUB_RIGHT_GREATER_EQ`;
   `SUB_LEFT_GREATER`;      `SUB_RIGHT_GREATER`;
   `SUB_LEFT_EQ`;           `SUB_RIGHT_EQ`
  ];;

%============================================================================%
% Conversions for normalising and eliminating conditionals                   %
%============================================================================%

COND_RATOR_CONV := REWR_CONV COND_RATOR;;
COND_RAND_CONV := REWR_CONV COND_RAND;;
COND_EXPAND_CONV := REWR_CONV COND_EXPAND;;
