%****************************************************************************%
% FILE          : decls.ml                                                   %
% DESCRIPTION   : Declarations to allow main code to be compiled without     %
%                 compiling theorems and thm_convs.                          %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 17th March 1991                                            %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 8th October 1992                                           %
%****************************************************************************%

letref ONE_PLUS = TRUTH;;
letref ZERO_PLUS = TRUTH;;
letref PLUS_ZERO = TRUTH;;
letref SUC_ADD1 = TRUTH;;
letref SUC_ADD2 = TRUTH;;
letref ZERO_MULT = TRUTH;;
letref ONE_MULT = TRUTH;;
letref MULT_ZERO = TRUTH;;
letref MULT_ONE = TRUTH;;
letref MULT_SUC = TRUTH;;
letref MULT_COMM = TRUTH;;
letref SUC_ADD_LESS_EQ_F = TRUTH;;
letref MULT_LEQ_SUC = TRUTH;;
letref ZERO_LESS_EQ_T = TRUTH;;
letref SUC_LESS_EQ_ZERO_F = TRUTH;;
letref ZERO_LESS_EQ_ONE_TIMES = TRUTH;;
letref LESS_EQ_PLUS = TRUTH;;
letref LESS_EQ_TRANSIT = TRUTH;;
letref NOT_T_F = TRUTH;;
letref NOT_F_T = TRUTH;;

letref CONJ_ASSOC_NORM_CONV = ALL_CONV;;
letref DISJ_ASSOC_NORM_CONV = ALL_CONV;;
letref EQ_EXPAND_CONV = ALL_CONV;;
letref IMP_EXPAND_CONV = ALL_CONV;;
letref IMP_F_EQ_F_CONV = ALL_CONV;;
letref IMP_IMP_CONJ_IMP_CONV = ALL_CONV;;
letref LEFT_DIST_NORM_CONV = ALL_CONV;;
letref NOT_CONJ_NORM_CONV = ALL_CONV;;
letref NOT_DISJ_NORM_CONV = ALL_CONV;;
letref NOT_NOT_NORM_CONV = ALL_CONV;;
letref OR_F_CONV = ALL_CONV;;
letref RIGHT_DIST_NORM_CONV = ALL_CONV;;

letref ADD_ASSOC_CONV = ALL_CONV;;
letref ADD_SYM_CONV = ALL_CONV;;
letref GATHER_BOTH_CONV = ALL_CONV;;
letref GATHER_LEFT_CONV = ALL_CONV;;
letref GATHER_NEITHER_CONV = ALL_CONV;;
letref GATHER_RIGHT_CONV = ALL_CONV;;
letref GEQ_NORM_CONV = ALL_CONV;;
letref GREAT_NORM_CONV = ALL_CONV;;
letref LEFT_ADD_DISTRIB_CONV = ALL_CONV;;
letref LESS_NORM_CONV = ALL_CONV;;
letref MULT_ASSOC_CONV = ALL_CONV;;
letref MULT_COMM_CONV = ALL_CONV;;
letref NOT_GEQ_NORM_CONV = ALL_CONV;;
letref NOT_GREAT_NORM_CONV = ALL_CONV;;
letref NOT_LEQ_NORM_CONV = ALL_CONV;;
letref NOT_LESS_NORM_CONV = ALL_CONV;;
letref NOT_NUM_EQ_NORM_CONV = ALL_CONV;;
letref NUM_EQ_NORM_CONV = ALL_CONV;;
letref PLUS_ZERO_CONV = ALL_CONV;;
letref SYM_ADD_ASSOC_CONV = ALL_CONV;;
letref SYM_ONE_MULT_CONV = ALL_CONV;;
letref ZERO_MULT_CONV = ALL_CONV;;
letref ZERO_MULT_PLUS_CONV = ALL_CONV;;
letref ZERO_PLUS_CONV = ALL_CONV;;

letref LEQ_PLUS_CONV = ALL_CONV;;

letref FORALL_SIMP_CONV = ALL_CONV;;

letref NUM_COND_RATOR_CONV = ALL_CONV;;
letref NUM_COND_RAND_CONV = ALL_CONV;;
letref SUB_NORM_CONV = ALL_CONV;;

letref COND_RATOR_CONV = ALL_CONV;;
letref COND_RAND_CONV = ALL_CONV;;
letref COND_EXPAND_CONV = ALL_CONV;;
