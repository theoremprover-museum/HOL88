%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        load_thms.ml                                          %
%                                                                             %
%     DESCRIPTION:      Definitions and theorems autoloaded into HOL          %
%                                                                             %
%     AUTHOR:           T. F. Melham (88.04.04)                               %
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
%     REVISION HISTORY: MJCG 5/2/89 loading replaced by autoloading           %
%=============================================================================%

% --------------------------------------------------------------------- %
% THEORY: one                                                           %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `one`, `one_axiom`;
  `theorem`, `one`, `one`;
  `theorem`, `one`, `one_Axiom`];;

% --------------------------------------------------------------------- %
% THEORY: combin                                                        %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`definition`, `combin`, `o_DEF`;
  `definition`, `combin`, `K_DEF`;
  `definition`, `combin`, `S_DEF`;
  `definition`, `combin`, `I_DEF`;

  `theorem`, `combin`, `o_THM`;
  `theorem`, `combin`, `o_ASSOC`;
  `theorem`, `combin`, `K_THM`;
  `theorem`, `combin`, `S_THM`;
  `theorem`, `combin`, `I_THM`;
  `theorem`, `combin`, `I_o_ID`];;

% --------------------------------------------------------------------- %
% THEORY: sum                                                           %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `sum`, `sum_Axiom`;
  `theorem`, `sum`, `sum_axiom`;
  `definition`, `sum`, `ISL`;
  `definition`, `sum`, `ISR`;
  `definition`, `sum`, `OUTL`;
  `definition`, `sum`, `OUTR`;
  `theorem`, `sum`, `ISL_OR_ISR`;
  `theorem`, `sum`, `INL`;
  `theorem`, `sum`, `INR`];;

% --------------------------------------------------------------------- %
% THEORY: fun                                                           %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`definition`, `fun`, `ASSOC_DEF`;
  `definition`, `fun`, `COMM_DEF`;
  `definition`, `fun`, `FCOMM_DEF`;
  `definition`, `fun`, `RIGHT_ID_DEF`;
  `definition`, `fun`, `LEFT_ID_DEF`;
  `definition`, `fun`, `MONOID_DEF`;

  `theorem`, `fun`, `ASSOC_CONJ`;
  `theorem`, `fun`, `ASSOC_DISJ`;
  `theorem`, `fun`, `FCOMM_ASSOC`;
  `theorem`, `fun`, `MONOID_CONJ_T`;
  `theorem`, `fun`, `MONOID_DISJ_F`];;
% --------------------------------------------------------------------- %
% THEORY: num                                                           %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `num`, `NOT_SUC`;
  `theorem`, `num`, `INV_SUC`;
  `theorem`, `num`, `INDUCTION`];;

% --------------------------------------------------------------------- %
% THEORY: prim_rec                                                      %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `prim_rec`, `INV_SUC_EQ`;
  `theorem`, `prim_rec`, `LESS_REFL`;
  `theorem`, `prim_rec`, `SUC_LESS`;
  `theorem`, `prim_rec`, `NOT_LESS_0`;
  `theorem`, `prim_rec`, `LESS_MONO`;
  `theorem`, `prim_rec`, `LESS_SUC_REFL`;
  `theorem`, `prim_rec`, `LESS_SUC`;
  `theorem`, `prim_rec`, `LESS_THM`;
  `theorem`, `prim_rec`, `LESS_SUC_IMP`;
  `theorem`, `prim_rec`, `LESS_0`;
  `theorem`, `prim_rec`, `EQ_LESS`;
  `theorem`, `prim_rec`, `SUC_ID`;
  `theorem`, `prim_rec`, `NOT_LESS_EQ`;
  `theorem`, `prim_rec`, `LESS_NOT_EQ`;
  `theorem`, `prim_rec`, `LESS_SUC_SUC`;
  `theorem`, `prim_rec`, `PRE`;
  `theorem`, `prim_rec`, `num_Axiom`];;

% --------------------------------------------------------------------- %
% THEORY: arithmetic                                                    %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`definition`, `arithmetic`, `GREATER`;
  `definition`, `arithmetic`, `LESS_OR_EQ`;
  `definition`, `arithmetic`, `GREATER_OR_EQ`;
  `definition`, `arithmetic`, `DIVISION`;
  `definition`, `arithmetic`, `ADD`;
  `definition`, `arithmetic`, `MULT`;
  `definition`, `arithmetic`, `SUB`;
  `definition`, `arithmetic`, `EXP`;
  `definition`, `arithmetic`, `FACT`;
  `definition`, `arithmetic`, `EVEN`;
  `definition`, `arithmetic`, `ODD`;

  `theorem`, `arithmetic`, `ADD_SUC`;
  `theorem`, `arithmetic`, `ADD_CLAUSES`;
  `theorem`, `arithmetic`, `ADD_SYM`;
  `theorem`, `arithmetic`, `ADD_SUC`;
  `theorem`, `arithmetic`, `num_CASES`;
  `theorem`, `arithmetic`, `LESS_MONO_EQ`;
  `theorem`, `arithmetic`, `SUC_SUB1`;
  `theorem`, `arithmetic`, `PRE_SUB1`;
  `theorem`, `arithmetic`, `LESS_ADD`;
  `theorem`, `arithmetic`, `SUB_0`;
  `theorem`, `arithmetic`, `LESS_TRANS`;
  `theorem`, `arithmetic`, `ADD1`;
  `theorem`, `arithmetic`, `ADD_0`;
  `theorem`, `arithmetic`, `LESS_ANTISYM`;
  `theorem`, `arithmetic`, `LESS_LESS_SUC`;

  `theorem`, `arithmetic`, `FUN_EQ_LEMMA`;
  `theorem`, `arithmetic`, `LESS_SUC_EQ_COR`;
  `theorem`, `arithmetic`, `LESS_OR`;
  `theorem`, `arithmetic`, `OR_LESS`;
  `theorem`, `arithmetic`, `LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_NOT_SUC`;
  `theorem`, `arithmetic`, `LESS_0_CASES`;
  `theorem`, `arithmetic`, `LESS_CASES_IMP`;
  `theorem`, `arithmetic`, `LESS_CASES`;
  `theorem`, `arithmetic`, `ADD_INV_0`;
  `theorem`, `arithmetic`, `LESS_EQ_ADD`;
  `theorem`, `arithmetic`, `LESS_EQ_SUC_REFL`;
  `theorem`, `arithmetic`, `LESS_ADD_NONZERO`;

  `theorem`, `arithmetic`, `LESS_EQ_ANTISYM`;
  `theorem`, `arithmetic`, `NOT_LESS`;
  `theorem`, `arithmetic`, `SUB_EQ_0`;
  `theorem`, `arithmetic`, `ADD_ASSOC`;
  `theorem`, `arithmetic`, `MULT_0`;
  `theorem`, `arithmetic`, `MULT_CLAUSES`;
  `theorem`, `arithmetic`, `MULT_SYM`;
  `theorem`, `arithmetic`, `RIGHT_ADD_DISTRIB`;
  `theorem`, `arithmetic`, `LEFT_ADD_DISTRIB`;
  `theorem`, `arithmetic`, `MULT_ASSOC`;
  `theorem`, `arithmetic`, `SUB_ADD`;
  `theorem`, `arithmetic`, `PRE_SUB`;
  `theorem`, `arithmetic`, `ADD_EQ_0`;
  `theorem`, `arithmetic`, `ADD_INV_0_EQ`;

  `theorem`, `arithmetic`, `PRE_SUC_EQ`;
  `theorem`, `arithmetic`, `INV_PRE_EQ`;
  `theorem`, `arithmetic`, `LESS_SUC_NOT`;
  `theorem`, `arithmetic`, `ADD_EQ_SUB`;
  `theorem`, `arithmetic`, `LESS_MONO_ADD`;
  `theorem`, `arithmetic`, `LESS_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `EQ_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_TRANS`;
  `theorem`, `arithmetic`, `LESS_EQ_LESS_EQ_MONO`;
  `theorem`, `arithmetic`, `LESS_EQ_REFL`;
  `theorem`, `arithmetic`, `LESS_IMP_LESS_OR_EQ`;
  `theorem`, `arithmetic`, `LESS_MONO_MULT`;
  `theorem`, `arithmetic`, `RIGHT_SUB_DISTRIB`;
  `theorem`, `arithmetic`, `LEFT_SUB_DISTRIB`;
  `theorem`, `arithmetic`, `LESS_ADD_1`;

  `theorem`, `arithmetic`, `ZERO_LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_MONO`;
  `theorem`, `arithmetic`, `LESS_OR_EQ_ADD`;
  `theorem`, `arithmetic`, `SUC_NOT`;

  `theorem`, `arithmetic`, `EXP_ADD`;
  `theorem`, `arithmetic`, `NOT_ODD_EQ_EVEN`;
  `theorem`, `arithmetic`, `MULT_SUC_EQ`;
  `theorem`, `arithmetic`, `MULT_EXP_MONO`;
  `theorem`, `arithmetic`, `WOP`;

  `theorem`, `arithmetic`, `DA`;
  `theorem`, `arithmetic`, `MOD_ONE`;
  `theorem`, `arithmetic`, `DIV_LESS_EQ`;
  `theorem`, `arithmetic`, `DIV_UNIQUE`;
  `theorem`, `arithmetic`, `MOD_UNIQUE`;
  `theorem`, `arithmetic`, `DIV_MULT`;
  `theorem`, `arithmetic`, `LESS_MOD`;
  `theorem`, `arithmetic`, `MOD_EQ_0`;
  `theorem`, `arithmetic`, `ZERO_MOD`;
  `theorem`, `arithmetic`, `MOD_MULT`;
  `theorem`, `arithmetic`, `MOD_TIMES`;
  `theorem`, `arithmetic`, `MOD_PLUS`;
  `theorem`, `arithmetic`, `MOD_MOD`;

  `theorem`, `arithmetic`, `SUB_MONO_EQ`;
  `theorem`, `arithmetic`, `SUB_PLUS`;
  `theorem`, `arithmetic`, `INV_PRE_LESS`;
  `theorem`, `arithmetic`, `INV_PRE_LESS_EQ`;
  `theorem`, `arithmetic`, `SUB_LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_EQUAL_ANTISYM`;
  `theorem`, `arithmetic`, `SUB_EQ_EQ_0`;
  `theorem`, `arithmetic`, `SUB_LESS_0`;
  `theorem`, `arithmetic`, `SUB_LESS_OR`;
  `theorem`, `arithmetic`, `LESS_ADD_SUC`;
  `theorem`, `arithmetic`, `LESS_SUB_ADD_LESS`;
  `theorem`, `arithmetic`, `TIMES2`;
  `theorem`, `arithmetic`, `LESS_MULT_MONO`;
  `theorem`, `arithmetic`, `MULT_MONO_EQ`;
  `theorem`, `arithmetic`, `ADD_SUB`;
  `theorem`, `arithmetic`, `LESS_EQ_ADD_SUB`;
  `theorem`, `arithmetic`, `SUB_EQUAL_0`;
  `theorem`, `arithmetic`, `LESS_EQ_SUB_LESS`;
  `theorem`, `arithmetic`, `NOT_SUC_LESS_EQ`;
  `theorem`, `arithmetic`, `SUB_SUB`;
  `theorem`, `arithmetic`, `LESS_IMP_LESS_ADD`;
  `theorem`, `arithmetic`, `LESS_EQ_IMP_LESS_SUC`;
  `theorem`, `arithmetic`, `SUB_LESS_EQ_ADD`;
  `theorem`, `arithmetic`, `SUB_CANCEL`;
  `theorem`, `arithmetic`, `CANCEL_SUB`;
  `theorem`, `arithmetic`, `NOT_EXP_0`;
  `theorem`, `arithmetic`, `ZERO_LESS_EXP`;
  `theorem`, `arithmetic`, `ODD_OR_EVEN`;
  `theorem`, `arithmetic`, `LESS_EXP_SUC_MONO`;
  `theorem`, `arithmetic`, `ZERO_DIV`;
  `theorem`, `arithmetic`, `LESS_LESS_CASES`;
  `theorem`, `arithmetic`, `GREATER_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_CASES`;
  `theorem`, `arithmetic`, `LESS_EQUAL_ADD`;
  `theorem`, `arithmetic`, `LESS_EQ_EXISTS`;
  `theorem`, `arithmetic`, `NOT_LESS_EQUAL`;
  `theorem`, `arithmetic`, `LESS_EQ_0`;
  `theorem`, `arithmetic`, `MULT_EQ_0`;
  `theorem`, `arithmetic`, `LESS_MULT2`;
  `theorem`, `arithmetic`, `LESS_EQ_LESS_TRANS`;
  `theorem`, `arithmetic`, `LESS_LESS_EQ_TRANS`;
  `theorem`, `arithmetic`, `FACT_LESS`;
  `theorem`, `arithmetic`, `EVEN_ODD`;
  `theorem`, `arithmetic`, `ODD_EVEN`;
  `theorem`, `arithmetic`, `EVEN_OR_ODD`;
  `theorem`, `arithmetic`, `EVEN_AND_ODD`;
  `theorem`, `arithmetic`, `EVEN_ADD`;
  `theorem`, `arithmetic`, `EVEN_MULT`;
  `theorem`, `arithmetic`, `ODD_ADD`;
  `theorem`, `arithmetic`, `ODD_MULT`;
  `theorem`, `arithmetic`, `EVEN_DOUBLE`;
  `theorem`, `arithmetic`, `ODD_DOUBLE`;
  `theorem`, `arithmetic`, `EVEN_ODD_EXISTS`;
  `theorem`, `arithmetic`, `EVEN_EXISTS`;
  `theorem`, `arithmetic`, `ODD_EXISTS`;

  `theorem`, `arithmetic`, `EQ_LESS_EQ`;
  `theorem`, `arithmetic`, `ADD_MONO_LESS_EQ`;
  `theorem`, `arithmetic`, `NOT_SUC_LESS_EQ_0`;

  `theorem`, `arithmetic`, `NOT_LEQ`;
  `theorem`, `arithmetic`, `NOT_NUM_EQ`;
  `theorem`, `arithmetic`, `NOT_GREATER`;
  `theorem`, `arithmetic`, `NOT_GREATER_EQ`;
  `theorem`, `arithmetic`, `SUC_ONE_ADD`;
  `theorem`, `arithmetic`, `SUC_ADD_SYM`;
  `theorem`, `arithmetic`, `NOT_SUC_ADD_LESS_EQ`;
  `theorem`, `arithmetic`, `MULT_LESS_EQ_SUC`;

  `theorem`, `arithmetic`, `SUB_LEFT_ADD`;
  `theorem`, `arithmetic`, `SUB_RIGHT_ADD`;
  `theorem`, `arithmetic`, `SUB_LEFT_SUB`;
  `theorem`, `arithmetic`, `SUB_RIGHT_SUB`;
  `theorem`, `arithmetic`, `SUB_LEFT_SUC`;
  `theorem`, `arithmetic`, `SUB_LEFT_LESS_EQ`;
  `theorem`, `arithmetic`, `SUB_RIGHT_LESS_EQ`;
  `theorem`, `arithmetic`, `SUB_LEFT_LESS`;
  `theorem`, `arithmetic`, `SUB_RIGHT_LESS`;
  `theorem`, `arithmetic`, `SUB_LEFT_GREATER_EQ`;
  `theorem`, `arithmetic`, `SUB_RIGHT_GREATER_EQ`;
  `theorem`, `arithmetic`, `SUB_LEFT_GREATER`;
  `theorem`, `arithmetic`, `SUB_RIGHT_GREATER`;
  `theorem`, `arithmetic`, `SUB_LEFT_EQ`;
  `theorem`, `arithmetic`, `SUB_RIGHT_EQ`];;

% --------------------------------------------------------------------- %
% THEORY: list                                                          %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `list`, `list_Axiom`;
                                % in mk_list_defs.ml %
  `definition`, `list`, `NULL_DEF`;
  `definition`, `list`, `HD`;
  `definition`, `list`, `TL`;
  `definition`, `list`, `SUM`;
  `definition`, `list`, `APPEND`;
  `definition`, `list`, `FLAT`;
  `definition`, `list`, `LENGTH`;
  `definition`, `list`, `MAP`;
  `definition`, `list`, `MAP2`;
  `definition`, `list`, `EL`;

  `definition`, `list`, `SNOC`;
  `definition`, `list`, `FOLDR`;
  `definition`, `list`, `FOLDL`;
  `definition`, `list`, `FILTER`;
  `definition`, `list`, `SCANL`;
  `definition`, `list`, `SCANR`;
  `definition`, `list`, `SEG`;
  `definition`, `list`, `REVERSE`;
  `definition`, `list`, `ALL_EL`;
  `definition`, `list`, `SOME_EL`;
  `definition`, `list`, `IS_EL_DEF`;
  `definition`, `list`, `AND_EL_DEF`;
  `definition`, `list`, `OR_EL_DEF`;
  `definition`, `list`, `FIRSTN`;
  `definition`, `list`, `BUTFIRSTN`;
  `definition`, `list`, `LASTN`;
  `definition`, `list`, `BUTLASTN`;
  `definition`, `list`, `LAST_DEF`;
  `definition`, `list`, `BUTLAST_DEF`;
  `definition`, `list`, `ELL`;
  `definition`, `list`, `IS_PREFIX`;
  `definition`, `list`, `IS_SUFFIX`;
  `definition`, `list`, `IS_SUBLIST`;
  `definition`, `list`, `PREFIX_DEF`;
  `definition`, `list`, `SUFFIX_DEF`;
  `definition`, `list`, `SPLITP`;
  `definition`, `list`, `ZIP`;
  `definition`, `list`, `UNZIP`;
  `definition`, `list`, `UNZIP_FST_DEF`;
  `definition`, `list`, `UNZIP_SND_DEF`;
  `definition`, `list`, `GENLIST`;
  `definition`, `list`, `REPLICATE`;
                                % in mk_list_thms.ml %
  `theorem`, `list`, `NULL`;
  `theorem`, `list`, `list_INDUCT`;
  `theorem`, `list`, `list_CASES`;
  `theorem`, `list`, `CONS_11`;
  `theorem`, `list`, `NOT_NIL_CONS`;
  `theorem`, `list`, `NOT_CONS_NIL`;
  `theorem`, `list`, `LIST_NOT_EQ`;
  `theorem`, `list`, `NOT_EQ_LIST`;
  `theorem`, `list`, `EQ_LIST`;
  `theorem`, `list`, `CONS`;

  `theorem`, `list`, `APPEND_ASSOC`;
  `theorem`, `list`, `LENGTH_APPEND`;
  `theorem`, `list`, `MAP_APPEND`;
  `theorem`, `list`, `LENGTH_MAP`;
  `theorem`, `list`, `LENGTH_NIL`;
  `theorem`, `list`, `LENGTH_CONS`;
  `theorem`, `list`, `LENGTH_MAP2`;
                                % in mk_list_thm2.ml %
        `theorem`, `list`, `ALL_EL_APPEND`;
        `theorem`, `list`, `ALL_EL_BUTFIRSTN`;
        `theorem`, `list`, `ALL_EL_BUTLASTN`;
        `theorem`, `list`, `ALL_EL_CONJ`;
        `theorem`, `list`, `ALL_EL_FIRSTN`;
        `theorem`, `list`, `ALL_EL_FOLDL_MAP`;
        `theorem`, `list`, `ALL_EL_FOLDL`;
        `theorem`, `list`, `ALL_EL_FOLDR_MAP`;
        `theorem`, `list`, `ALL_EL_FOLDR`;
        `theorem`, `list`, `ALL_EL_LASTN`;
        `theorem`, `list`, `ALL_EL_MAP`;
        `theorem`, `list`, `ALL_EL_REPLICATE`;
        `theorem`, `list`, `ALL_EL_REVERSE`;
        `theorem`, `list`, `ALL_EL_SEG`;
        `theorem`, `list`, `ALL_EL_SNOC`;
        `theorem`, `list`, `APPEND_BUTLASTN_BUTFIRSTN`;
        `theorem`, `list`, `APPEND_BUTLASTN_LASTN`;
        `theorem`, `list`, `APPEND_BUTLAST_LAST`;
        `theorem`, `list`, `APPEND_FIRSTN_BUTFIRSTN`;
        `theorem`, `list`, `APPEND_FIRSTN_LASTN`;
        `theorem`, `list`, `APPEND_FOLDL`;
        `theorem`, `list`, `APPEND_FOLDR`;
        `theorem`, `list`, `APPEND_LENGTH_EQ`;
        `theorem`, `list`, `APPEND_NIL`;
        `theorem`, `list`, `APPEND_SNOC`;
        `theorem`, `list`, `ASSOC_APPEND`;
        `theorem`, `list`, `ASSOC_FOLDL_FLAT`;
        `theorem`, `list`, `ASSOC_FOLDR_FLAT`;
        `theorem`, `list`, `BUTFIRSTN_APPEND1`;
        `theorem`, `list`, `BUTFIRSTN_APPEND2`;
        `theorem`, `list`, `BUTFIRSTN_BUTFIRSTN`;
        `theorem`, `list`, `BUTFIRSTN_LASTN`;
        `theorem`, `list`, `BUTFIRSTN_LENGTH_APPEND`;
        `theorem`, `list`, `BUTFIRSTN_LENGTH_NIL`;
        `theorem`, `list`, `BUTFIRSTN_REVERSE`;
        `theorem`, `list`, `BUTFIRSTN_SEG`;
        `theorem`, `list`, `BUTFIRSTN_SNOC`;
        `theorem`, `list`, `BUTLASTN_APPEND1`;
        `theorem`, `list`, `BUTLASTN_APPEND2`;
        `theorem`, `list`, `BUTLASTN_BUTLAST`;
        `theorem`, `list`, `BUTLASTN_BUTLASTN`;
        `theorem`, `list`, `BUTLASTN_CONS`;
        `theorem`, `list`, `BUTLASTN_FIRSTN`;
        `theorem`, `list`, `BUTLASTN_LASTN_NIL`;
        `theorem`, `list`, `BUTLASTN_LASTN`;
        `theorem`, `list`, `BUTLASTN_LENGTH_APPEND`;
        `theorem`, `list`, `BUTLASTN_LENGTH_CONS`;
        `theorem`, `list`, `BUTLASTN_LENGTH_NIL`;
        `theorem`, `list`, `BUTLASTN_MAP`;
        `theorem`, `list`, `BUTLASTN_REVERSE`;
        `theorem`, `list`, `BUTLASTN_SEG`;
        `theorem`, `list`, `BUTLASTN_SUC_BUTLAST`;
        `theorem`, `list`, `BUTLASTN_1`;
        `theorem`, `list`, `BUTLAST`;
        `theorem`, `list`, `COMM_ASSOC_FOLDL_REVERSE`;
        `theorem`, `list`, `COMM_ASSOC_FOLDR_REVERSE`;
        `theorem`, `list`, `COMM_MONOID_FOLDL`;
        `theorem`, `list`, `COMM_MONOID_FOLDR`;
        `theorem`, `list`, `CONS_APPEND`;
        `theorem`, `list`, `ELL_0_SNOC`;
        `theorem`, `list`, `ELL_APPEND1`;
        `theorem`, `list`, `ELL_APPEND2`;
        `theorem`, `list`, `ELL_CONS`;
        `theorem`, `list`, `ELL_EL`;
        `theorem`, `list`, `ELL_IS_EL`;
        `theorem`, `list`, `ELL_LAST`;
        `theorem`, `list`, `ELL_LENGTH_APPEND`;
        `theorem`, `list`, `ELL_LENGTH_CONS`;
        `theorem`, `list`, `ELL_LENGTH_SNOC`;
        `theorem`, `list`, `ELL_MAP`;
        `theorem`, `list`, `ELL_PRE_LENGTH`;
        `theorem`, `list`, `ELL_REVERSE_EL`;
        `theorem`, `list`, `ELL_REVERSE`;
        `theorem`, `list`, `ELL_SEG`;
        `theorem`, `list`, `ELL_SNOC`;
        `theorem`, `list`, `ELL_SUC_SNOC`;
        `theorem`, `list`, `EL_APPEND1`;
        `theorem`, `list`, `EL_APPEND2`;
        `theorem`, `list`, `EL_CONS`;
        `theorem`, `list`, `EL_ELL`;
        `theorem`, `list`, `EL_IS_EL`;
        `theorem`, `list`, `EL_LENGTH_APPEND`;
        `theorem`, `list`, `EL_LENGTH_SNOC`;
        `theorem`, `list`, `EL_MAP`;
        `theorem`, `list`, `EL_PRE_LENGTH`;
        `theorem`, `list`, `EL_REVERSE_ELL`;
        `theorem`, `list`, `EL_REVERSE`;
        `theorem`, `list`, `EL_SEG`;
        `theorem`, `list`, `EL_SNOC`;
        `theorem`, `list`, `FCOMM_FOLDL_APPEND`;
        `theorem`, `list`, `FCOMM_FOLDL_FLAT`;
        `theorem`, `list`, `FCOMM_FOLDR_APPEND`;
        `theorem`, `list`, `FCOMM_FOLDR_FLAT`;
        `theorem`, `list`, `FILTER_APPEND`;
        `theorem`, `list`, `FILTER_COMM`;
        `theorem`, `list`, `FILTER_FILTER`;
        `theorem`, `list`, `FILTER_FLAT`;
        `theorem`, `list`, `FILTER_FOLDL`;
        `theorem`, `list`, `FILTER_FOLDR`;
        `theorem`, `list`, `FILTER_IDEM`;
        `theorem`, `list`, `FILTER_MAP`;
        `theorem`, `list`, `FILTER_REVERSE`;
        `theorem`, `list`, `FILTER_SNOC`;
        `theorem`, `list`, `FIRSTN_APPEND1`;
        `theorem`, `list`, `FIRSTN_APPEND2`;
        `theorem`, `list`, `FIRSTN_BUTLASTN`;
        `theorem`, `list`, `FIRSTN_FIRSTN`;
        `theorem`, `list`, `FIRSTN_LENGTH_APPEND`;
        `theorem`, `list`, `FIRSTN_LENGTH_ID`;
        `theorem`, `list`, `FIRSTN_REVERSE`;
        `theorem`, `list`, `FIRSTN_SEG`;
        `theorem`, `list`, `FIRSTN_SNOC`;
        `theorem`, `list`, `FLAT_APPEND`;
        `theorem`, `list`, `FLAT_FLAT`;
        `theorem`, `list`, `FLAT_FOLDL`;
        `theorem`, `list`, `FLAT_FOLDR`;
        `theorem`, `list`, `FLAT_REVERSE`;
        `theorem`, `list`, `FLAT_SNOC`;
        `theorem`, `list`, `FOLDL_APPEND`;
        `theorem`, `list`, `FOLDL_FILTER`;
        `theorem`, `list`, `FOLDL_FOLDR_REVERSE`;
        `theorem`, `list`, `FOLDL_MAP`;
        `theorem`, `list`, `FOLDL_REVERSE`;
        `theorem`, `list`, `FOLDL_SINGLE`;
        `theorem`, `list`, `FOLDL_SNOC_NIL`;
        `theorem`, `list`, `FOLDL_SNOC`;
        `theorem`, `list`, `FOLDR_APPEND`;
        `theorem`, `list`, `FOLDR_CONS_NIL`;
        `theorem`, `list`, `FOLDR_FILTER_REVERSE`;
        `theorem`, `list`, `FOLDR_FILTER`;
        `theorem`, `list`, `FOLDR_FOLDL_REVERSE`;
        `theorem`, `list`, `FOLDR_FOLDL`;
        `theorem`, `list`, `FOLDR_MAP_REVERSE`;
        `theorem`, `list`, `FOLDR_MAP`;
        `theorem`, `list`, `FOLDR_REVERSE`;
        `theorem`, `list`, `FOLDR_SINGLE`;
        `theorem`, `list`, `FOLDR_SNOC`;
        `theorem`, `list`, `IS_EL_APPEND`;
        `theorem`, `list`, `IS_EL_BUTFIRSTN`;
        `theorem`, `list`, `IS_EL_BUTLASTN`;
        `theorem`, `list`, `IS_EL_FILTER`;
        `theorem`, `list`, `IS_EL_FIRSTN`;
        `theorem`, `list`, `IS_EL_FOLDL_MAP`;
        `theorem`, `list`, `IS_EL_FOLDL`;
        `theorem`, `list`, `IS_EL_FOLDR_MAP`;
        `theorem`, `list`, `IS_EL_FOLDR`;
        `theorem`, `list`, `IS_EL_LASTN`;
        `theorem`, `list`, `IS_EL_REPLICATE`;
        `theorem`, `list`, `IS_EL_REVERSE`;
        `theorem`, `list`, `IS_EL_SEG`;
        `theorem`, `list`, `IS_EL_SNOC`;
        `theorem`, `list`, `IS_EL_SOME_EL`;
        `theorem`, `list`, `IS_EL`;
        `theorem`, `list`, `IS_PREFIX_APPEND`;
        `theorem`, `list`, `IS_PREFIX_IS_SUBLIST`;
        `theorem`, `list`, `IS_PREFIX_PREFIX`;
        `theorem`, `list`, `IS_PREFIX_REVERSE`;
        `theorem`, `list`, `IS_SUBLIST_APPEND`;
        `theorem`, `list`, `IS_SUBLIST_REVERSE`;
        `theorem`, `list`, `IS_SUFFIX_APPEND`;
        `theorem`, `list`, `IS_SUFFIX_IS_SUBLIST`;
        `theorem`, `list`, `IS_SUFFIX_REVERSE`;
        `theorem`, `list`, `LASTN_APPEND1`;
        `theorem`, `list`, `LASTN_APPEND2`;
        `theorem`, `list`, `LASTN_BUTFIRSTN`;
        `theorem`, `list`, `LASTN_BUTLASTN`;
        `theorem`, `list`, `LASTN_CONS`;
        `theorem`, `list`, `LASTN_LASTN`;
        `theorem`, `list`, `LASTN_LENGTH_APPEND`;
        `theorem`, `list`, `LASTN_LENGTH_ID`;
        `theorem`, `list`, `LASTN_MAP`;
        `theorem`, `list`, `LASTN_REVERSE`;
        `theorem`, `list`, `LASTN_SEG`;
        `theorem`, `list`, `LASTN_1`;
        `theorem`, `list`, `LAST`;
        `theorem`, `list`, `LAST_LASTN_LAST`;
        `theorem`, `list`, `LENGTH_BUTFIRSTN`;
        `theorem`, `list`, `LENGTH_BUTLASTN`;
        `theorem`, `list`, `LENGTH_BUTLAST`;
        `theorem`, `list`, `LENGTH_EQ`;
        `theorem`, `list`, `LENGTH_FIRSTN`;
        `theorem`, `list`, `LENGTH_FLAT`;
        `theorem`, `list`, `LENGTH_FOLDL`;
        `theorem`, `list`, `LENGTH_FOLDR`;
        `theorem`, `list`, `LENGTH_GENLIST`;
        `theorem`, `list`, `LENGTH_LASTN`;
        `theorem`, `list`, `LENGTH_NOT_NULL`;
        `theorem`, `list`, `LENGTH_REPLICATE`;
        `theorem`, `list`, `LENGTH_REVERSE`;
        `theorem`, `list`, `LENGTH_SCANL`;
        `theorem`, `list`, `LENGTH_SCANR`;
        `theorem`, `list`, `LENGTH_SEG`;
        `theorem`, `list`, `LENGTH_SNOC`;
        `theorem`, `list`, `LENGTH_UNZIP_FST`;
        `theorem`, `list`, `LENGTH_UNZIP_SND`;
        `theorem`, `list`, `LENGTH_ZIP`;
        `theorem`, `list`, `MAP_FILTER`;
        `theorem`, `list`, `MAP_FLAT`;
        `theorem`, `list`, `MAP_FOLDL`;
        `theorem`, `list`, `MAP_FOLDR`;
        `theorem`, `list`, `MAP_MAP_o`;
        `theorem`, `list`, `MAP_REVERSE`;
        `theorem`, `list`, `MAP_SNOC`;
        `theorem`, `list`, `MAP_o`;
        `theorem`, `list`, `MONOID_APPEND_NIL`;
        `theorem`, `list`, `NOT_ALL_EL_SOME_EL`;
        `theorem`, `list`, `NOT_NIL_SNOC`;
        `theorem`, `list`, `NOT_SNOC_NIL`;
        `theorem`, `list`, `NOT_SOME_EL_ALL_EL`;
        `theorem`, `list`, `NULL_EQ_NIL`;
        `theorem`, `list`, `NULL_FOLDL`;
        `theorem`, `list`, `NULL_FOLDR`;
        `theorem`, `list`, `PREFIX_FOLDR`;
        `theorem`, `list`, `PREFIX`;
        `theorem`, `list`, `REVERSE_APPEND`;
        `theorem`, `list`, `REVERSE_EQ_NIL`;
        `theorem`, `list`, `REVERSE_FLAT`;
        `theorem`, `list`, `REVERSE_FOLDL`;
        `theorem`, `list`, `REVERSE_FOLDR`;
        `theorem`, `list`, `REVERSE_REVERSE`;
        `theorem`, `list`, `REVERSE_SNOC`;
        `theorem`, `list`, `RIGHT_ID_APPEND_NIL`;
        `theorem`, `list`, `SEG_0_SNOC`;
        `theorem`, `list`, `SEG_APPEND1`;
        `theorem`, `list`, `SEG_APPEND2`;
        `theorem`, `list`, `SEG_APPEND`;
        `theorem`, `list`, `SEG_FIRSTN_BUTFISTN`;
        `theorem`, `list`, `SEG_LASTN_BUTLASTN`;
        `theorem`, `list`, `SEG_LENGTH_ID`;
        `theorem`, `list`, `SEG_LENGTH_SNOC`;
        `theorem`, `list`, `SEG_REVERSE`;
        `theorem`, `list`, `SEG_SEG`;
        `theorem`, `list`, `SEG_SNOC`;
        `theorem`, `list`, `SEG_SUC_CONS`;
        `theorem`, `list`, `SNOC_11`;
        `theorem`, `list`, `SNOC_APPEND`;
        `theorem`, `list`, `SNOC_Axiom`;
        `theorem`, `list`, `SNOC_CASES`;
        `theorem`, `list`, `SNOC_EQ_LENGTH_EQ`;
        `theorem`, `list`, `SNOC_FOLDR`;
        `theorem`, `list`, `SNOC_INDUCT`;
        `theorem`, `list`, `SNOC_REVERSE_CONS`;
        `theorem`, `list`, `SOME_EL_APPEND`;
        `theorem`, `list`, `SOME_EL_BUTFIRSTN`;
        `theorem`, `list`, `SOME_EL_BUTLASTN`;
        `theorem`, `list`, `SOME_EL_DISJ`;
        `theorem`, `list`, `SOME_EL_FIRSTN`;
        `theorem`, `list`, `SOME_EL_FOLDL_MAP`;
        `theorem`, `list`, `SOME_EL_FOLDL`;
        `theorem`, `list`, `SOME_EL_FOLDR_MAP`;
        `theorem`, `list`, `SOME_EL_FOLDR`;
        `theorem`, `list`, `SOME_EL_LASTN`;
        `theorem`, `list`, `SOME_EL_MAP`;
        `theorem`, `list`, `SOME_EL_REVERSE`;
        `theorem`, `list`, `SOME_EL_SEG`;
        `theorem`, `list`, `SOME_EL_SNOC`;
        `theorem`, `list`, `SUM_APPEND`;
        `theorem`, `list`, `SUM_FLAT`;
        `theorem`, `list`, `SUM_FOLDL`;
        `theorem`, `list`, `SUM_FOLDR`;
        `theorem`, `list`, `SUM_REVERSE`;
        `theorem`, `list`, `SUM_SNOC`;
        `theorem`, `list`, `TL_SNOC`;
        `theorem`, `list`, `UNZIP_SNOC`;
        `theorem`, `list`, `UNZIP_ZIP`;
        `theorem`, `list`, `ZIP_SNOC`;
        `theorem`, `list`, `ZIP_UNZIP`;
 ];;

% --------------------------------------------------------------------- %
% THEORY: tree                                                          %
% --------------------------------------------------------------------- %
% === do not load
let node_11             = theorem `tree` `node_11` and
    tree_Induct         = theorem `tree` `tree_Induct` and
    tree_Axiom          = theorem `tree` `tree_Axiom`;;
%
% --------------------------------------------------------------------- %
% THEORY: ltree                                                         %
% --------------------------------------------------------------------- %
% === do not load
let Node_11             = theorem `ltree` `Node_11` and
    Node_onto           = theorem `ltree` `Node_onto` and
    ltree_Induct        = theorem `ltree` `ltree_Induct` and
    ltree_Axiom         = theorem `ltree` `ltree_Axiom`;;
%
% --------------------------------------------------------------------- %
% THEORY: tydefs                                                        %
% --------------------------------------------------------------------- %

map
 autoload_theory
 [`theorem`, `tydefs`, `TY_DEF_THM`;
  `theorem`, `tydefs`, `exists_TRP`];;
