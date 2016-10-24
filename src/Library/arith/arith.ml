% ===================================================================== %
% FILE          : arith.ml                                              %
% DESCRIPTION   : loads the library "arith" into hol.                   %
%                                                                       %
% AUTHOR        : R.J.Boulton                                           %
% DATE          : 2nd October 1992                                      %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Load the reduce library to evaluate the formula once it has been      %
% instantiated with a witness.                                          %
% --------------------------------------------------------------------- %

load_library `reduce`;;

% --------------------------------------------------------------------- %
% Add the arith help files to online help.                              %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/arith/help/entries/` in
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Begin a section for the arithmetic proof procedure code.              %
% --------------------------------------------------------------------- %

begin_section arith;;

% --------------------------------------------------------------------- %
% Load the code into ml.                                                %
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/arith/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`int_extra`;
         `arith_cons`;
         `string_extra`;
         `term_coeffs`;
         `qconv`;
         `decls`;
         `norm_bool`;
         `norm_arith`;
         `norm_ineqs`;
         `solve_ineqs`;
         `solve`;
         `rationals`;
         `sup-inf`;
         `streams`;
         `sol_ranges`;
         `exists_arith`;
         `sub_and_cond`;
         `prenex`;
         `instance`;
         `gen_arith`;
         `theorems`;
         `thm_convs`];;

% --------------------------------------------------------------------- %
% Export top-level functions from the section.                          %
% --------------------------------------------------------------------- %

(FORALL_ARITH_CONV,
 EXISTS_ARITH_CONV,
 SUB_AND_COND_ELIM_CONV,
 COND_ELIM_CONV,
 is_prenex,
 PRENEX_CONV,
 INSTANCE_T_CONV,
 non_presburger_subterms,
 is_presburger,
 ARITH_CONV,
 NEGATE_CONV,
 (\tm. QCONV ARITH_FORM_NORM_QCONV tm ? failwith `ARITH_FORM_NORM_CONV`),
 (\tm. QCONV DISJ_INEQS_FALSE_QCONV tm ? failwith `DISJ_INEQS_FALSE_CONV`)
);;

% --------------------------------------------------------------------- %
% End the section.                                                      %
% --------------------------------------------------------------------- %

end_section arith;;

% --------------------------------------------------------------------- %
% Bind the top-level functions.                                         %
% --------------------------------------------------------------------- %

let (FORALL_ARITH_CONV,EXISTS_ARITH_CONV,
     SUB_AND_COND_ELIM_CONV,COND_ELIM_CONV,is_prenex,PRENEX_CONV,
     INSTANCE_T_CONV,non_presburger_subterms,is_presburger,ARITH_CONV,
     NEGATE_CONV,ARITH_FORM_NORM_CONV,DISJ_INEQS_FALSE_CONV) = it;;
