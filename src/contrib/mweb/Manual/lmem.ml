
%- 5.2 -%
new_theory`lmem`;;
load_library`latex-hol`;;

%- 16.3 {LMEM\_DEF} -%
let LMEM_DEF = new_list_rec_definition(`LMEM_DEF`,
 "(LMEM x [] = F) /\
  (LMEM x (CONS (h:*) t) = (x = h) \/ (LMEM x t))");;

%- 28.4 {NULL\_NOT\_LMEM} -%
let NULL_NOT_LMEM = prove_thm(`NULL_NOT_LMEM`,
    "!(x:*) l. NULL l ==> ~(LMEM x l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NULL;LMEM_DEF]);;

%- 35.5 -%
latex_thm_tag := `@t `;;
latex_thm_end := `@e `;;
latex_all_theorems_to (`lmem.tag`) 
 (\s. (theorem `-` s) ? (definition `-` s))
 [`LMEM_DEF`; `NULL_NOT_LMEM`];;

%- 44.6 -%
close_theory();;

