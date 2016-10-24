
@D "mac_before_tag" = "\\begin{equation}\n"
@D "mac_after_tag" = "\\end{equation}\n"
@D "mac_begin_env" = "\\begin{comment}"
@D "mac_changed" = " \n"
@D "mac_end_env" = "\\end{comment}\n"
@D "ml_only" = "true"

@*{The theory {\tt lmem}}
This theory contains definition of the constant \CONST{LMEM} and a theorem.
@-
@M
@N
new_theory`lmem`;;
load_library`latex-hol`;;
@-

@ {Definition of \protect\CONST{LMEM}}
The constant \CONST{LMEM} is a predicate asserting the membership of an
element in a list.
@t{LMEM_DEF}
@N
let LMEM_DEF = new_list_rec_definition(`LMEM_DEF`,
 "(LMEM x [] = F) /\
  (LMEM x (CONS (h:*) t) = (x = h) \/ (LMEM x t))");;
@-

@ {A theorem}
The theorem \mlname{NULL_NOT_LMEM} states that nothing is an element
of an empty list. 
@t{NULL_NOT_LMEM}
@N
let NULL_NOT_LMEM = prove_thm(`NULL_NOT_LMEM`,
    "!(x:*) l. NULL l ==> ~(LMEM x l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NULL;LMEM_DEF]);;
@-

@M
@N
latex_thm_tag := `@t `;;
latex_thm_end := `@e `;;
latex_all_theorems_to (`lmem.tag`) 
 (\s. (theorem `-` s) ? (definition `-` s))
 [`LMEM_DEF`; `NULL_NOT_LMEM`];;
@-

@M
@N
close_theory();;
@-
