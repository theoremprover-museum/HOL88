
@D "ml_only" = "true"
@D "mac_changed" = "\n"

@A
% This is a simple example fo using the mweb utility.
% If there is only a single master file, all LaTeX preamble and
% post-amble materials can be included in the master file.
\documentstyle[12pt]{article}

\title{My beautiful proof}
\author{H.O.L. Prover}

\input{mwebmac}
\input{tokmac}

\newtokmac{mlname}{\tt}
\newtokmac{CONST}{\constfont}
\font\sfc=cmssc12 \def\constfont{\sfc}

\begin{document}
\maketitle
@-

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

@N
let LMEM_DEF = new_list_rec_definition(`LMEM_DEF`,
 "(LMEM x [] = F) /\
  (LMEM x (CONS (h:*) t) = (x = h) \/ (LMEM x t))");;
@-

@ {A theorem}
The theorem \mlname{NULL_NOT_LMEM} states that nothing is an element
of an empty list. 

@N
let NULL_NOT_LMEM = prove_thm(`NULL_NOT_LMEM`,
    "!(x:*) l. NULL l ==> ~(LMEM x l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NULL;LMEM_DEF]);;
@-

@M
@N
close_theory();;
@-

@A
\end{document}
@-
