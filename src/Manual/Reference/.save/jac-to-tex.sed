# jac-to-tex.sed: A sed script that transforms a <thing>.doc file into 
#                 tex source code for a reference manual entry on <thing>
/\\begin{verbatim}/d;
s/\\end{verbatim}/\\end{verbatim}}/g;
#s/%//g;
/^*[*]*$/,/^*[*]*$/s/^/\\DOC /g;
/\\DOC [*]*$/d;
/\\DOC.*/s/_/\\_/g;
/\\DOC.*/s/.DOC[ ]*/\\DOC{/g;
/\\DOC.*/s/$/}/g;

/\\DOC.*/a\
\\egroup\
{\\footnotesize\\begin{verbatim}\
PRELIMINARY DOCUMENTATION\
=========================
