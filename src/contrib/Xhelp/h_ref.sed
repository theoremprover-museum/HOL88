
# SED SCRIPT TO GIVE COMPLETE DOCUMENTATION ON HOL FUNCTION

s/\\#/#/g

s/\\char'136/^/g

s/\\char'056/./g

s/\\char'100/./g

s/{{/<<<<<</g

s/}}/>>>>>>/g

s/{//g

s/}//g

s/^{\\verb%[ ]*$/\\begin{verbatim}/g

s/^%}[ ]*$/\\end{verbatim}/g

/^\\DOC.*$/d

/^\\TYPE/s/^\\TYPE[ ]*//

s/^\\noindent[ ]//g

/\\SYNOPSIS.*/a\

s/^\\SYNOPSIS[ ]*$/SYNOPSIS/g

/\\CATEGORIES.*/a\

s/^\\CATEGORIES[ ]*$/CATEGORIES/g

/\\DESCRIBE.*/a\

s/^\\DESCRIBE[ ]*$/DESCRIPTION/g

/\\FAILURE.*/a\

s/^\\FAILURE[ ]*$/FAILURE CONDITIONS/g

/\\EXAMPLE.*/a\

s/^\\EXAMPLE[ ]*$/EXAMPLES/g


/\\KEYWORDS.*/d


s/^\\KEYWORDS[ ]*$//g

/\\USES.*/a\

s/^\\USES[ ]*$/USES/g

/\\COMMENTS.*/a\

s/^\\COMMENTS[ ]*$/COMMENTS/g

/\\SEEALSO.*/,$s/,//g

/\\SEEALSO.*/,$s/\.//g

s/^\\SEEALSO[ ]*$/SEE ALSO/g

/\\ENDDOC.*/d

s/<<<<<</{/g

s/>>>>>>/}/g














