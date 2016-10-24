

# SED SCRIPT FOR GETTING TWO LINE DESCRIPTION OF A HOL FUNCTION

s/\\#/#/g

s/{{/<<<<<</g

s/}}/>>>>>>/g

s/{//g

s/}//g

s/^{\\verb%[ ]*$/\\begin{verbatim}/g

s/^%}[ ]*$/\\end{verbatim}/g

s/^\\noindent[ ]//g

/^\\DOC.*$/d


/^\\TYPE/s/^\\TYPE[ ]*//

/^$/d

/\\SYNOPSIS.*/d

/\\DESCRIBE.*/,$d


/\\KEYWORD.*/,$d

/\\FAILURE.*/,$d


/\\EXAMPLE.*/,$d

/\\USES.*/,$d

/\\SEEALSO.*/,$d

/\\ENDDOC.*/,$d














