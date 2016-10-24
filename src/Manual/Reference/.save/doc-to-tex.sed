# doc-to-tex.sed: A sed script that transforms a <thing>.doc file into 
#                 tex source code for a reference manual entry on <thing>
s/{{/<<<<<</g;
s/}}/>>>>>>/g;
s/{/{\\small\\verb%/g;
s/}/%}/g;
s/^{\\small\\verb%[ ]*$/{\\par\\samepage\\setseps\\small\\begin{verbatim}/g;
s/^%}[ ]*$/\\end{verbatim}}/g;
/\\DOC.*/s/_/\\_/g;
/\\DOC.*/s/.DOC[ ]*/\\DOC{/g;
/\\DOC.*/s/$/}/g;
/\\TYPE.*/s/$/\\egroup/g;
/\\THEOREM.*/s/_/\\_/g;
/\\THEOREM.*/s/\\none/{\\none}/g;
s/<<<<<</{/g;
s/>>>>>>/}/g;




