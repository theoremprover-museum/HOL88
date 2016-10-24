% --------------------------------------------------------------------- %
% print_doc_file thy (name, |- thm)					%
%									%
% Creates a file called `name.doc' in the current directory, and prints %
% a .doc file for the theorem |- thm into the file in the standard      %
% reference manual format:						%
%									%
% \THEOREM name thy							%
% |- thm								%
% \ENDTHEOREM								%
% --------------------------------------------------------------------- %

let print_doc_file thy (name,thm) = 
   lisp (`(setq poport (outfile '` ^ name ^ `.doc))`);
   print_string (`\\THEOREM ` ^ name ^ ` ` ^ thy);
   print_newline();
   print_thm thm;
   print_newline();
   print_string `\\ENDTHEOREM`;
   print_newline();
   lisp `(close poport)`;
   lisp `(setq poport nil)`;;

% --------------------------------------------------------------------- %
% create_doc_files thy 							%
%									%
% Given the name of a theory file thy, this function creates <name>.doc %
% file in the current directory for each axiom, theorem, and definition %
% in the theory file `thy.th'.  The filenames are generated from the 	%
% names under which the theorems are stored in the theory file.  The    %
% format of these <name>.doc files is the standard format for the 	%
% documentation of theorems in the HOL reference manual.		%
% --------------------------------------------------------------------- %

let create_doc_files thy = 
    let prfn = print_doc_file thy in
    let thms = theorems thy and
        axs  = axioms thy and
	defs = definitions thy in
    map prfn thms; map prfn axs; map prfn defs; ();;
