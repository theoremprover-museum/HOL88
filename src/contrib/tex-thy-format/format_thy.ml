% --------------------------------------------------------------------- %
% FILE: format_thy.ml	    	    					%
% By Wai Wong 24 JAN 1990   	    					%
% This file contains some ML functions to print HOL theories in LaTeX   %
% format. It is not a very good solution, however, it works.		%
% This is based on the system function print_theory  in ml\hol-thyfn.ml %
% The user function defined is:	    					%
%   format_theory thy	    	    					%
% It is an analogy to print_theory except the output is in LaTeX format %
% and appear on the terminal. You have to cut and save it in a file.	%
% A better way to do this is to redirect the output to a file. But I do %
% know how to do it. Maybe in new version of HOL, redirection is easier.%
% --------------------------------------------------------------------- %

% define a interface map for all special symbols %
let latex_map = [
	`\\sa `, `!`;
	`\\sc `, `@`;
	`\\sd `, `<=>`;
	`\\se `, `?`;
	`\\sg `, `>=`;
	`\\si `, `/\\`;
	`\\sl `, `<=`;
	`\\sm `, `==>`;
	`\\sn `, `~`;
	`\\so `, `\\/`;
	`\\sr `, `>`;
	`\\ss `, `*`;
	`\\su `, `?!`;
	`\\sv `, `<`];;


% --------------------------------------------------------------------- %
% BELOW are printing functions modified from the original print_theory  %
% print_theory : print the contents of a theory.			%
%									%
% MJCG 31/1/89 for HOL88: print current theory name instead of `-`.	%
%									%
% Utilities for print_theory made local.		 [TFM 90.04.24] %
%									%
% The utilities are:							%
%									%
%   print_tok_ty   : Print a token and type for constants and infixes. 	%
%									%
%   print_tok_thm  : Print a labelled theorem (or axiom)		%
%									%
%   apply_type_op  : Create an example type using arguments of the form %
%		     *, **, ***, etc.   				%
%									%
%   print_tok_all_thm : Print a labelled theorem with its assumptions 	%
% --------------------------------------------------------------------- %

let print_line str =
	do(	print_string str;
	print_newline());;


% --------------------------------------------------------------------- %
%   format_list     : Print a non-empty list, labelled with name, using	%
%		     a supplied printing function prfn.			%
% --------------------------------------------------------------------- %
let format_list incon name prfn l =
    if not (null l) then
    do ( print_line (`\\sec{` ^ name ^ `}`);
       print_line ( `{\\tt` );
       if incon then print_ibegin 0 
       else print_begin 0;
       map (\x. prfn x; print_break (5,0)) (rev l);
       print_end();
       print_line (`}`);
       print_newline());;

let format_thm_list incon name prfn l =
    if not (null l) then
    do ( print_line (`\\sec{` ^ name ^ `}`);
	 print_line (`\\begin{description}`);
       if incon then print_ibegin 0 
       else print_begin 0;
       map (\x. prfn x; print_break (5,0)) (rev l);
       print_end();
       print_line (`\\end{description}`);
       print_newline());;

let format_tok_list incon name prfn l =
    if not (null l) then
    do ( print_line (`\\sec{` ^ name ^ `}`);
	 print_line (`\\begin{description}`);
       if incon then print_ibegin 0 
       else print_begin 0;
       map (\x. prfn x; print_break (5,0)) (rev l);
       print_end();
       print_line (`\\end{description}`);
       print_newline());;

% A list of special symbols which required to be converted to LaTeX	%
% special commands  	    	    					%
let spec_list = [
		 `_`, `\\zm `;
		 `#`, `\\za `;
		 `&`, `\\zd `;
		 `%`, `\\zc `;
		 `$`, `\\zb `;
		 `\\`, `\\zj `;
		 `'`, `\\sz `;
		 `~`, `\\zp `;
		 `*`, `\\ss `;
		 `<`, `\\sv `;
		 `|`, `\\zg `;
		 `>`, `\\sr `;
		 `[`, `\\zi `;
		 `]`, `\\zk `;
		 `^`, `\\zl `;
		 `{`, `\\zn `;
		 `}`, `\\zo `];;

let do_char c = 
    let is_special c = mem c (fst(split spec_list)) in
    (is_special c) => (snd (assoc c spec_list)) | c;;

letrec fil_char l = if null l then []
		 else (do_char (hd l)).(fil_char (tl l));;

let filter_tok tok = concatl (fil_char (explode tok));;

let format_theory  =

    letrec upto from to = 
           if from>to then [] else from . (upto (from+1) to) in

    let print_tok_ty (tok,ty) = 
	print_begin 2;
        print_string (`\\tok{` ^ (filter_tok tok) ^ `}{\\tt `);
	print_break(1,0); 
        print_type ty;
        print_string `}`;
	print_end()

    and print_tok_thm (tok,th) = 
        print_begin 2;
	print_string (`\\thm{` ^ (filter_tok tok) ^ `}{`);
        print_break (2,0);
        print_thm th;
        print_string `}`;
        print_end()

    and apply_type_op (arity, name) =
        mk_type (name,
	    map (mk_vartype o implode o (replicate `*`)) (upto 1 arity))

    and print_tok_all_thm (tok,th) =
        print_begin 2;
	print_string (`\\thm{` ^ (filter_tok tok) ^ `}{`);
        print_break (2,0);
        print_all_thm th;
       print_string `}`;
       print_end()


    and old_map = set_interface_map latex_map 
    and old_lambda = set_lambda `\\sb `
    and old_turnstile = set_turnstile `\\st ` in
	
    let print_const = print_tok_ty o dest_const in

    \tok.let thy = if (tok=`-`) then current_theory() else tok in

    	 print_line (` `);
    	 print_line (`-----BEGINLaTeX`);
	 print_line (`\\documentstyle{article}`);
         print_line (`\\input holmac`);
	 print_line (`\\title{The Theory {\\tt ` ^ thy ^ `}}`);  
	 print_line (`\\author{} \\date{\\printtimestamp}`);
	 print_line (`\\begin{document}`);
	 print_line (`\\maketitle`);
	 print_newline();
	 format_list true `Parents` print_string (parents thy);
	 format_list true `Types` (print_type o apply_type_op) (types thy);
	 format_tok_list true `Type Abbreviations` print_tok_ty (type_abbrevs thy);
         format_tok_list true `Constants` print_const (constants thy);
         format_tok_list true `Infixes` print_const (curried_infixes thy);
         format_tok_list true `Binders` print_const (binders thy);
         format_thm_list false `Axioms` print_tok_thm (axioms thy); 
         format_thm_list false `Definitions` print_tok_all_thm (definitions thy); 
         format_thm_list false `Theorems` print_tok_all_thm (theorems thy); 

        print_newline();
    	print_line( `\\endthy{` ^ thy ^ `}`);
	print_string(`\\end{document}`);

	set_interface_map old_map;
	set_lambda old_lambda;
	set_turnstile old_turnstile;
	print_newline();;
