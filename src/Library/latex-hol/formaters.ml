% formaters.ml by Wai Wong ver. 1.0                                     %
% 15 May 1991	    	    	    					%
% This file is the user interface to the pretty printer and formaters	%
%-----------------------------------------------------------------------%

%  Function to write a list of strings to a file.  %

%  Each string is followed by a line-feed.  %
%  The first argument is a file handle.     %

let output_strings port sl =

   % : (string -> string list -> void) %

   do (map (\s. write (port,(s ^ `\L`))) sl);;


%  Combined HOL pretty-printing rules  %

let latex_hol_rules_fun = latex_sets_rules_fun then_try
    	    	    latex_thm_rules_fun then_try
                    latex_term_rules_fun then_try
                    latex_type_rules_fun;;


%  Functions to convert types, terms and theorems into parse-trees.  %

%  The amount of type information included is that required by the rules  %
%  in `hol_rules_fun'.                                                    %

let pp_convert_type t =   % : (type -> print_tree) %

   type_to_print_tree t;;


let pp_convert_term t =   % : (term -> print_tree) %

   term_to_print_tree true (if (get_flag_value `show_types`)
                            then Useful_types
                            else Hidden_types) t;;


%  Hypotheses abbreviated  %

let pp_convert_thm t =   % : (thm -> print_tree) %

   thm_to_print_tree false true (if (get_flag_value `show_types`)
                                 then Useful_types
                                 else Hidden_types) t;;


%  Hypotheses in full  %

let pp_convert_all_thm t =   % : (thm -> print_tree) %

   thm_to_print_tree true true (if (get_flag_value `show_types`)
                                then Useful_types
                                else Hidden_types) t;;

%---------------------------------------------------------------%
% functions to format theorems	    				%
%---------------------------------------------------------------%
let latex_type t =   % : (type -> void) %
   do(pp latex_type_rules_fun `type` [] (pp_convert_type t);
    print_newline());;

let latex_term t =   % : (term -> void) %
   do(pp (latex_sets_rules_fun then_try latex_term_rules_fun then_try
       latex_type_rules_fun) `term` [] (pp_convert_term t);
    print_newline());;

let latex_thm t =   % : (thm -> void) %
   do(pp latex_hol_rules_fun `thm` [] (pp_convert_thm t);
    print_newline());;

let latex_all_thm t =   % : (thm -> void) %
   do(pp latex_hol_rules_fun `thm` [] (pp_convert_all_thm t);
    print_newline());;

let latex_type_to file t =   % : (string -> type -> void) %

 let port = openw file in
 do(   pp_write port 78 0  latex_type_rules_fun `type` [] (pp_convert_type t);
       close port);;

let latex_type_add_to file t =   % : (string -> type -> void) %

 let port = append_openw file in
 do(   pp_write port 78 0  latex_type_rules_fun `type` [] (pp_convert_type t);
       close port);;

let latex_term_to file t =   % : (string -> term -> void) %

 let port = openw file in
 do(   pp_write port 78 0 
    	(latex_sets_rules_fun then_try 
    	 latex_term_rules_fun then_try latex_type_rules_fun)
    	 `term` [] (pp_convert_term t);
       close port);;

let latex_term_add_to file t =   % : (string -> term -> void) %

 let port = append_openw file in
 do(   pp_write port 78 0 
    	(latex_sets_rules_fun then_try 
    	 latex_term_rules_fun then_try latex_type_rules_fun)
    	 `term` [] (pp_convert_term t);
       close port);;

let latex_thm_to file t =   % : (string -> thm -> void) %

 let port = openw file in
 do(   pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_thm t);
       close port);;

let latex_thm_add_to file t =   % : (string -> thm -> void) %

 let port = append_openw file in
 do(   pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_thm t);
       close port);;

let latex_all_thm_to file t =   % : (string -> thm -> void) %

 let port = openw file in
 do(   pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_all_thm t);
       close port);;

let latex_all_thm_add_to file t =   % : (string -> thm -> void) %

 let port = append_openw file in
 do(   pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_all_thm t);
       close port);;



let latex_theory_to file incl s =   % : (string -> bool -> string -> void) %
    % if incl = true, the file generated can be included into other LaTeX file %
    let port = openw file in
    let make_type ispair =      % : ((int # string) -> type) %

      let make_vartypes n =         % : (int -> type list) %

         letrec make_vartypes' n s l =
            % : (int -> string -> type list -> type list) %
            if (n < 1)
            then (rev l)
            else let s' = `*` ^ s
                 in  make_vartypes' (n - 1) s' ((mk_vartype s').l)
         in make_vartypes' n `` []
      in  mk_type (snd ispair, make_vartypes (fst ispair))
    in
    let out_latex_thm t =   % : (thm -> void) %

       (pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_thm t))

    and out_latex_type t =   % : (type -> void) %

       	    (pp_write port 78 0 (latex_type_rules_fun) 
    	    	`type` [] (pp_convert_type t))
    in
   let print_constant t =      % : (term -> void) %

      let (name,typ) = ((dest_const t) ? failwith `print_constant`)
      in  do (output_strings port [`\\item[{\\sf ` ^ (filter_id name) ^ `}]`];
    	    out_latex_type typ)

   and print_theorem (s,t) =      % : (string # thm -> void) %

      do( output_strings port [`\\item[{\\tt ` ^ (filter_id s) ^ `}] $`];
          out_latex_thm t;
    	  output_strings port [`$`])

    and format_section sec env pr_fun l =
    	% : (string -> string -> (string -> void) -> list -> void) %
    	if not (null l) then 
    	do( output_strings port [(`\\sec{` ^ sec ^ `}`);
    	    	(`\\begin{` ^ env ^ `}`)];
    	    map pr_fun (rev l);
    	    output_strings port [(`\\end{` ^ env ^ `}`); ` `]
    	)

   in  do (
    if not incl
    then output_strings port [`\\documentstyle{article}`;
             `\\input holmacs`;
	     (`\\title{The Theory {\\tt ` ^ (filter_id s) ^ `}}`);  
    	     `\\author{} \\date{\\printtimestamp}`;
    	     `\\begin{document}`;
    	     `\\maketitle`;
    	     ` `] 
    else output_strings port [(`\\theory{` ^ (filter_id s) ^ `}`); ` `];

    format_section `Parents` `ttlist` 
    	(\p. write(port, ((filter_id p) ^ `\L`))) (parents s);
    format_section `Types` `ttlist` (out_latex_type o make_type) (types s);
    format_section `Constants` `typelist` print_constant (constants s);
    format_section `Infixes` `typelist` print_constant (infixes s);
    format_section `Binders` `typelist` print_constant (binders s);
    format_section `Axioms` `thmlist` print_theorem (axioms s);
    format_section `Definitions` `thmlist` print_theorem (definitions s);
    format_section `Theorems` `thmlist` print_theorem (theorems s);

    output_strings port [(`\\endthy{` ^ (filter_id s) ^ `}`)];
    if not incl then output_strings port [ `\\end{document}`; ` `];

    close port);;

%-----------------------------------------------------------------------------%

letref latex_thm_tag = `@t `;;
letref latex_thm_end = ``;;

let latex_theorems_to file tfn thmss =
    % : (string -> (string -> thm) -> string list -> void) %
    let port = openw file in
    let out_latex_thm t =   % : (thm -> void) %
       (pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_thm t)) in
    let out_thm thms =
    	do( output_strings port [(latex_thm_tag ^ thms)];
    	    out_latex_thm (tfn thms);
    	    output_strings port [latex_thm_end]) in
    do(
    	map out_thm thmss;
    	close port);;

let latex_all_theorems_to file tfn thmss =
    % : (string -> (string -> thm) -> string list -> void) %
    let port = openw file in
    let out_latex_thm t =   % : (thm -> void) %
       (pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_all_thm t)) in
    let out_thm thms =
    	do( output_strings port [(latex_thm_tag ^ thms)];
    	    out_latex_thm (tfn thms);
    	    output_strings port [latex_thm_end]) in
    do(
    	map out_thm thmss;
    	close port);;

let latex_theorems_add_to file tfn thmss =
    % : (string -> (string -> thm) -> string list -> void) %
    let port = append_openw file in
    let out_latex_thm t =   % : (thm -> void) %
       (pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_thm t)) in
    let out_thm thms =
    	do( output_strings port [(latex_thm_tag ^ thms)];
    	    out_latex_thm (tfn thms);
    	    output_strings port [latex_thm_end]) in
    do(
    	map out_thm thmss;
    	close port);;


let latex_all_theorems_add_to file tfn thmss =
    % : (string -> (string -> thm) -> string list -> void) %
    let port = append_openw file in
    let out_latex_thm t =   % : (thm -> void) %
       (pp_write port 78 0 latex_hol_rules_fun `thm` [] (pp_convert_all_thm t)) in
    let out_thm thms =
    	do( output_strings port [(latex_thm_tag ^ thms)];
    	    out_latex_thm (tfn thms);
    	    output_strings port [latex_thm_end]) in
    do(
    	map out_thm thmss;
    	close port);;