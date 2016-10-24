%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-thyfn.ml                                          %
%                                                                             %
%     DESCRIPTION:      Definitions of functions for creating and accessing   %
%                       theories                                              %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml  %
%                       (commented-out code depends on other ml files as well)%
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`);;


% --------------------------------------------------------------------- %
% ML for coding assumptions so that					%
%  these can be restored on reading in theorems.			%
%									%
% This feature DELETED: TFM 90.12.01					%
% Restored for storing theorems only: TFM 91.04.27			%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Section in which IS_ASSUMPTION_OF hack is implemented.		%
% --------------------------------------------------------------------- %

begin_section IS_ASSUMPTION_OF;;

let IS_ASSUMPTION_OF    = definition `bool` `IS_ASSUMPTION_OF`;;

% --------------------------------------------------------------------- %
% ASSUMPTION_DISCH:							%
%									%
%          A, t1 |- t2							%
%   ---------------------------						%
%   A |- t1 IS_ASSUMPTION_OF t2						%
%									%
% let ASSUMPTION_DISCH t1 th =						%
% EQ_MP (SYM(SPEC(concl th)(SPEC t1 IS_ASSUMPTION_OF))) (DISCH t1 th)	%
% ? failwith `ASSUMPTION_DISCH`;;					%
% --------------------------------------------------------------------- %

let ASSUMPTION_DISCH t1 th =
 mk_thm(disch(t1,hyp th), "^t1 IS_ASSUMPTION_OF ^(concl th)")
 ? failwith`ASSUMPTION_DISCH`;;

letrec ASSUMPTION_DISCH_ALL th =
 ASSUMPTION_DISCH_ALL (ASSUMPTION_DISCH (hd (hyp th)) th)  ?  th;;

% --------------------------------------------------------------------- %
% ASSUMPTION_UNDISCH:							%
%									%
%   A |- t1 IS_ASSUMPTION_OF t2						%
%   ---------------------------						%
%          t1, A1 |- t2							%
%									%
% let ASSUMPTION_UNDISCH th =						%
%  (let ((),t1),t2 = ((dest_comb # I) o dest_comb o concl) th		%
%   in									%
%   UNDISCH (EQ_MP (SPEC t2 (SPEC t1 IS_ASSUMPTION_OF)) th)		%
%  ) ? failwith `ASSUMPTION_UNDISCH`;;					%
% --------------------------------------------------------------------- %

let ASSUMPTION_UNDISCH th =
 (let (C,t1),t2 = ((dest_comb # I) o dest_comb o concl) th
  in
  if fst(dest_const C)=`IS_ASSUMPTION_OF`
  then mk_thm(union[t1](hyp th),t2)
  else fail
 ) ? failwith `ASSUMPTION_UNDISCH`;;

letrec ASSUMPTION_UNDISCH_ALL th =
 ASSUMPTION_UNDISCH_ALL (ASSUMPTION_UNDISCH th) ? th;;

let save_thm(name,th) = 
 ASSUMPTION_UNDISCH_ALL
  (save_thm(name, ASSUMPTION_DISCH_ALL th));;

% --------------------------------------------------------------------- %
% Functions for dealing with the theorems of a theory.			%
% --------------------------------------------------------------------- %

let theorem thy thm = ASSUMPTION_UNDISCH_ALL(theorem thy thm);;	

let delete_thm thy thm = ASSUMPTION_UNDISCH_ALL(delete_thm thy thm);;

% --------------------------------------------------------------------- %
% Revised: no ASSUMPTION_UNDISCH_ALL 			[TFM 90.12.01]  %
%									%
% Note that this OVERWRITES the ML function "theorems".			%
%									%
% ASSUMPTION_UNDISCH_ALL restored [TFM 91.04.27]			%
% --------------------------------------------------------------------- %

let theorems thy =
 mapfilter
  (\(tok,th).
    if tok=`LIST_OF_BINDERS` 
    then fail 
    else (tok, ASSUMPTION_UNDISCH_ALL th))
  (theorems thy);;

% --------------------------------------------------------------------- %
% End of section and export of values.					%
% --------------------------------------------------------------------- %
(save_thm,theorem,delete_thm,theorems);;

end_section IS_ASSUMPTION_OF;;

let (save_thm,theorem,delete_thm,theorems) = it;;

% --------------------------------------------------------------------- %
% Get the (proper) ancestors of a theory.				%
% --------------------------------------------------------------------- %
%< Deleted by WW 05-07-93. A faster implementation is in hol-syn.ml
let ancestors = 
    letrec f st = let ths = parents st in itlist union (map f ths) ths in
    \st. f st ? failwith `ancestors: ` ^ st ^ ` is not an ancestor`;; >%

% --------------------------------------------------------------------- %
% Functions for dealing with the constants of a theory.			%
%									%
% In HOL88 the ML function constants returns all constants, 		%
% including binders and infixes.					%
% --------------------------------------------------------------------- %

% The following definition masks the old value of "constants".		%

let constants = 
    let pp_constants = constants in
    \thy. union (pp_constants thy) (infixes thy);;

% --------------------------------------------------------------------- %
% Functions for dealing with the axioms and definitions of a theory.	%
%									%
% HOL88 versions of the ML functions definition and definitions		%
% apply ASSUMPTION_UNDISCH_ALL to a stored definition.			%
%									%
% Use of ASSUMPTION_UNDISCH_ALL deleted			[TFM 90.12.01]  %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% The following definition masks the old value of "axioms".		%
%									%
% Conditional call to ASSUMPTION_UNDISCH_ALL deleted (conditional on    %
% a undisch_defs flag. 					[TFM 90.12.01]  %
% Adding proof recording for the function definition. [WW 6 Dec. 93]    %
% --------------------------------------------------------------------- %

let (axioms,definition,definitions) =
    let pp_axioms = axioms in 
    let dest_asm_definition t = 
        let C,t1 = dest_comb t in
           if fst(dest_const C)=`HOL_DEFINITION` 
	      then (mk_thm([],t1)) else fail in
 (filter(\ (tok,th). not(is_definition(concl th))) o pp_axioms,
  (\thy name.
    fst(dest_asm_definition(concl(pp_axiom thy name)),
    	RecordStep(DefinitionStep(thy,name))) ? failwith `definition`),
  (mapfilter(\ (tok,th). (tok, dest_asm_definition(concl th))) o
    pp_axioms));;

% --------------------------------------------------------------------- %
% Apply ASSUMPTION_UNDISCH_ALL to output of new_specification.		%
% Can't do this in the original definition in hol-syn.ml because	%
% ASSUMPTION_UNDISCH_ALL is not defined there. 				%
%  Should really reorganize source files!				%
%									%
% Calls to ASSUMPTION_UNDISCH_ALL removed, so this no longer needed	%
%									%
% let new_specification defname flag_name_list th =			%
%     let defth = new_specification defname flag_name_list th 		%
%         in								%
%         if get_flag_value`undisch_defs`				%
%            then ASSUMPTION_UNDISCH_ALL defth				%
%            else defth;;						%
%									%
% [TFM 90.12.01]							%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
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

% --------------------------------------------------------------------- %
%   print_list     : Print a non-empty list, labelled with name, using	%
%		     a supplied printing function prfn.			%
% --------------------------------------------------------------------- %

let print_list incon name prfn l =
    if not (null l) then
    do (print_begin 2;
        print_string name;  print_string ` --`;
        print_break (2,0);
       if incon then print_ibegin 0 
       else print_begin 0;
       map (\x. prfn x; print_break (5,0)) (rev l);
       print_end(); print_end();
       print_newline());;

let print_theory  =

    letrec upto from to = 
           if from>to then [] else from . (upto (from+1) to) in

    let print_tok_ty (tok,ty) = 
	print_begin 2;
        print_string tok;
        print_break (1,0);
        print_type ty;
	print_end() 

    and print_tok_thm (tok,th) = 
        print_begin 2;
        print_string tok;
        print_break (2,0);
        print_thm th;
        print_end()

    and apply_type_op (arity, name) =
        mk_type (name,
	    map (mk_vartype o implode o (replicate `*`)) (upto 1 arity)) 

    and print_tok_all_thm (tok,th) =
        print_begin 2;
        print_string tok;
        print_break (2,0);
        print_all_thm th;
        print_end() in

    let print_const = print_tok_ty o dest_const in

    \tok.let thy = if (tok=`-`) then current_theory() else tok in
         print_string (`The Theory ` ^ thy);  
	 print_newline();
	 print_list true `Parents` print_string (parents thy);
	 print_list true `Types` (print_type o apply_type_op) (types thy);
	 print_list true `Type Abbreviations` print_tok_ty (type_abbrevs thy);
         print_list true `Constants` print_const (constants thy);
         print_list true `Infixes` print_const (infixes thy);
         print_list true `Binders` print_const (binders thy);
         print_list false `Axioms` print_tok_thm (axioms thy); 
         print_list false `Definitions` print_tok_all_thm (definitions thy); 
         print_list false `Theorems` print_tok_all_thm (theorems thy); 
        print_string(`******************** ` ^ thy ^ ` ********************`);
        print_newline();print_newline();;

% --------------------------------------------------------------------- %
% Functions for loading in axioms, definitions and theorems 		%
% --------------------------------------------------------------------- %

% Printing made conditional on value of print_load flag    %
% in HOL88.1.05, MJCG April 6 1989.                        %

let theorem_lfn[thy;th] = theorem thy th;;

% undo_autoload th added in HOL88.1.02 
  to make autoloading in compiled ML files work.
%
let theorem_msg_lfn [thy;th] =
 (if get_flag_value `print_load`
   then (print_string
          (`Theorem `^th^` autoloading from theory \``^thy^`\` ...`);
         print_newline()));
 undo_autoload th;
 theorem thy th;;

% ml_let changed to let_after for HOL88 (MJCG 6/2/89) %
let load_theorem thy th = let_after(th, `theorem_lfn`, [thy;th]);;

let load_theorems thy = 
 map (\(tok,th). load_theorem thy tok) (theorems thy);;

let definition_lfn[thy;th] = definition thy th;;

% undo_autoload th added in HOL88.1.02 
  to make autoloading in compiled ML files work.
%
let definition_msg_lfn [thy;th] =
 (if get_flag_value `print_load`
  then (print_string
         (`Definition `^th^` autoloading from theory \``^thy^`\` ...`);
         print_newline()));
 undo_autoload th;
 definition thy th;;

% ml_let changed to let_after for HOL88 (MJCG 6/2/89) %
let load_definition thy th = let_after(th, `definition_lfn`, [thy;th]);;

let load_definitions thy =
 map (\(tok,th). load_definition thy tok) (definitions thy);;

let axiom_lfn[thy;th] = axiom thy th;;

% undo_autoload th added in HOL88.1.02 
  to make autoloading in compiled ML files work.
%
let axiom_msg_lfn [thy;th] =
 (if get_flag_value `print_load`
   then (print_string(`Axiom `^th^` autoloading from theory \``^thy^`\` ...`);
         print_newline()));
 undo_autoload th;
 axiom thy th;;

% ml_let changed to let_after for HOL88 (MJCG 6/2/89) %
let load_axiom thy th = let_after(th, `axiom_lfn`, [thy;th]);;

let load_axioms thy =
 map (\(tok,th). load_axiom thy tok) (axioms thy);;

% =====================================================================

What follows is now obsolete (and was never debuged) -- see definition of
new_specification on ml/hol-syn.ml for current treatment.

  The code that follows implements constant specifications in which
  the stored definition is not necessarily of the form |- ?x1 ... xn. t,
  be may only be logically equivalent to this. Sequents are encoded as terms
  using the infix constant IS_ASSUMPTION_OF defined by:

     IS_ASSUMPTION_OF = |- !t1 t2. (t1 IS_ASSUMPTION_OF t2) = (t1 ==> t2)

  Evaluating

     new_general_specification
      name 
      [`flag1`,`C1`; ... ; `flagn,Cn`] 
      |- ?x1 ... xn. t[x1,...,xn]
      |- !x1 .... xn. 
          (t1[x1,...,xn] IS_ASSUMPTION_OF
                               .
                               .
                               .
           tm[x1,...,xn] IS_ASSUMPTION_OF t'[x1,...,xn]) =
          t[x1,...,xn]

  specifies C1, ... ,Cn by the definition:

          t1[C1,...,Cn], ... , tm[C1,...,Cn] |- t'[C1,...,Cn])

  Normally, t1, ... , tm would be closed terms, but this is
  not logically necessary.

let new_general_specification defname flag_name_list th eqth =
 let exists_vars,exists_body =
  check_specification defname flag_name_list th
 in
 let forall_vars,forall_body = 
  (n_strip_quant dest_forall (length exists_vars) (concl eqth)
   ? `missing outermost universally quantified variable(s)`)
 in
 if not(forall_vars = exists_vars)
  then failwith`different quantified variables`;
 let left,right = 
  (dest_eq forall_body ? `not a universally quantified equation`)
 in
 if not(right = exists_body)
  then failwith`rhs of equation doesn't match body of existential quantification`;
 map2
  (\((flag,name),var).
   if flag = `constant`
    then new_constant(name,type_of var)
   if flag = `infix`
    then new_infix(name,type_of var)
    else new_binder(name,type_of var))
  (flag_name_list,exists_vars);
 store_definition
  (defname, 
   subst
    (map2
     (\((flag,name),var). (mk_const(name,type_of var),var))
     (flag_name_list,exists_vars))
    left);;

===================================================================== %
