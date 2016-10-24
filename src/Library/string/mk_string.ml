% ===================================================================== %
% FILE		: mk_string.ml						%
% DESCRIPTION   : Creates the theory "string.th".			%
%									%
% PARENTS	: ascii.th						%
% WRITES FILES	: string.th						%
%									%
% AUTHOR	: (c) T. Melham 1988					%
% DATE		: 87.07.27						%
% REVISED	: 90.10.27						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory							%
% --------------------------------------------------------------------- %
new_theory `string`;;

% --------------------------------------------------------------------- %
% Parent theories							%
% --------------------------------------------------------------------- %
new_parent `ascii`;;

% --------------------------------------------------------------------- %
% The following hack allows us to use "``"  in the following type	%
% definition.  This switches off the code that makes `` a constant (of	%
% type :string, in fact) so that we can define `` using new_definition.	%
%									%
% These lisp hacks are purely local to this file...			%
% --------------------------------------------------------------------- %

lisp `(setdebug t)`;;

lisp `(defun mk-ol-atom (x)
    (cond ((memq x spec-toks)  (parse-failed (concat x '| cannot be a term|)))
          ((numberp x) (list 'MK=CONST (atomify x)))
          ((constp x) (list 'MK=CONST x))
          ((eq x tokflag)
           (list 
            'MK=VAR
                (let ((tok (car toklist)))
                     (setq toklist (cdr toklist))
                     (implode
                      (append '(96) (append (exploden tok) '(96)))))))
   	 (t (list 'MK=VAR x))))`;;

lisp `(defun idenp (tok) t)`;;

lisp `(defun constp (tok) (get tok 'const))`;;

% --------------------------------------------------------------------- %
% Note: we need to parse all our strings here, since ` is about to be   %
% made into a letter.							%
% --------------------------------------------------------------------- %

let string_Axiom  = `string_Axiom`;;
let spec          = `string = \`\` | STRING ascii string`;;
let tok 	  = `tok`;;
let string_Induct = `string_Induct`;;
let string_CASES = `string_CASES`;;
let STRING_11 = `STRING_11`;;
let NOT_STRING_EMPTY = `NOT_STRING_EMPTY`;;
let NOT_EMPTY_STRING = `NOT_EMPTY_STRING`;;

new_letter `\``;;

% --------------------------------------------------------------------- %
% define the type :string						%
% --------------------------------------------------------------------- %
let string_Axiom = define_type string_Axiom spec;;

% --------------------------------------------------------------------- %
% Make tok an abbreviation for string, for compatibility with old code  %
% --------------------------------------------------------------------- %
new_type_abbrev(tok, ":string");;

% --------------------------------------------------------------------- %
% prove "induction" theorem for :string.				%
% --------------------------------------------------------------------- %
let string_Induct = 
    save_thm (string_Induct,prove_induction_thm string_Axiom);;

% --------------------------------------------------------------------- %
% prove cases theorem for :string.					%
% --------------------------------------------------------------------- %
let string_CASES = 
    save_thm (string_CASES, prove_cases_thm string_Induct);;

% --------------------------------------------------------------------- %
% prove that the constructor STRING is one-to-one			%
% --------------------------------------------------------------------- %
let STRING_11 = 
    save_thm (STRING_11, prove_constructors_one_one string_Axiom);;

% --------------------------------------------------------------------- %
% prove that the constructors empty_string and STRING are distinct	%
% --------------------------------------------------------------------- %
let NOT_STRING_EMPTY = 
    save_thm (NOT_STRING_EMPTY, prove_constructors_distinct string_Axiom);;

let NOT_EMPTY_STRING =
    save_thm (NOT_EMPTY_STRING,
              GEN_ALL(NOT_EQ_SYM(SPEC_ALL NOT_STRING_EMPTY)));;

close_theory();;

quit();; % Needed for Common Lisp %
