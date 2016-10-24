% ===================================================================== %
%   FILE NAME        : parser.ml					%
%   USES FILES       : N/A						%
%   DESCRIPTION      : This file sets up the parser-generator.  It uses %
%		       one big section so that we only export the top-  %
%		       level function (parse) for use by users.		%
%									%
%   AUTHOR           : J. Van Tassel					%
%                      <jvt@cl.cam.ac.uk>				%
%									%
%   ORGANIZATION     : University of Cambridge				%
%                      Hardware Verification Group			%
%   ADDRESS          : Computer Laboratory				%
%                      New Museums Site					%
%                      Pembroke Street					%
%                      Cambridge  CB2 3QG				%
%                      England						%
%   PHONE            : +44-223-334729					%
%									%
%   DATE             : Tue Mar 13 1990					%
%   VERSION          : 1						%
%   REVISION HISTORY : Tue Nov 3 1990 Cleaned up and made ready for the %
%                                     release of HOL 1.12               %
% ===================================================================== %

% ********************************************************************* %
% Set add to the help search path to provide on-line help for the one   %
% function exported to the rest of the world.                           %
% ********************************************************************* %

let path = library_pathname() ^ `/parser/help/` in
    set_help_search_path (path . help_search_path());;

begin_section parser;;

% ********************************************************************* %
% We start with some basic functions used by the rest of the generator. %
% ********************************************************************* %

% ===================================================================== %
% EXPECTED: Holds a list of tokens expected on return from individual   %
%           productions and action symbols.                             %
% ===================================================================== %

letref EXPECTED = []:string list;;

% ===================================================================== %
% pg_failwith: Enhanced failwith for reporting encountered during the   %
%              parsing of an input grammar.				%
% ===================================================================== %

let pg_failwith symb prdn reason =
   EXPECTED := [];
   failwith (concat `\L\L    ERROR: symbol "`
            (concat symb
            (concat `" encountered in the wrong place.\L`
            (concat `       -- Production: `
            (concat prdn
            (concat `\L       -- Diagnostic: ` 
            (concat reason `\L`)))))));;

% ===================================================================== %
% escaped: Determine if we have escaped to something that's not an      %
%          "escapable" character.                                       %
% ===================================================================== %

let escaped ch prdn =
    if mem ch [` `;`	`;`\L`] then
       let nch = if ch = ` ` then `<blank>`
                 else if ch = `	` then `<tab>`
                 else `<newline>` in
         pg_failwith nch prdn `escaped to whitespace`
    else if mem ch [`}`;`{`;`]`;`[`] then
       ch
    else if ch = `\\` then
       `\\\\`
    else
       pg_failwith ch prdn `escaped to non-special symbol`;;

% ===================================================================== %
% Suite of I/O functions that tie together terminal and file I/O.  The  %
% string `nil` denotes terminal I/0.                                    %
% ===================================================================== %

let write_string str file =
   if file = `nil` then tty_write str else write(file,str);;

let read_char file =
   if file = `nil` then tty_read() else (read file);;

letrec split_filename path lst first =
   if null (tl lst) then
      if first then
         (hd lst,`./`)
      else
         (hd lst,concatl path)
   else
      split_filename (append path [(hd lst);`/`]) (tl lst) false;;

let close_file file =
   if file = `nil` then ()
   else close file;;

letrec bad_read (ch) =
   if ch = ascii(10) then failwith `bad file name`
   else bad_read (tty_read());;

letrec terminal_read_1 (ch) =
   if ch = ascii(10) then []
   else if mem ch [` ` ; `	`] then bad_read (tty_read())
   else (ch . terminal_read_1 (tty_read ()));;

let terminal_read () =
   implode (terminal_read_1 (tty_read ()));;

% ===================================================================== %
% make_Makefile: Build a skeleton Makefile for the generated parser.    %
% ===================================================================== %

let make_Makefile filename file path =
   let decs = (concat filename `_decls`) in
   let outf = openw (concatl [path;`Makefile.`;file]) in
      write_string `# Generated parser Makefile\L\L` outf;
      write_string `# Version of HOL to be used:\L` outf;
      write_string `HOL=../../hol\L\L` outf;
      write_string `# General definitions for all generated parsers:\L` outf;
      write_string (`GENERAL=`^(library_pathname())^`/parser/general\L\L`) outf;
      write_string `# Insert entries for user-defined stuff here:\L` outf;
      write_string `# Remember to insert the appropriate ` outf;
      write_string `dependencies and "load"'s below.\L\L` outf;
      write_string `# Now compile the declarations:\L` outf;
      write_string (concatl [file;`_decls_ml.o: `;decs;`.ml\L`]) outf;
      write_string `	echo 'set_flag(\`abort_when_fail\`,true);;'\\\L` outf;
      write_string `\T     'loadf \`$(GENERAL)\`;;'\\\L` outf;
      write_string (concatl [`\T     'compilet \``;filename;`_decls\`;;'\\\L`])
                   outf;
      write_string `\T     'quit();;' | $(HOL)\L\L` outf;
      write_string `# Finally do the actual functions\L` outf;
      write_string (file^`_ml.o: `^filename^`.ml `^file^`_decls_ml.o\L`) outf;
      write_string `	echo 'set_flag(\`abort_when_fail\`,true);;'\\\L` outf;
      write_string `\T     'loadf \`$(GENERAL)\`;;'\\\L` outf;
      write_string (concatl [`\T     'loadf \``;decs;`\`;;'\\\L`]) 
                   outf;
      write_string (concatl [`\T     'compilet \``;filename;`\`;;'\\\L`]) outf;
      write_string `	     'quit();;' | $(HOL)\L\L` outf;
      write_string (concatl [`all: `;file;`_ml.o\L`]) outf;
      write_string (concatl [`	@echo '===> Parser "`;file;`" built.'\L\L`]) 
                   outf;
      close outf;;

% ===================================================================== %
% make_makefile: Build a skeleton load file for the generated parser.   %
% ===================================================================== %

let make_makefile filename =
    let (makefile,decs,main) = ((concat filename `_load.ml`),
                                (concat filename `_decls`),
                                filename) in
    let outf = openw makefile in
      write_string `% Generated parser load file\L\L` outf;
      write_string `  First load some basic definitions: %\L` outf;
      write_string (`loadf \``^(library_pathname())^`/parser/general\`;;\L\L`) 
                   outf;
      write_string `% Insert any other files you want loaded here: %\L\L` outf;
      write_string `% Now load the declarations: %\L` outf;
      write_string (concat `loadf \`` 
                   (concat decs `\`;;\L\L`)) outf;
      write_string `% Finally load in the function definitions: %\L` outf;
      write_string (concat `loadf \`` 
                   (concat main `\`;;\L`)) outf;
      close outf;;

let open_file direction filename =
   if filename = `nil` then (`nil`,`nil`) 
   else if mem direction [`in` ; `input` ; `i`] then
      ((openi filename),`nil`)
   else if mem direction [`out`; `output`; `o`] then
      let first_char = if (hd (explode filename)) = `/` then [`/`] else [] in
      let (file,path) = split_filename first_char (words2 `/` filename) true in
         write_string `Opening the file ` `nil`;
         write_string (concat filename `.ml (MAIN OUTPUT)\L`) `nil`;
         write_string `Opening the file ` `nil`;
         write_string (concat filename `_decls.ml (DECLARATIONS)\L`) `nil`;
         write_string `Load the declarations file before the main output.\L` 
                      `nil`;
         make_makefile filename;
         write_string (concat `See the file `
                      (concat filename `_load.ml for a sample.\L`)) `nil`; 
         make_Makefile filename file path;
         write_string (concatl [`See the file `;path;`Makefile.`;file;
                                ` for a sample Makefile.\L`]) `nil`;
      (openw (concat filename `.ml`),openw (concat filename `_decls.ml`))
   else 
      failwith (concat `can't open ` 
               (concat filename 
               (concat ` in direction ` direction)));;

% ===================================================================== %
% Various ways of eating white space to suit different purposes later   %
% on in the generator.							%
% ===================================================================== %

letrec eat_white_space file chr =
   if mem chr [` ` ; `\T` ; `\L` ] then 
      eat_white_space file (read_char file)
   else 
      chr;;

letrec e_w_s file chr =
   if mem chr [` ` ; `\T` ; `\L` ] then e_w_s file (read_char file)
   else if chr = `nil` then failwith `unexpected eof`
   else chr;;

letrec e_w_s_ok file chr =
   if mem chr [` ` ; `\T` ; `\L` ] then e_w_s file (read_char file)
   else if chr = `nil` then `nil`
   else chr;;

% ===================================================================== %
% The mechanism to read in a source file containing an input grammar is %
% contained in the following functions.                                 %
% ===================================================================== %

 % ------------------------------------------------------------------- %
 % write_comments: Write out the rest of a comment after it has been   %
 %                 started.                                            %
 % ------------------------------------------------------------------- %

letrec write_comments ch in_file out_file prdn =
   if ch = `nil` then
      pg_failwith `EOF` prdn
                  `Runnaway comment?  EOF encountered before end of comment.`
   else if ch = `%` then (write_string ch out_file ;
                     write_string `\L` out_file ;
                     e_w_s_ok in_file (read_char in_file))
   else (write_string ch out_file ;
         write_comments (read_char in_file) in_file out_file prdn);;

 % ------------------------------------------------------------------- %
 % get_word1: Helping function for get_word below to finish reading in %
 %            a token from the input grammar.                          %
 % ------------------------------------------------------------------- %

letrec get_word1 in_file lst chr out_file prdn flag =
   if mem chr [` ` ; `\L` ; `	`] then
      (lst, e_w_s in_file (read_char in_file))
   else if chr = `.` then
        if flag = `terminal` then
           get_word1 in_file (append lst [chr]) (read_char in_file)
                     out_file prdn flag
        else
           (lst,chr)
   else if mem chr [`nil`; `[` ; `(` ; `{` ; `}` ; `|` ;`[`;`]`] then 
      (lst,chr)
   else if chr = `%` then
      (write_string (concat `\L` chr) out_file;
       (lst, write_comments (read_char in_file) in_file out_file prdn))
   else if chr = `-` then 
      if flag = `terminal` then
         get_word1 in_file (append lst [chr]) (read_char in_file)
                   out_file prdn flag
      else
         (lst,chr)
   else if chr = `\\` then
      if flag = `terminal` then
         let nch = escaped (read_char in_file) prdn in
         get_word1 in_file (append lst [nch]) (read_char in_file) 
                           out_file prdn flag
      else
         pg_failwith `\\` prdn `escapes can only be done in terminals.`
   else 
      get_word1 in_file (append lst [chr]) (read_char in_file) 
                out_file prdn flag;;

 % ------------------------------------------------------------------- %
 % first_test: Is the current character legal?                         %
 % ------------------------------------------------------------------- %

let first_test flag ch =
    if flag = `first` then
       mem ch (append
                 (words `a b c d e f g h i j k l m n o p q r s t u v w x y z`)
                 (words `A B C D E F G H I J K L M N O P Q R S T U V W X Y Z`))
    else
       true;;

 % ------------------------------------------------------------------- %
 % get_word: Read in a token from the input grammar.                   %
 % ------------------------------------------------------------------- %

letrec get_word in_file ch out_file prdn flag =
   if ch = `nil` then
      (`nil`,`nil`)
   else if ch = `%` then
      (write_string (concat `\L` ch) out_file;
       get_word in_file (write_comments (read_char in_file) 
                                        in_file out_file prdn)
                out_file prdn flag)
   else if ch = `\\` then
      if flag = `terminal` then
         let nch = escaped (read_char in_file) prdn in
         let (wrd,next_ch) = get_word1 in_file [`\\`;nch] (read_char in_file)
                                       out_file prdn flag in
            (implode wrd,next_ch)
      else
         pg_failwith `\\` prdn `escapes can only be done in terminals.`
   else
      (if first_test flag ch then
          let (wrd,next_ch) = get_word1 in_file [ch] (read_char in_file)
                                        out_file prdn flag in
            (implode wrd,next_ch)
       else
          pg_failwith ch prdn `not appropriate first character`);;

 % ------------------------------------------------------------------- %
 % get_inits1: Finish reading in a list of either FIRST_CHARS or CHARS %
 % ------------------------------------------------------------------- %

letrec get_inits1 ch lst file =
   if ch = `\`` then (lst,e_w_s file ` `)
   else if mem ch [`\L`;`\T`] then
        get_inits1 (read_char file) (append lst [` `]) file
   else get_inits1 (read_char file) (append lst [ch]) file;;

 % ------------------------------------------------------------------- %
 % get_inits: Read in a list of either FIRST_CHARS or CHARS.           %
 % ------------------------------------------------------------------- %

let get_inits file ch prdn = 
       if ch = `\`` then 
          let (lst,nch) = get_inits1 (e_w_s file ` `) [] file in
              if nch = `.` then
                 if null lst then
                    pg_failwith (concat prdn ` list`) prdn
                                (concat `can't have empty list of ` prdn)
                 else
                    implode lst
              else
                 pg_failwith nch prdn
                             `improperly terminated string intialiser`
       else
          pg_failwith ch prdn
                      `improperly started string initaliser`;;

 % ------------------------------------------------------------------- %
 % get_inits_specials1: Finish reading in a list of either USEFUL or   %
 %                      IGNORE.                                        %
 % ------------------------------------------------------------------- %

letrec get_inits1_specials ch lst file =
   if ch = `]` then (append lst [`]`],e_w_s file ` `)
   else get_inits1_specials (read_char file) (append lst [ch]) file;;

 % ------------------------------------------------------------------- %
 % get_inits_specials: Read in a list of either USEFUL or IGNORE.      %
 % ------------------------------------------------------------------- %

let get_inits_specials file ch prdn =
    if ch = `[` then
       let (lst,nch) = get_inits1_specials (e_w_s file ` `) [`[`] file in
           if nch = `.` then
              implode lst
           else
              pg_failwith nch prdn
                          `improperly terminated specials list`
    else
       pg_failwith ch prdn
                   `improperly started specials list`;;

% ===================================================================== %
% Define some functions to make various boiler-plate statements.        %
% ===================================================================== %

 % ------------------------------------------------------------------- %
 % separator: Determine what the look-ahead charater is.  It is used   %
 %            during the generation of function definitions and calls. %
 % ------------------------------------------------------------------- %
let separator prev =
    if prev = `sep` then `whitespace` 
    else if prev = `EOF` then `\`nil\``
    else prev;;

 % ------------------------------------------------------------------- %
 % MK_word: Generate a call to gnt (get next token).                   %
 % ------------------------------------------------------------------- %

let MK_word prev =
    [`let`;
      `(WORD,lst)`;`=`;`gnt lst whitespace`;(separator prev);`in`];;

 % ------------------------------------------------------------------- %
 % MK_start: Generate the code to make a list of characters from the   %
 %           current token.                                            %
 % ------------------------------------------------------------------- %

let MK_start prev =
    append (MK_word prev) [`let`;`TOKENS`;`=`;`explode WORD`;`in`];;

% ********************************************************************* %
% We now give the code for retrieving a terminal symbol from the input  %
% grammar.                                                              %
% ********************************************************************* %

% ===================================================================== %
% EOF: A way of generating escaped backquotes as well as the EOF symbol.%
% ===================================================================== %

let EOF word = 
   if word = `EOF` then `nil`
   else if word = `\`` then `\\\``
   else word;;


% ===================================================================== %
% write_conditional: Generate the code for testing a word against a     %
%                    particular string.                                 %
% ===================================================================== %

let write_conditional word =
   [(`WORD` . (`=` .
              [(concatl [`\``;(EOF word);`\``])]))];;

% ===================================================================== %
% write_if: Generate the "if" test for different situations.            %
% ===================================================================== %

let write_if level word =
   if level = `if` then
    append [[`if`]] 
              (append (write_conditional word) [[`then`;`(`]])
   else 
    append [[`?`];[`if`]] 
              (append (write_conditional word) [[`then`;`(`]]);;

% ===================================================================== %
% finish_terminal: Test to see that a terminal symbol was terminated    %
%                  properly.                                            %
% ===================================================================== %

letrec finish_terminal ch prdn_name =
    if ch = `]` then []
    else pg_failwith ch prdn_name 
                     `improperly terminated terminal symbol.`;;

% ===================================================================== %
% epsilon_start: Start each branch of the production.  If we're at the  %
%                beginning, parenthesize only, otherwise put in a fail  %
%                trap.                                                  %
% ===================================================================== %

let epsilon_start level =
    if level = `if` then
       [[`(`]]
    else
       [[`?`];[`(`]];;

% ===================================================================== %
% get_terminal_2: Eat up the characters in a terminal symbol.           %
% ===================================================================== %

letrec get_terminal_2 ch in_file prdn_name =
    if ch = `\\` then
       (escaped (read_char in_file) prdn_name) . 
       (get_terminal_2 (read_char in_file) in_file prdn_name)
    else if ch = `]` then 
       []
    else if mem ch [` `;`\T`; `\L`] then 
       finish_terminal (e_w_s in_file (read_char in_file)) prdn_name
    else 
       ch . get_terminal_2 (read_char in_file) in_file prdn_name ;;

% ===================================================================== %
% is_EOF: Make sure we know about the special symbol `EOF`.             %
% ===================================================================== %

let is_EOF termnal = if termnal = `EOF` then `EOF` else `sep`;;

% ===================================================================== %
% get_terminal_1: If we are in a terminal symbol, check to see if it's  %
%                 empty.  Get the rest of it if it's not.               %
% ===================================================================== %

let get_terminal_1 ch in_file prdn_name level pfail =
    if ch = `]` then 
       (epsilon_start level, e_w_s in_file (read_char in_file),
        `WORD`,false)
    else 
       let termnal = concatl (get_terminal_2 ch in_file prdn_name) in
       (write_if level termnal,
        e_w_s in_file (read_char in_file),is_EOF termnal,true) ;;

% ===================================================================== %
% get_terminal: Check to see if we are starting a terminal symbol.  Get %
%               it from the input grammar if so.                        %
% ===================================================================== %

let get_terminal level ch in_file prdn_name prev_fail =
    if ch = `[` then get_terminal_1 (e_w_s in_file (read_char in_file)) 
                                    in_file prdn_name level prev_fail
    else if level = `if` then ([[`(`]] , ch, `WORD`, false)
    else (epsilon_start level, ch, `WORD`, false);;

% ********************************************************************* %
% We now describe the functions that parse action symbols from the      %
% input grammar and generate the appropriate function calls.            %
%                                                                       %
% A note on methodology:                                                %
%                                                                       %
% We need to parse an action symbol that looks like act(arg1,..,argn),  %
% where each argn is either a reserved symbol (system function) or the  %
% name of some other production in the grammar.  The code corresponding %
% to each of these possibilites can best be described by the sequence:  % 
%                                                                       %
%  A. Simple calls to other productions.                                %
%     Evaluate the function and pass the result to the action.          %
%  B. POP                                                               %
%     Take a result off the intermediate results list and pass it as an %
%     argument to the action in question.                               %
%  C. TOKEN                                                             %
%     Check the current input token to see if it meets the constraints  %
%     of CHARS and FIRST_CHARS, then pass it as an argument to the      %
%     action.                                                           %
%  D. Pass the current input token to the action directly.              %
%                                                                       %
% We need to generate two code segments to do this properly.  One holds %
% all the POP calls.  The other contains the more ordinary calls.  The  %
% two code segments will be joined together after we are finished with  %
% parsing all the arguments.  The POP calls appear first to make sure   %
% that we get any old data before generating new results.               %
% ********************************************************************* %

% ===================================================================== %
% system_function: Check to make sure we are not using a function name  %
%                  that conflicts with one already used by all parsers. %
% ===================================================================== %

let system_function_args next_wd = 
    mem next_wd [`PARSE_text`;`PARSE_file`;`TOKEN_1`;`push`;`pop`;
                 `write_string`;`read_char`;`close_file`;`open_file`;`e_w_s`;
                 `e_w_s_ok`;`determine_lst`;`get_word`;`get_word1`; 
                 `get_word2`;`complete_separator`;`read_input`;
                 `gnt`;`eat_terminal`;`chop_off`;`do_return`;`do_return_1`;
                 `debug_enter`;`debug_on`;`debug_off`;`debug_return`];;

% ===================================================================== %
% prdn_errors: Check that we are using names that are legal.            %
% ===================================================================== %

let prdn_errors_args prdn_name next_wd =
    if system_function_args next_wd then
       pg_failwith next_wd prdn_name
                   (concatl [`"`;next_wd;`" is a system function.`])
    else if next_wd = `type` then
       pg_failwith `type` prdn_name
                   `"type" is a reserved word in HOL.`
    else if next_wd = `MAIN_LOOP` then
       pg_failwith `MAIN_LOOP` prdn_name
                   `"MAIN_LOOP" may not be called.`
    else
       ();;

% ===================================================================== %
% tmp_var: Generate temporary variable names given a running counter.   %
% ===================================================================== %

let tmp_var word number =
   if number = (0-1) then word 
   else if word = `` then ``
   else if word = `nil` then ``
   else concatl (word . (`_` . [(string_of_int number)]));;

% ===================================================================== %
% HOL_term: Are we starting something from HOL (` or ")?                %
% ===================================================================== %

let HOL_term str =
   mem (hd (explode str)) [`\``;`"`];;

% ===================================================================== %
% top_or_middle: Generate a call to push something onto the intermedi-  %
%                ate results list.                                      %
% ===================================================================== %

let top_or_middle new_name = 
    (`result_list` .
    (`=` .
    (`push` .
    (new_name .
    (`result_list` . [])))));;

% ===================================================================== %
% get_args_prdn: Make sure that productions don't have arguments.       %
% ===================================================================== %

let get_args_prdn ch file prdn_name prev =
  if ch = `(` then 
     pg_failwith ch prdn_name `arguments not allowed to non-terminals.`
  else 
     (concatl [`lst whitespace `;(separator prev);
               ` result_list FIRST_CHARS CHARS`], ch);;

% ===================================================================== %
% finish_arg: Make sure that each argument ends with either a comma or  %
%             a parenthesis.                                            %
% ===================================================================== %

let finish_arg ch prdn call =
    if mem ch [`,`;`)`] then []:(string list)
    else pg_failwith ch prdn 
                     (concatl [`strange terminator for an argument to `;
                               call;`.`]);;

% ===================================================================== %
% get_argn1: Helping function for get_arg_name to finish reading in a   %
%            particular argument name.                                  %
% ===================================================================== %

letrec get_argn1 ch file prdn call flag hol_flag =
    if mem ch [`,`;`)`] then []
    else if mem ch [` `;`\T`;`\L`] then
       finish_arg (e_w_s file (read_char file)) prdn call
    else if hol_flag then
       ch . get_argn1 (read_char file) file prdn call `any` hol_flag
    else if ch = `-` then
       pg_failwith ch prdn
                   (concatl [`use underscores rather than dashes`])
    else
       (if first_test flag ch then
           ch . get_argn1 (read_char file) file prdn call `any` hol_flag
        else
           pg_failwith ch prdn `not an appropriate first character`);;

% ===================================================================== %
% get_arg_name: Begin reading in an argument name.                      %
% ===================================================================== %

let get_arg_name ch file prdn call start =
    if ch = `,` then
       pg_failwith ch prdn
                   (concatl [`empty argument to `;call;`.`])
    else if ch = `)` then
       if start then
          pg_failwith ch prdn
                      (concatl [call;` must have at least one argument.`])
       else
          (`nil`,`)`)
    else
       let wrd = get_argn1 (e_w_s file ch) file prdn call `any` 
                           (if mem ch [`\``;`"`] then true else false) in
           (implode wrd,e_w_s file (read_char file));;

% ===================================================================== %
% add_new_calls: Set things up for code generation for the action's     %
%                arguments depending on wether or not we're using a     %
%                system function.                                       %
% ===================================================================== %

let add_new_calls tmp_calls argn calls pops =
    if mem argn [`POP`;`TOKEN`;`WORD`] then
       (append pops tmp_calls,calls)
    else
       (pops,append calls tmp_calls);;

% ===================================================================== %
% require_start: Decide if we need to check TOKENS.                     %
% ===================================================================== %

let require_start prev tmp_name call =
    let tmp_calls = if prev = `WORD` then [] else MK_start prev in
        if call = `WORD` then 
           (append tmp_calls [`let`;tmp_name;`= WORD`;`NOMARK`;`in`],`sep`)
        else
           (append tmp_calls [`let`;tmp_name;`= TOKEN TOKENS`;
                              `FIRST_CHARS`;`CHARS`;`(hd lst)`;`MARK`;`in`], 
            `sep`);;

% ===================================================================== %
% neet_to_use_pops:  Generate the code to pop things off of the results %
%                    list if needed.                                    %
% ===================================================================== %

let need_to_use_pops pop_size =
    if pop_size = 0 then
       []
    else
       [`let`;`(result_list,pop_list) = chop_off`;(string_of_int pop_size);
        `[] result_list`;`in`];;

% ===================================================================== %
% add_EXPECTED: Add something to the EXPECTED list as required.         %
% ===================================================================== %

let add_EXPECTED thing flag =
  if flag then
     EXPECTED := append EXPECTED [thing]
  else
     EXPECTED;;

% ===================================================================== %
% pop_or_reg: Generate a call to pop something or a regular function    %
%             call as required.                                         %
% ===================================================================== %

let pop_or_reg call prev t_par =
    if call = `POP` then
       ([`) = (pop pop_list)`],prev,`pop_list`,t_par)
    else
       (add_EXPECTED `\`nil\`` (not t_par);
       ([`, prev, lst) = `;call;` lst whitespace `;(separator prev);
                 ` result_list FIRST_CHARS CHARS`;`MARK`],
        `prev`,`result_list`,false));;

% ===================================================================== %
% mk_lets: Generate the appropriate "let" statement.                    %
% ===================================================================== %

let mk_lets call gen_num prev t_par =
    if call = `nil` then
       ([],``,gen_num,prev,t_par)
    else if mem call [`WORD`;`TOKEN`] then
       let tmp_name = (tmp_var call gen_num) in
       add_EXPECTED `\`nil\`` (not t_par);
       let (new_call,nprev) = require_start prev tmp_name call in
       (new_call,tmp_name,gen_num+1,nprev,false)
    else if HOL_term call then
       ([],call,gen_num,prev,t_par)
    else
       let tmp_name = (tmp_var call gen_num) and
           (pop_call,nprev,result_list,ntp) = pop_or_reg call prev t_par in 
       (append [`let`;(concat `(` tmp_name);`,`;result_list]
               (append pop_call [`in`]), tmp_name,gen_num+1,nprev,ntp);;

% ===================================================================== %
% comma: Add a comma to an argument if we need to.                      %
% ===================================================================== %

let comma start arg =
    if start then arg
    else concat `,` arg;;

% ===================================================================== %
% failed_arg: Make sure we are not doing something improper by calling  %
%             a function that we shouldn't be.                          %
% ===================================================================== %

let failed_arg argn =
   mem argn [`TOKEN_1`;`PARSE`;`MAIN_LOOP`];;

% ===================================================================== %
% preprocess_args: Go through the argument list putting together the    %
%                  various sequences of calls.                          %
% ===================================================================== %

letrec preprocess_args ch calls pops args file prdn gen_num 
                       prev call start pop_ctr t_par  =
    if ch = `}` then
       if start then
          pg_failwith ch prdn (concatl [`bad argument to `;call;`.`])
       else
          (append pops calls,e_w_s file (read_char file),gen_num,
           append args [`)`],pop_ctr,prev,t_par)
    else if ch = `)` then
       if start then
          pg_failwith ch prdn (concatl [call;` must have some arguments.`])
       else
          (append pops calls,e_w_s file (read_char file),gen_num,
           append args [`)`],pop_ctr,prev,t_par)
    else
       let (argn,nch) = get_arg_name ch file prdn call start in
           if failed_arg argn then
              pg_failwith argn prdn
                          (concatl [`"`;argn;
                                    `" is not allowed as an argument.`])
           else
              (prdn_errors_args prdn argn;
              let (tmp_calls,narg,ngen_num,nprev,ntp) = mk_lets argn gen_num
                                                                prev t_par
              and npop_ctr = if argn = `POP` then pop_ctr+1 else pop_ctr in
              let (npops,ncalls) = add_new_calls tmp_calls argn calls pops in
                 preprocess_args nch ncalls npops (append args 
                                                          [(comma start narg)]) 
                                 file prdn ngen_num nprev call false 
                                 npop_ctr ntp);;

% ===================================================================== %
% get_args_act: Parse out the arguments to an action, and put the calls %
%               together so that they may be glued into the output.     %
% ===================================================================== %

let get_args_act ch file call letrefs gen_num prdn prev t_par =
    if ch = `(` then
       let (lrefs,nch,ngen_num,args,pop_size,nprev,ntp) =
              preprocess_args (e_w_s file (read_char file)) [] [] [`(`] file
                              prdn gen_num prev call true 0 t_par in
           (append letrefs (append [(need_to_use_pops pop_size)] [lrefs]),
            call . args,ngen_num,nch,nprev,ntp)
    else if ch = `}` then
       (letrefs,[(call^`()`)],gen_num,(e_w_s file (read_char file)),prev,t_par)
    else pg_failwith ch prdn (concatl [`can't understand symbol "`;ch;
                                       `" after the action "`;call;`".`]);;

% ********************************************************************* %
% We now describe functions that implement a restricted ML pretty       %
% printer.  This part of the generator is not, strictly speaking,       %
% required.  BUT, it did make debugging easier.                         %
% ********************************************************************* %

% ===================================================================== %
% write_tabs: Write out a certain number of blanks.                     %
% ===================================================================== %

letrec write_tabs tabs file =
   if tabs = 0 then () 
   else (write_string ` ` file ; write_tabs (tabs-1) file);;

% ===================================================================== %
% then_if: Increment the tab count if the previous token was "else"     %
% ===================================================================== %

let then_if t pp =
   if pp = `else` then (t + 4) else t;;

% ===================================================================== %
% pop_EXPECTED: Pop something off the EXPECTED list to fill in a blank. %
% ===================================================================== %

let pop_EXPECTED () = 
    if null EXPECTED then
       failwith `bad match in EXPECTED`
    else
       let tmp = hd EXPECTED in
           EXPECTED := tl EXPECTED;
           tmp;;

% ===================================================================== %
% write_final: Write a fragment to the named file in a nice (?) format  %
% ===================================================================== %

letrec write_final file lst tabs pch =
   if null lst then (tabs,pch)
   else 
      (let word = (hd lst) in
         if word = `` then
            write_final file (tl lst) tabs pch
         else if word = `;;` then
            (write_string `;;` file;
             write_string (ascii 10) file;
             write_string (ascii 10) file;
             write_final file (tl lst) 0 `st`)
         else if word = `NOMARK` then
            (pop_EXPECTED();
             write_final file (tl lst) tabs pch)
         else if word = `MARK` then
            (write_string (concat ` ` (pop_EXPECTED ())) file;
             write_final file (tl lst) tabs pch)
         else if word = `?` then
            (write_string `\L` file;
             write_tabs 2 file;
             write_string `?` file;
             write_final file (tl lst) 4 `let`)
         else if word = `.` then
            (if pch = `st` then
                (write_string word file;
                 write_final file (tl lst) (tabs+4) `let`)
             else
                (write_string word file;
                 write_final file (tl lst) tabs pch))
         else if mem word [`( `; ` ( ` ; `(`] then
            (if (pch = `then`) then
                (write_string (ascii 10) file;
                 write_tabs (then_if tabs pch) file;
                 write_string `(` file;
                 write_final file (tl lst) ((then_if tabs pch)+1) `(`)
             else
                ((if tabs > 5 then
                     write_string `` file
                  else
                     (write_string (ascii 10) file;
                      write_tabs tabs file));
                 write_string `(` file;
                 write_final file (tl lst) (tabs+1) `(`))
         else if word = `)` then
            (write_string `)` file;
             write_final file (tl lst) (tabs-1) `)`)
         else if word = `if` then
            (if pch = `if` then
                 (write_string (ascii 10) file;
                  write_tabs (tabs+4) file;
                  write_string word file;
                  write_final file (tl lst) (tabs+4) `if`)
             else if pch = `(` then
                (write_string `if` file;
                 write_final file (tl lst) (tabs+4) `if`)
             else
                (write_string (ascii 10) file;
                 write_tabs tabs file;
                 write_string word file;
                 write_final file (tl lst) (tabs+4) `if`))
         else if word = `else` then
            (write_string (ascii 10) file;
             write_tabs (tabs-4) file;
             write_string `else\L` file;
             write_tabs tabs file;
             write_final file (tl lst) tabs `else`)
         else if mem word [`in`;`then`] then
            (write_string (concat ` ` word) file;
             write_final file (tl lst) tabs `then`)
         else if mem word [`let`;`letrec`] then
            (if pch = `st` then
                (write_string word file;
                 write_final file (tl lst) (tabs+4) `let`)
             else if pch = `(` then
                (write_string word file;
                 write_final file (tl lst) tabs `let`)
             else if pch = `else` then
                (write_string (ascii 10) file;
                 write_tabs (tabs+4) file;
                 write_string word file;
                 write_final file (tl lst) (tabs+4) `let`)
             else
                (write_string (ascii 10) file;
                 write_tabs tabs file;
                 write_string word file;
                 write_final file (tl lst) tabs `let`))
         else if word = `;` then
             (write_string `;\L` file;
              write_tabs (tabs-1) file;
              write_final file (tl lst) tabs pch)
         else
            (if pch = `then` then
                (write_string (ascii 10) file;
                 write_tabs tabs file;
                 write_string word file;
                 write_final file (tl lst) tabs ``)
             else if pch = `(` then
                (write_string word file;
                 write_final file (tl lst) tabs ``)
             else if pch = `st` then
                (write_string word file;
                 write_final file (tl lst) tabs pch)
             else
                (write_string ` ` file;
                 write_string (hd lst) file; 
                 write_final file (tl lst) tabs pch)));;

% ===================================================================== %
% write_final_all: Write each code fragment to the output stream.       %
% ===================================================================== %

letrec write_final_all lst file tabs pch =
   if null lst then () 
   else
      let (tabs',pch') = write_final file (hd lst) tabs pch in
         write_final_all (tl lst) file tabs' pch';;

% ********************************************************************* %
% We now describe the functions that go through individual productions  %
% in the input grammar, and generate ML code for them.                  %
% ********************************************************************* %

% ===================================================================== %
% eat_arrow: Eat an arrow (the name says it all).                       %
% ===================================================================== %

letrec eat_arrow prdn_name ch in_file n =
   if n = 2 then
      if ch = `>` then (e_w_s in_file ` `)
      else pg_failwith ch prdn_name `strange ending for an arrow.`
   else if ch = `-` then
      eat_arrow prdn_name (read_char in_file) in_file (n+1)
   else failwith pg_failwith ch prdn_name `strange character in arrow.`;;

% ===================================================================== %
% unwind_parens: Construct enough parentheses to match the open ones.   %
% ===================================================================== %

letrec unwind_parens par =
   if par = 0 then []
   else (`)` . (unwind_parens (par-1)));;

% ===================================================================== %
% finish_arm: Put the code for a given arm of a production together.    %
% ===================================================================== %

let finish_arm whole letrefs return failed parens next_thing =
    (append whole 
            (append letrefs
                    (append [return]
                            (append [parens]
                                    (append failed next_thing)))));;

% ===================================================================== %
% new_letrefs: Generate a new "let" statement.                          %
% ===================================================================== %

let new_letrefs new_name next_wd args flag =
    [[next_wd;args;(if flag then `MARK` else ``);`in`;`let`];
     (top_or_middle new_name);[`in`]];;

% ===================================================================== %
% NT_letrefs: Make a "let" statement for non-terminal symbols.          %
% ===================================================================== %

let NT_letrefs new_name next_wd args =
    append [[`let`;(concat `(` new_name);`,`; `result_list`;`, prev, lst) =`]]
           (new_letrefs new_name next_wd args true);;
 
% ===================================================================== %
% ACTION_letrefs: Make a "let" statement after returning from an action %
%                 symbol.                                               %
% ===================================================================== %

let ACTION_letrefs new_name next_wd args =
    append [[`let` ; new_name ; `=`]]
           (new_letrefs new_name next_wd args false);;

% ===================================================================== %
% MK_failed: If we need to fail here, generate the code.                %
% ===================================================================== %

let MK_failed failcond prdn msg update_list =
    if failcond then
       [[`else`];[`fail`]]
    else
       [[]];;

% ===================================================================== %
% MK_return: generate a call to the "do_return" function.               %
% ===================================================================== %

let MK_return prev flag prdn =
    [(`do_return result_list whitespace \``^prdn^`\` `^separator prev^` lst `
      ^(if flag then `expected` else `\`nil\``))];;

% ===================================================================== %
% system_function: Are we using a system function?                      %
% ===================================================================== %

let system_function next_wd = 
    mem next_wd [`TOKEN`;`PARSE_text`;`PARSE_file`;`TOKEN_1`;`push`;`pop`;
                 `write_string`;`read_char`;`close_file`;`open_file`;`e_w_s`;
                 `e_w_s_ok`;`determine_lst`;`get_word`;`get_word1`; 
                 `get_word2`;`complete_separator`;`read_input`;
                 `gnt`;`eat_terminal`;`chop_off`;`do_return`;`do_return_1`;
                 `debug_enter`;`debug_on`;`debug_off`;`debug_return`];;

% ===================================================================== %
% terminal_errors: Different kinds of errors at the end of terminals.   %
% ===================================================================== %

let terminal_errors prdn_name next_wd next_ch =
    if next_wd = `]` then
       pg_failwith next_wd prdn_name `can't have imbedded epsilons.`
    else if not (next_ch = `]`) then
         pg_failwith next_ch prdn_name
                     (concatl [`improper ending to terminal_sybol "`;
                               next_wd;`" (\``;next_ch;`\`).`])
    else
       ();;

% ===================================================================== %
% prdn_errors: Different errors that can occur when trying to parse a   %
%              production name.                                         %
% ===================================================================== %

let prdn_errors prdn_name next_wd =
    if system_function next_wd then
       pg_failwith next_wd prdn_name
                   (concatl [`"`;next_wd;`" is a system function.`])
    else if next_wd = `type` then
       pg_failwith `type` prdn_name
                   `"type" is a reserved word in HOL.`
    else if next_wd = `WORD` then
       pg_failwith `WORD` prdn_name
                   `"WORD" is a reserved word.`
    else if next_wd = `TOKEN` then
       pg_failwith `TOKEN` prdn_name
                   `calls to "TOKEN" may not be non-terminals.`
    else if next_wd = `MAIN_LOOP` then
       pg_failwith `MAIN_LOOP` prdn_name
                   `"MAIN_LOOP" may not be called.`
    else if next_wd = `-->` then
       pg_failwith `-->` prdn_name
                   (concatl [`no terminating \`.\` in the production "`;
                             prdn_name;`".`])
    else
       ();;

% ===================================================================== %
% action_errors: The different things you CAN'T have as action symbol   %
%                names.                                                 %
% ===================================================================== %

let action_errors prdn_name act_name =
    if mem act_name [`TOKEN`;`TOKEN_1`;`PARSE_file`;`PARSE_text`;`MAIN_LOOP`;
                     `push`;`pop`;`write_string`;`read_char`;`close_file`;
                     `open_file`;`e_w_s`;`e_w_s_ok`;`determine_lst`;`get_word`;
                     `get_word1`;`get_word2`;`complete_separator`;`read_input`;
                     `gnt`;`eat_terminal`;`chop_off`;`do_return`;
                     `do_return_1`;`debug_enter`;`debug_on`;`debug_off`;
                     `debug_return`;`WORD`] then
       pg_failwith act_name prdn_name
                   (concatl [`can't use "`;act_name;
                             `" as the name of an action.`])
    else
       ();;

% ===================================================================== %
% final_trap: Generate an ending "fail" if required.                    %
% ===================================================================== %

let final_trap flag prdn =
    if flag then
       [[`?`];[`fail`];[`;;`]]
    else
       [[`;;`]];;

% ===================================================================== %
% get_rest_of_prdn: Here it is, the one you've all been waiting for.    %
%                   We parse in a given productions generating the ML   %
%                   code that implements it.                            %
% ===================================================================== %

letrec get_rest_of_prdn prdn_name letrefs whole ch in_file par
                        tmp_num failcond out_file prev t_par =
   if ch = `.` then 
      (add_EXPECTED `expected` (not t_par);
       finish_arm whole letrefs (MK_return prev t_par prdn_name) 
                  (MK_failed failcond prdn_name `` true)
                  (unwind_parens par) (final_trap failcond prdn_name))
   else if ch = `|` then
      let (condition,next_ch,nprev,nfailcond) = (get_terminal `else`
                                                     (e_w_s in_file ` `)
                                                     in_file prdn_name
                                                     failcond) in
          add_EXPECTED `expected` (not t_par);
          get_rest_of_prdn prdn_name [[``]]
                           (finish_arm whole letrefs 
                                       (MK_return prev t_par prdn_name)
                                       (MK_failed failcond prdn_name `` false)
                                       (unwind_parens par) condition) 
                           next_ch in_file 1 0 nfailcond out_file 
                           nprev true
   else if ch = `{` then 
      let (act_name,next_ch) = get_word in_file (e_w_s in_file ` `)
                                        out_file prdn_name `first` in
          action_errors prdn_name act_name; 
          let (lrefs,call,t_num,nnext_ch,nprev,ntp) = get_args_act next_ch 
                                                            in_file act_name 
                                                            letrefs tmp_num  
                                                            prdn_name prev
                                                            t_par in
             get_rest_of_prdn prdn_name (append lrefs 
                                                (ACTION_letrefs
                                                        (tmp_var `tmp` t_num)
                                                        (concatl call) ``))
                              whole nnext_ch in_file par t_num
                              failcond out_file nprev ntp
   else if ch = `[` then
      let (next_wd,next_ch) = get_word in_file (e_w_s in_file 
                                                      (read_char in_file)) 
                                       out_file prdn_name `terminal` in
           terminal_errors prdn_name next_wd next_ch;
           let nxt = EOF next_wd in
           add_EXPECTED (`\``^nxt^`\``) (not t_par);
           get_rest_of_prdn prdn_name 
                            (append letrefs 
                                    [(if prev = `WORD` then [] 
                                      else MK_word prev);
                                     [`let`;`(WORD,lst)`;`=`;`eat_terminal`;
                                      (concatl [`\``;nxt;`\``]);`WORD`;`lst`;
                                      (concatl [`\``;prdn_name;`\``])];
                                     [`in`];
                                     [`let`;`TOKENS`;`=`;`explode WORD`;`in`]])
                            whole (e_w_s in_file (read_char in_file)) in_file
                            par tmp_num failcond out_file `WORD` true
   else
      let (next_wd , next_ch) = get_word in_file ch out_file 
                                         prdn_name `first` in
         prdn_errors prdn_name next_wd;
         let (args , nnext_ch) = get_args_prdn next_ch in_file prdn_name prev
         and new_name = (tmp_var next_wd tmp_num) in
             add_EXPECTED `\`nil\`` (not t_par);
             get_rest_of_prdn prdn_name (append letrefs (NT_letrefs new_name
                                                             next_wd args))
                              whole nnext_ch in_file par (tmp_num+1)
                              failcond out_file `prev` false;;

% ===================================================================== %
% process: Drives get_rest_of_prdn by initialising some variables and   %
%          getting the code for the first terminal symbol if it exists. %
% ===================================================================== %

let process in_file prdn_name ch out_file =
  let (args,next_ch) = get_args_prdn ch in_file prdn_name `prev`
  in
  let nnext_ch = eat_arrow prdn_name next_ch in_file 0
  in
  let (condition,nnnext_ch,nprev,failcond) = get_terminal `if` nnext_ch 
                                                          in_file
                                                          prdn_name false
  in
      EXPECTED := [];
      get_rest_of_prdn prdn_name [] condition nnnext_ch in_file 1 0 
                       failcond out_file nprev true;;

% ===================================================================== %
% MK_lambda: Start out the lambda expression for a given production.    %
% ===================================================================== %

let MK_lambda wrd call_list =
    append [[wrd;`:=`;`\L`;
             `   \\lst `;`whitespace `;`prev `;
             `result_list `;`FIRST_CHARS `;`CHARS `; `expected`];
            [`.`]]
            (append [(MK_start `prev`)]
                    (append [[(`debug_enter(\``^wrd^`\`,expected,WORD)`);`;`]]
                    call_list));;

% ===================================================================== %
% write_decs: Output the dummy declaration for a given production.      %
% ===================================================================== %

let write_decs wrd out_file out_type =
    write_string `letref ` out_file;
    write_string wrd out_file;
    write_string `\L   (lst:string list) (whitespace:string)`
                 out_file;
    write_string `(prev:string)\L` out_file;
    write_string `   (result_list:` out_file;
    write_string out_type out_file;
    write_string ` list)\L` out_file;
    write_string `   (FIRST_CHARS:string list) (CHARS:string list) ` out_file;
    write_string `(expected:string) =\L` out_file;
    write_string `   (fail:` out_file;
    write_string out_type out_file;
    write_string `,fail:` out_file;
    write_string out_type out_file;
    write_string ` list,fail:string,fail:string list);;\L\L` out_file;;

% ===================================================================== %
% make_main_wrapper: Generate the functions PARSE_file and PARSE_text   %
%                    when the production MAIN_LOOP is encountered.      %
% ===================================================================== %

let make_main_wrapper out_file =
   write_string `\L\L Generating PARSE_file and PARSE_text ` `nil`;
   write_string `(MAIN_LOOP used).\L\L` `nil`;
   write_string `let PARSE_file (in_file,whitespace,separators) =\L` out_file;
   write_string `   let white = if null whitespace then\L` out_file;
   write_string `                  [\` \`;\`\\T\`;\`\\L\`]\L` out_file;
   write_string `               else\L` out_file;
   write_string `                  whitespace and\L` out_file;
   write_string `       inf = open_file \`in\` in_file in\L` out_file;
   write_string `   let WORD = e_w_s inf (hd white) white in\L` out_file;
   write_string `   let lst = read_input inf [] white separators ` out_file;
   write_string `WORD IGNORE USEFUL in\L` out_file;
   write_string `   let (WORD,lst) = (hd lst,tl lst) in\L` out_file;
   write_string `   let result = fst (MAIN_LOOP lst (hd white) ` out_file;
   write_string `WORD []\L` out_file;
   write_string `                               FIRST_CHARS CHARS` out_file;
   write_string ` \`nil\`) in\L` out_file;
   write_string `       result\L` out_file;
   write_string `   ? fail;;\L\L` out_file;
   write_string `let PARSE_text (text,whitespace,separators) =\L` out_file;
   write_string `    let outf = open_file \`out\` ` out_file;
   write_string `\`/tmp/.000HOL\` in\L` out_file;
   write_string `    write_string text outf;\L` out_file;
   write_string `    close_file outf;\L` out_file;
   write_string `    let result = PARSE_file (\`/tmp/.000HOL\`,` out_file;
   write_string `whitespace,separators) in\L` out_file;
   write_string `        unlink \`/tmp/.000HOL\`; result;;\L\L` out_file;;

% ===================================================================== %
% emit_firsts: Output the code for CHARS or FIRST_CHARS.                %
% ===================================================================== %

let emit_firsts wrd firsts file =
   if can implode (words firsts) then
      write_string (concatl [wrd;` := words \``;firsts;`\`;;\L\L`])
                   file
   else
      pg_failwith firsts wrd
                  (concatl [wrd;` must be a list of single characters.`]);;

% ===================================================================== %
% emit_specials: Output the code for IGNORE or USEFUL.                  %
% ===================================================================== %

let emit_specials wrd specials file =
    write_string (concatl [wrd;` := `;specials;`;;\L\L`]) file;;

% ===================================================================== %
% token_failwith: Error message used while generating the tokeniser.    %
% ===================================================================== %

let token_failwith missing =
    failwith (concat `\L\L     ERROR in tokeniser generator.\L`
             (concat `       -- Problem: no definition of `
             (concat missing `.\L`)));;

% ===================================================================== %
% make_tokeniser: Generate the functions TOKEN and TOKEN_1 to check the %
%                 vailidity of an input token against CHARS and         %
%                 FIRST_CHARS.                                          %
% ===================================================================== %

let make_tokeniser out_file firsts chars =
    if not firsts then
       if chars then
          token_failwith `FIRST_CHARS` out_file
       else close_file out_file
    else if not chars then
       if firsts then
          token_failwith `CHARS` out_file
       else close_file out_file
    else
       (write_string `letrec TOKEN_1 TOKENS CHARS =\L` out_file;
        write_string `   if null TOKENS then ()\L` out_file;
        write_string `   else if mem (hd TOKENS) CHARS then\L` out_file;
        write_string `      TOKEN_1 (tl TOKENS) CHARS\L` out_file;
        write_string `   else\L` out_file;
        write_string `      fail;;\L\L` out_file;
        write_string `let TOKEN TOKENS FIRST_CHARS CHARS next expected =\L` 
                      out_file;
        write_string `   if mem (hd TOKENS) FIRST_CHARS then\L` out_file;
        write_string `      (TOKEN_1 (tl TOKENS) CHARS;\L` out_file;
        write_string `       let wrd = implode TOKENS in\L` out_file;
        write_string `         if expected = \`nil\` then\L` out_file;
        write_string `             wrd\L` out_file;
        write_string `         else if expected = next then\L` out_file;
        write_string `             wrd\L` out_file;
        write_string `         else fail)\L` out_file;
        write_string `   else\L` out_file;
        write_string `      fail\L` out_file;
        write_string `   ? fail;;\L\L` out_file;
        close_file out_file);;

% ===================================================================== %
% decls_fail: Convenient wrapper for pg_failwith used in decls_errors.  %
% ===================================================================== %

let decls_fail wrd =
    pg_failwith wrd wrd
                (concatl [`multiple definitions of "`;wrd;
                          `" are not allowed.`]);;

% ===================================================================== %
% decls_errors: Make sure everything is defined as far as CHARS and     %
%               FIRST_CHARS are concerned.                              %
% ===================================================================== %

let decls_errors wrd firsts chars =
    if wrd = `FIRST_CHARS` then
       if firsts then
          decls_fail wrd
        else
          (true,chars)
    else
       (if chars then
          decls_fail wrd
       else
          (firsts,true));;

% ===================================================================== %
% make_productions: Overall driver for deciding if we're dealing with   %
%                   a declaration or a production.  The appropriate     %
%                   function is called, and the code for it is gener-   %
%                   ated.                                               %
% ===================================================================== %

letrec make_productions in_file out_file out_decs out_type firsts chars =
   let (wrd , ch) = get_word in_file (eat_white_space in_file ` `) out_file
                             `UNKNOWN (starting a new one)` `first` in
         if ch = `nil` then 
            (close_file in_file ; close_file out_file;
             make_tokeniser out_decs firsts chars)
         else if wrd = `type` then
            pg_failwith wrd wrd
                        `"type" is a reserved word in HOL.`
         else if mem wrd [`TOKEN`;`PARSE`] then
            pg_failwith wrd wrd
                        (concatl [`can't use "`;wrd;`" as a production name.`])
         else if wrd = `TOKEN_1` then
            pg_failwith `TOKEN_1` `TOKEN_1` 
                        `"TOKEN_1" is a system function.`
         else if mem wrd [`FIRST_CHARS`;`CHARS`] then
            let (nfirsts,nchars) = decls_errors wrd firsts chars in
                emit_firsts wrd (get_inits in_file ch wrd) out_decs;
                make_productions in_file out_file out_decs out_type 
                                 nfirsts nchars
         else if mem wrd [`USEFUL`;`IGNORE`] then
            (emit_specials wrd (get_inits_specials in_file ch wrd) out_decs;
             make_productions in_file out_file out_decs out_type firsts chars)
         else
            (write_decs wrd out_decs out_type;
             write_final_all (MK_lambda wrd (process in_file wrd ch out_file))
                             out_file 0 `st`;
             if wrd = `MAIN_LOOP` then
                make_main_wrapper out_file
             else 
                ();
             make_productions in_file out_file out_decs 
                              out_type firsts chars);;

% ===================================================================== %
% get_ty: Make sure the user gave us some input for the output type of  %
%         the generated parser.                                         %
% ===================================================================== %

letrec get_ty lst flag =
    let ch = read_char `nil` in
        if ch = `\L` then
           if flag then
              failwith `Must have a type`
           else
              implode lst
        else get_ty (append lst [ch]) false;;

% ===================================================================== %
% parse: Top-level function for driving the generator.  It is the only  %
%        one exported from the section.                                 %
% ===================================================================== %

let parse () = 
    tty_write `Input file:  `;
    let in_file = terminal_read() in
      tty_write `Output file: `;
      let inf = (fst (open_file `in` in_file)) and 
          out_file = terminal_read() in
          let (outf,outf_decs) = open_file `out` out_file in
          tty_write `Output type: `;
          let out_type = get_ty [] true in
           make_productions inf outf outf_decs out_type false false;;

parse;;

end_section parser;;

let parse = it;;
