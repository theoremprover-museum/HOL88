% lex.ml                                                                      %
%-----------------------------------------------------------------------------%


%  Function to copy a number of characters from an input port to an output  %
%  port.                                                                    %

%  The input port is specified as a function and a port name. When the e      %
%  function is applied to the port name, a character is obtained. The output  %
%  port is specified as a function which given a character writes it to some  %
%  destination. If the input is exhausted before the specified number of      %
%  characters have been copied, the copying terminates without error.         %

letrec copy_chars n inf (inport:string) (out:string -> void) =

   % : (int -> (string -> string) -> string -> (string -> void) -> void) %

   if (n < 1)
   then ()
   else let char = inf inport
        in  if (char = `nil`)
            then ()
            else do (out char; copy_chars (n - 1) inf inport out);;


%  Datatype for lexical objects.  %

%  The kinds of object are: special symbols, numbers, identifiers, and    %
%  blocks of text. Lex_block((begin,end),sl) is obtained from a block of  %
%  text beginning with the value of `begin' and ending with the value of  %
%  `end'. The text in between is split on line-breaks into a list of      %
%  strings, sl.                                                           %

type lex_symb = Lex_spec of string
              | Lex_num of string
              | Lex_id of string
              | Lex_block of (string # string) # string list;;

begin_section lex;;

%  Functions for determining classification of a character.  %

let is_lex_char (l,c,u) =

   % : (string # string # string -> bool) %

   not (((ascii_code c) < (ascii_code l)) or
           ((ascii_code c) > (ascii_code u)));;


let is_lex_ucase c = is_lex_char (`A`,c,`Z`);;

let is_lex_lcase c = is_lex_char (`a`,c,`z`);;

let is_lex_letter c = (is_lex_ucase c) or (is_lex_lcase c);;

let is_lex_digit c = is_lex_char (`0`,c,`9`);;

let is_lex_underscore c = mem c [`_`];;

let is_lex_eof c = mem c [`nil`];;

let is_lex_eol c = mem c [`\R`;`\L`;`\F`];;

let is_lex_space c = mem c [`\0`;`\1`;`\2`;`\3`;`\4`;`\5`;`\6`;`\7`;`\8`;`\9`;
                            ` `;`\S`;`\T`];;


%  Error handler for lexical errors.  %

let lex_error f port exp got =

   % : ((string -> string) -> string -> string -> string -> ?) %

   tty_write (`Syntax error: expected `^exp^`, got `^got^` ...`^`\L`);
   copy_chars 200 f port tty_write;
   tty_write `\L`;
   tty_write (`... parse failed.`^`\L`);
   failwith `lex_error`;;


%  Function to read a character from an input port.  %

let read_char f port =

   % : ((string -> string) -> string -> string) %

   let c = f port
   in  if (is_lex_eof c)
       then failwith `read_char -- input exhausted`
       else c;;


%  Function to read a number.  %

%  Requires first character of input as an argument. Returns the first        %
%  unused character. This allows the necessary lookahead. Builds digits into  %
%  a string until no more are encountered.                                    %

let read_number f port c =

   % : ((string -> string) -> string -> string -> (lex_symb # string)) %

   letrec scan f port (s,c') =

      % : ((string -> string) -> string -> (string # string) ->    %
      %                                         (string # string)) %

      if (is_lex_digit c')
      then scan f port ((s ^ c'),(read_char f port))
      else (s,c')

   in let (s,c') = scan f port (``,c)
      in  (Lex_num s,c');;


%  Function to read an identifier.  %

%  Identifiers can contain letters, digits and underscores, but underscores  %
%  must be followed by a letter or a digit. The function given allows        %
%  identifiers to begin with a number or an underscore. This is not correct  %
%  but since the function will only ever be called when a letter is          %
%  encountered, there should be no problem.                                  %

let read_identifier f port c =

   % : ((string -> string) -> string -> string -> (lex_symb # string)) %

   letrec scan f port (s,c') =

      % : ((string -> string) -> string -> (string # string) ->    %
      %                                         (string # string)) %

      if (is_lex_underscore c') then
         (let c'' = read_char f port
          in  if ((is_lex_letter c'') or (is_lex_digit c''))
              then scan f port ((s ^ c' ^ c''),(read_char f port))
              else lex_error f port `letter or digit` c'')
      if (is_lex_letter c') then
         (scan f port ((s ^ c'),(read_char f port)))
      if (is_lex_digit c') then
         (scan f port ((s ^ c'),(read_char f port)))
      else (s,c')

   in let (s,c') = scan f port (``,c)
      in  (Lex_id s,c');;


%  Function to read a block of text.  %

%  This function expects to be called with the character used to introduce    %
%  the block as its last argument. It discards this character because it is   %
%  not to be included in the list of strings representing the block of text.  %

%  On encountering the terminating character, the function reads the next     %
%  character to check if the end character has been doubled-up. If it has,    %
%  a single end character is included in the string list, and the scan        %
%  continues. Otherwise the scan ends and the list of strings is reversed,    %
%  since it has been built in reverse order.                                  %

%  If the start character is encountered doubled-up, a single start char. is  %
%  included in the list of strings. If the start char. is not doubled-up, an  %
%  error occurs.                                                              %

%  If an end-of-line occurs, a new string is begun.                           %

let read_block f port (start,end) (c:string) =

   % : ((string -> string) -> string -> (string # string) -> string ->    %
   %                                                 (lex_symb # string)) %

   letrec scan f port (start,end) (sl,s,c') =

      % : ((string -> string) -> string -> (string # string) ->          %
      %       (string list # string # string) -> (string list # string)) %

      if (c' = end) then      % Note : order important if start = end %
         (let c'' = read_char f port
          in  if (c'' = end)
              then scan f port (start,end) (sl,(s ^ end),(read_char f port))
              else (rev (s.sl),c''))
      if (c' = start) then
         (let c'' = read_char f port
          in  if (c'' = start)
              then scan f port (start,end) (sl,(s ^ start),(read_char f port))
              else lex_error f port (start ^ start) start)
      if (is_lex_eol c') then
         (scan f port (start,end) ((s.sl),``,(read_char f port)))
      else scan f port (start,end) (sl,(s ^ c'),(read_char f port))

   in let (sl,c') = scan f port (start,end) ([],``,(read_char f port))
      in  (Lex_block ((start,end),sl),c');;


%  Function to read a special symbol.  %

%  Note: Special symbols must not contain letters, digits, underscore or any  %
%  character occuring in the argument `quotes' of the function `read_symb'.   %

%  The function builds up a string. Initially this is null. It tries adding   %
%  the next character of the input to the end of the string. If the result    %
%  is one of the specified special symbols, or the beginnings of one, the     %
%  function tries to add another character. If not, the old string is tested  %
%  to see if it is a special symbol. If it is not, or if no characters could  %
%  be added, an error occurs. This process allows one special symbol to be a  %
%  substring of another. The function reads the larger one if it can.         %

let read_special f port specials c =

   % : ((string -> string) -> string -> string list -> string ->    %
   %                                           (lex_symb # string)) %

   letrec scan f port specials (s,c') =

      % : ((string -> string) -> string -> string list ->    %
      %              (string # string) -> (string # string)) %

      let s' = s ^ c'
      in  if (exists (\x. (s' = (substr 0 (strlen s') x)) ? false) specials)
          then scan f port specials (s',(read_char f port))
          else if (mem s specials)
               then (s,c')
               else (``,s')

   in let (s,c') = scan f port specials (``,c)
      in  if (s = ``)
          then lex_error f port `a special symbol` c'
          else (Lex_spec s,c');;


%  Function to read a lexical object.  %

%  Spaces and line-breaks are ignored. If a digit is encountered, a number   %
%  is read. If a letter is encountered, an identifier is read. The           %
%  identifier is made into a special symbol if it is listed as a keyword.    %
%  If the next character is listed as the start of a block, the appropriate  %
%  kind of block is read. Failing all these, an attempt is made to read a    %
%  special symbol.                                                           %

letrec read_symb f (port:string) quotes keywords specials c =

   % : ((string -> string) -> string -> (string # string) list ->      %
   %      string list -> string list -> string -> (lex_symb # string)) %

   if ((is_lex_space c) or (is_lex_eol c)) then
      (read_symb f port quotes keywords specials (read_char f port))
   if (is_lex_digit c) then
      (read_number f port c)
   if (is_lex_letter c) then
      (case (read_identifier f port c)
       of (Lex_id s,c') .
             (if (mem s keywords)
              then (Lex_spec s,c')
              else (Lex_id s,c'))
        | (_) . failwith `read_symb -- system error`)
   else (  (let p = assoc c quotes
            in  read_block f port p c)
        ?? [`assoc`] (read_special f port specials c)
        );;

read_symb;;
end_section lex;;
let read_symb = it;;

%-----------------------------------------------------------------------------%
