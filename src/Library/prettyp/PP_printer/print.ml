% print.ml                                                                    %
%-----------------------------------------------------------------------------%

begin_section print;;

%  Function to write a list of strings to the terminal.  %

%  Each string is followed by a line-feed.  %

let display_strings sl =

   % : (string list -> void) %

   do (map (\s. tty_write (s ^ `\L`)) sl);;


%  Function to write a list of strings to a file.  %

%  Each string is followed by a line-feed.  %
%  The first argument is a file handle.     %

let output_strings port sl =

   % : (string -> string list -> void) %

   do (map (\s. write (port,(s ^ `\L`))) sl);;


%  Function to insert a list of strings into  %
%  the standard HOL pretty-printer buffer.    %

%  All except the last string are followed by a line break.  %

let insert_strings sl =

   % : (string list -> void) %

   letrec print_strings sl' =

      % : (string list -> void) %

      if (null sl')
      then ()
      else if (null (tl sl'))
           then print_string (hd sl')
           else do (print_string (hd sl');
                    print_break (0,0);
                    print_strings (tl sl'))

   in do (print_begin 0;
          print_strings sl;
          print_end ());;


%  Function to pretty-print a parse-tree to the terminal.  %

%  If a `DEBUG' parameter is present in the parameter list, the `debug'  %
%  argument to `print_box_to_strings' is set to true.                    %

let pretty_print m i prf context params pt =

   % : (int -> int -> print_rule_function -> string -> (string # int) list -> %
   %                                                      print_tree -> void) %

   (display_strings o (print_box_to_strings (can (assoc `DEBUG`) params) i))
      (print_tree_to_box m i prf context params pt);;


%  Function to pretty-print a parse-tree to a file.  %

%  If a `DEBUG' parameter is present in the parameter list, the `debug'  %
%  argument to `print_box_to_strings' is set to true.                    %
%                                                                        %
%  The first argument to pp_write is a file handle.                      %

let pp_write port m i prf context params pt =

   % : (string -> int -> int -> print_rule_function ->          %
   %       string -> (string # int) list -> print_tree -> void) %

   ((output_strings port) o
       (print_box_to_strings (can (assoc `DEBUG`) params) i))
      (print_tree_to_box m i prf context params pt);;


%  Function to pretty-print a parse-tree, inserting the output into the  %
%  standard HOL pretty-printer buffer.                                   %

%  If a `DEBUG' parameter is present in the parameter list, the `debug'    %
%  argument to `print_box_to_strings' is set to true.                      %

%  The width of the display is obtained from the parameter set by the HOL  %
%  function `set_margin'. The initial indentation is taken to be zero.     %

let pp prf context params pt =

   % : (print_rule_function -> string -> (string # int) list -> print_tree -> %
   %                                                                    void) %

   (insert_strings o (print_box_to_strings (can (assoc `DEBUG`) params) 0))
      (print_tree_to_box (get_margin ()) 0 prf context params pt);;

(pretty_print,pp_write,pp);;
end_section print;;
let (pretty_print,pp_write,pp) = it;;


%-----------------------------------------------------------------------------%
