% PP_to_ML.ml                                                                 %
%-----------------------------------------------------------------------------%


%  Main pretty-printer compiling function.  %

%  If first argument is true, the output is appended to the output file.      %
%  Input filename must end in `.pp', but the `.pp' may be omitted from the    %
%  argument to this function. If output argument is a null string, the input  %
%  filename is used with the `.pp' replaced by `_pp.ml'.                      %

let PP_to_ML app input output =

   % : (bool -> string -> string -> void) %

   let input' =
      if (((substr ((strlen input) - 3) 3 input) = `.pp`) ? false)
      then (substr 0 ((strlen input) - 3) input)
      else input
   in  let infile = openi (input' ^ `.pp`)
       and output' = if (output = ``)
                     then (input' ^ `_pp.ml`)
                     else output
       in  let outfile = if app
                         then append_openw output'
                         else openw output'
           in  do (write (outfile,(`% ` ^ output' ^
                                   (string_copies ` ` (76-(strlen output'))) ^
                                   `%`));
                   write (outfile,`\L`);
                   write (outfile,(`%` ^ (string_copies `-` 77) ^ `%`));
                   write (outfile,`\L`);
                   write (outfile,`\L`);
                   generate_ML write outfile 
                      (fst (convert_PP (read_PP read infile,[])));
                   write (outfile,`\L`);
                   write (outfile,(`%` ^ (string_copies `-` 77) ^ `%`));
                   write (outfile,`\L`);
                   close outfile;
                   close infile
                  );;


%-----------------------------------------------------------------------------%
