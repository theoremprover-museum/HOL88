%****************************************************************************%
% Patch to correct a bug in preterm handling in Common Lisp versions of      %
% HOL88.2.01                                                                 %
%****************************************************************************%

if version() < 202 
then (print_newline();
      print_string `-------------------------------------------------------`;
      print_newline();
      lisp `(load '|lisp/f-gp|)`;
      print_string `Version 2.02 f-gp     loaded to fix preterm_handler bug`;
      print_newline();
      lisp `(load '|lisp/f-parser|)`;
      print_string `Version 2.02 f-parser loaded to fix preterm_handler bug`;
      print_newline();
      lisp `(load '|lisp/f-parsml|)`;
      print_string `Version 2.02 f-parsml loaded to fix preterm_handler bug`;
      print_newline();
      lisp `(load '|lisp/hol-pars|)`;
      print_string `Version 2.02 hol-pars loaded to fix preterm_handler bug`;
      print_newline();
      print_string `-------------------------------------------------------`;
      print_newline());;


