% link_to_hol.ml                                                              %
%-----------------------------------------------------------------------------%


%  Installs new printers for types, terms, and theorems into HOL.  %

top_print pp_print_type;;


top_print pp_print_term;;


top_print pp_print_thm;;


assignable_print_term := pp_print_term;;

%-----------------------------------------------------------------------------%
