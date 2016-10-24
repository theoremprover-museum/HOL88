%
Created by Mike Gordon during or before May 1990.

****************************************************************************
  define "!x1 ... xn. FOO x1 ... xn = ...";;

 is equivalent to

 let FOO =
  new_definition
   (`FOO`,
    "FOO x1 ... xn = ...");;
****************************************************************************
%

%----------------------------------------------------------------------------%
% The assignable variable def_buffer is a register for passing an argument   %
% to the function new_defn, which is called using let_before. This hack is   %
% necessary because only strings can be passed as parameters via calls of    %
% let_before (see DESCRIPTION).                                              %
%----------------------------------------------------------------------------%

letref def_buffer = "T";;

%----------------------------------------------------------------------------%
% Function invoked by let_before; gets argument through def_buffer.          %
%----------------------------------------------------------------------------%

let new_defn [name] = new_definition(name,def_buffer);;

%----------------------------------------------------------------------------%
% The function define extracts the name of the constant to be defined,       %
% then stashes the defining term in def_buffer,                              %
% then calls new_defn.                                                       %
%----------------------------------------------------------------------------%

let define t =
 let head =
  ((fst o dest_var o fst o strip_comb o lhs o snd o strip_forall) t
   ? failwith `bad term to define`)
 in
 def_buffer:=t;
 let_before(head,`new_defn`,[head]);;
