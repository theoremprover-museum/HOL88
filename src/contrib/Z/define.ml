
%****************************************************************************%
% define "!x1 ... xn. FOO x1 ... xn = ...";;                                 %
%                                                                            %
% is equivalent to                                                           %
%                                                                            %
% let FOO =                                                                  %
%  new_definition                                                            %
%   (`FOO`,                                                                  %
%    "FOO x1 ... xn = ...");;                                                %
%****************************************************************************%

%----------------------------------------------------------------------------%
% The assignable variables term_buffer and fun_buffer are registers for      %
% passing arguments to the function make_new_definition. This function       %
% is called by let_before. The buffers are a hack to get around the fact     %
% that only strings can be passed as arguments to make_new_definition        %
% when it is invoked using let_before. See DESCRIPTION for details.          %
%----------------------------------------------------------------------------%

letref term_buffer = "T"
and    fun_buffer  = new_definition;;

%----------------------------------------------------------------------------%
% Functions invoked by let_before; gets argument through term_buffer.        %
%----------------------------------------------------------------------------%

let make_new_definition [name] = fun_buffer(name,term_buffer);;

%----------------------------------------------------------------------------%
% The function define extracts the name of the constant to be defined,       %
% then stashes the defining term in term_buffer,                             %
% then calls make_new_definition.                                            %
%----------------------------------------------------------------------------%

let define_fun t =
 let head = 
  ((fst o dest_var o fst o strip_comb o lhs o snd o strip_forall o 
    hd o conjuncts o snd o strip_forall) t
   ? failwith `bad term to define`)
 in
 term_buffer:=t;
 let_before(head,`make_new_definition`,[head]);;

let define t         = fun_buffer := new_definition;         define_fun t
and define_infix t   = fun_buffer := new_infix_definition;   define_fun t
and define_binder t  = fun_buffer := new_binder_definition;  define_fun t
and rec_define thm t =
 fun_buffer :=  uncurry(new_recursive_definition false thm); define_fun t;;

%============================================================================%
% define_structure `foo = ...` expands to                                    %
%                                                                            %
%    let foo = define_type `foo` `foo = ...`;;                               %
%                                                                            %
%============================================================================%

let make_new_structure_definition [name;def] = define_type name def;;

let define_structure s = 
 let name = hd(words s)
 in
 let_before(name, `make_new_structure_definition`, [name;s]);;

%----------------------------------------------------------------------------%
% "[t1;...;tn] |-? t"  --->  (["t1";...;"tn"],"t")                           %
%----------------------------------------------------------------------------%

let dest_Z_goal tm =
 (let op,[t1;t2] = strip_comb tm
  in
  if is_const op & (fst(dest_const op) = `|-?`) & is_list t1
  then (fst(dest_list t1),t2)
  else fail
 ) ? failwith `dest_Z_goal`;;

let is_Z_goal = can dest_Z_goal;;

let prove_thm(name,term,tac) =
 let th = 
  (if is_Z_goal term then TAC_PROOF(dest_Z_goal term,tac) else PROVE(term,tac))
 in
 save_thm(name,th) 
  ? (print_newline();
     print_string(`deleting previous version of `^name^`:`);
     print_newline();
     print_thm(delete_thm `-` name); 
     print_newline();
     print_newline();
     save_thm(name,th));;

let g tm = set_goal(dest_Z_goal tm) ? set_goal([],tm);;


%============================================================================%
% prove_theorem(`name`,term,tactic) expands to                               %
%                                                                            %
%    let name =                                                              %
%     prove_thm                                                              %
%      (`name`,                                                              %
%       term,                                                                %
%       tactic);;                                                            %
%                                                                            %
%============================================================================%

letref prove_theorem_buffer = (`initial-name`,"T",ALL_TAC);;

let make_prove_theorem [] = prove_thm prove_theorem_buffer;;

let prove_theorem(name,term,tac) = 
 prove_theorem_buffer := (name,term,tac);
 let_before(name, `make_prove_theorem`, []);;






