%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        ml-curry.ml                                           %
%                                                                             %
%     DESCRIPTION:      Currying of Meta Language functions                   %
%                                                                             %
%                       These functions are more conveninent in curried form, %
%                       but it is difficult to define curried ML functions    %
%                       via "dml"                                             %
%                                                                             %
%     USES FILES:       hol-lcf lisp files                                    %
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
% The following definitions OVERWRITE the old meanings of the functions %
% they define, which were originally paired functions (list utilities)  %
% defined in f-lis.l							%
% --------------------------------------------------------------------- %

let mem x l = mem(x,l);;
let map f l = map(f,l);;
let exists p l = exists(p,l);;
let forall p l = forall(p,l);;
let find p l = find(p,l);;
let tryfind f l = tryfind(f,l);;
let filter p l = filter(p,l);;
let mapfilter f l = mapfilter(f,l);;

let rev_itlist f l x = rev_itlist(f,l,x);;


% --------------------------------------------------------------------- %
% The following definitions OVERWRITE the old meanings of the functions %
% they define, which were originally paired functions (obj utilities)   %
% defined in f-obj.l							%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% obj primititives deleted [TFM 90.09.09]                               %
% 									%
% let set_left x y = set_left(x,y)                       		%
% and set_right x y = set_right(x,y)					%
% and eq x y = eq(x,y)							%
% and cons x y = cons(x,y);;						%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Added TFM/MJCG 88.10.07						%
% 									%
% This was added to simplify the makefile for HOL. The boolean flag 	%
% `compiling' is true during compilation and false otherwise. The 	%
% definitions below overwrite the old definitions so that the flag 	%
% `compiling' is maintained.						% 
% --------------------------------------------------------------------- %

letref compiling = false;;

letref compiling_stack = ([]:bool list);;
	
let load p = (compiling_stack := compiling . compiling_stack;
	      compiling := false;
	      load p;
	      compiling := hd compiling_stack;
	      compiling_stack := tl compiling_stack;
	      ());;

let compile p = (compiling_stack := compiling . compiling_stack;
	         compiling := true;
	         compile p;
	         compiling := hd compiling_stack;
	         compiling_stack := tl compiling_stack;
  	         ());;
