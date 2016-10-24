%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        lis.ml                                                %
%                                                                             %
%     DESCRIPTION:      List-processing functions for ML.  Many of these      %
%                       functions could be coded in Lisp for speed.           %
%                                                                             %
%     USES FILES:       ml-curry.ml                                           %
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

% let nil = [];;        [ Deleted: TFM 90.05.31]                        %

let append x y = x @ y;;

%genmem has been deleted;  if p is a curried predicate,
  then you can write "exists (p x)"
else write "exists (curry p x)"
%


let itlist f l x = rev_itlist f (rev l) x;;

% [x1; ...; xn]   --->   (ff x1 ... (ff (xn-1) xn)...)   for n>0 %
let end_itlist ff l =
    if null l then failwith `end_itlist`
    else (let last.rest = rev l in
          rev_itlist ff rest last);;

% Ad hoc and only used once in HOL sources, so deleted. [TFM 90.06.01]  %
% let eqfst x (y,z) = (x=y)                                             %
% and eqsnd x (y,z) = (x=z);;                                           %

% Failure strings added [TFM 90.12.01]                                  %

let assoc x l = find (\(y,z). y=x) l ? failwith `assoc`;;
let rev_assoc x l = find (\(y,z). z=x) l ? failwith `rev_assoc`;;

let intersect l1 l2 = filter (\x. mem x l2) l1 ;;
let subtract l1 l2 = filter (\x. not mem x l2) l1 ;;
let union l1 l2 = l1 @ (subtract l2 l1) ;;

% `make_set' renamed `setify' [RJB 90.10.20].                           %
%                                                                       %
% make a list into a set, stripping out duplicate elements              %

let setify l =
    itlist (\a s. if mem a s then s else a.s) l [];;


letrec split l =
    if null l then ([],[])
    else
      (let (x1,x2) .l' = l  in
       let l1',l2' = split l' in (x1.l1', x2.l2'));;


letrec combine(l1,l2) =
    if null l1  &  null l2  then []
    else
      ((hd l1, hd l2) . combine(tl l1, tl l2)
       ? failwith `combine`);;



ml_paired_infix `com`;;
let $com = combine;;



%Check if the elements of `l` are all distinct%
letrec distinct l =
    (null l) or
    (not (mem (hd l) (tl l)) & distinct (tl l));;



% chop_list n [e1; ...; en; e[n+1]; ... ; e[n+m]   --->
        [e1; ...; en] , [e[n+1]; ...; e[n+m]]
%
letrec chop_list n l =
    if  n=0  then  ([],l)
    else  (let m,l' = chop_list (n-1) (tl l) in  hd l . m , l')
    ? failwith `chop_list`;;


% --------------------------------------------------------------------- %
% Functions last and butlast added.                     [RJB 90.10.20]  %
% --------------------------------------------------------------------- %

% last [x1;...;xn]   --->   xn %

letrec last l = last (tl l) ? hd l ? failwith `last`;;

% butlast [x1;...x(n-1);xn]   --->   [x1;...;x(n-1)] %

letrec butlast l =
 if null (tl l) then [] else (hd l).(butlast(tl l)) ? failwith `butlast`;;


% Occurrences of rotate_left and rotate_right replaced  %
% by calls to hd, tl, @, last and butlast.              %
% Commented-out  [RJB 90.10.20]                         %
%                                                       %
% let rotate_left (a.l) = l @ [a]                       %
% and rotate_right l =                                  %
%     let ra.rl = rev l in ra . (rev rl);;              %



% [[1;2;3]; [4;5;6]; [7;8;9]]   --->   [1; 5; 9]        %
% Not used anywhere: commented-out  [TFM 90.04.21]      %
%                                                       %
% letrec diagonal ll =                                  %
%    if null ll then []                                 %
%    else hd (hd ll) . (diagonal (map tl (tl ll)));;    %




% [x1; ...; x(m+n)]   --->  [y1; ...; ym], [z1; ...; zn]
where the y's are all x's that satisfy p, the z's all other x's
%
let partition p l =
    itlist (\a (yes,no). if p a then (a.yes),no else yes, (a.no))
    l ([],[]);;


%make the list [x; x; ...; x] of length n%
letrec replicate x n =
    if n<0 then failwith `replicate`
    else if n=0 then []
    else x . (replicate x (n-1));;


% make the list [from; from+1; ...; to]                                 %
% Made local where actually used: [TFM 90.06.25]                        %
% letrec upto from to =                                                 %
%    if from>to then []                                                 %
%    else from . (upto (from+1) to);;                                   %

%--------------------------------------------------------------------%
% sort - Quicksorts a list according to a given "less-than" operator %
% [JRH 91.07.17]                                                     %
%--------------------------------------------------------------------%

letrec sort cmp lis =
  let curry f x y = f (x,y) in
  if null lis then []
  else let piv.rest = lis in
  let (r,l) = partition (curry cmp piv) rest in
  (sort cmp l)@(piv.(sort cmp r));;

%--------------------------------------------------------------------%
% splitp --- splits a list into two according to a given predicate   %
% [WW 93.05.19]        	    	    				     %
%--------------------------------------------------------------------%

 
let splitp pred l = 
    	letrec spl lst = 
    	    if null lst then ([], [])
            else let (h.rest) = lst in
    	    	if pred h then ([], lst)
        	    else let (p,s) = spl rest in
    	    	((h.p),s)
    	in spl l ;;

%-----------------------------------------------------------------------%
% remove x satisfying p from l.... giving x and the thing and rest of l	%
% Moved here by WW 24-July-93                                           %
%-----------------------------------------------------------------------%
letrec remove p l = 
       if (p(hd l)) then ((hd l), (tl l)) else
        let (p', l') = remove p (tl l) in
       (p', ((\r. ((hd l) . r)) l')) ;;
