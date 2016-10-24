%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        genfns.ml                                             %
%                                                                             %
%     DESCRIPTION:      Some general purpose ML functions                     %
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

letrec map2 f (l1,l2) =
   if (null l1)
   then if (null l2)
        then []
        else failwith `map2`
   else if (null l2)
        then failwith `map2`
        else f (hd l1,hd l2) . map2 f (tl l1,tl l2);;

letrec itlist2 f (l1,l2) x =
   if (null l1)
   then if (null l2)
        then x
        else failwith `itlist2`
   else if (null l2)
        then failwith `itlist2`
        else f (hd l1,hd l2) (itlist2 f (tl l1,tl l2) x);;

% --------------------------------------------------------------------- %
% Used only once, so replaced by \(x,y).(y,x)		[TFM 90.06.01] 	%
% let flip(x,y) = (y,x);;						%
% --------------------------------------------------------------------- %

let set_equal s1 s2 = subtract s1 s2 = [] & subtract s2 s1 = [];;

letrec el i l = 
 (if null l or i<1 then fail
  if i=1           then hd l
                   else el (i-1) (tl l)
 ) ? failwith `el`;;

% --------------------------------------------------------------------- %
% functions:								%
%									%
%  seg:(int#int)->(*)list->(*)list 					%
%  word_seg:(int#int)->(*)list->(*)list 				% 
%  word_el:int->(*)list->*						%
%  truncate:int->(*)list->(*)list					%
%									%
% moved to eval library					[TFM 90.06.01]	%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% The version of words used below uses space and <CR> as separators	%
% --------------------------------------------------------------------- %
let word_separators = [` `;
`
`];;

let words string =
    snd (itlist (\ch (chs,tokl). 
	     if mem ch word_separators then
		if null chs then [],tokl
		else [], (implode chs . tokl)
	     else (ch.chs), tokl)
    (` ` . explode string)
    ([],[]));;

let maptok f = (map f) o words;;

% make_set in ml/lis.ml has same functionality as setify, but a better	%
% definition, so definition below commented-out.  [RJB 90.10.20]	%
%									%
% setify l removes repeated elements from l 				%
%									%
% letrec setify l =							%
%  if null l            then []						%
%  if mem (hd l) (tl l) then setify(tl l)				%
%                       else hd l.(setify(tl l));;			%

let uncurry f (x,y) = f x y;;
