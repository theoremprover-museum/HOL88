% ===================================================================== %
% FILE		: ascii.ml						%
% DESCRIPTION   : Defines a conv for determining when two ascii values	%
%		  are equal.						%
%									%
% 		  Assumes that ascii.th is a parent of current thy.	%
%									%
% AUTHOR	: (c) T. Melham 1988					%
% DATE		: 87.05.30						%
% REVISED	: 90.10.27						%
% ===================================================================== %


% --------------------------------------------------------------------- %
% ascii_EQ_CONV: decision-procedure for equality of ascii constants.	%
% --------------------------------------------------------------------- %

let ascii_EQ_CONV = 
    let check = assert (\c.fst(dest_const c)=`ASCII`) in
    let ckargs = let T="T" and F="F" in assert (forall (\tm. tm=T or tm=F)) in
    let strip = snd o (check # ckargs) o strip_comb in
    let thm,vs = let th = theorem `ascii` `ASCII_11` in
                 let vs = fst(strip_forall(concl th)) in
                     fst(EQ_IMP_RULE (SPECL vs th)), vs in
    letrec fc th = 
       (let t,c = CONJ_PAIR th in ($=(dest_eq(concl t)) => fc c | t)) ? th in
    \tm. (let l,r = (strip # strip) (dest_eq tm) in
          if (l=r) then EQT_INTRO(REFL(rand tm)) else
	  let cntr = fc(UNDISCH (INST (combine(l@r,vs)) thm)) in
	  let fth = EQ_MP (bool_EQ_CONV (concl cntr)) cntr in
              EQF_INTRO (NOT_INTRO (DISCH tm fth))) ? 
	failwith `ascii_EQ_CONV`;;

% -------------------------------------------------- TESTS ---
timer true;;
ascii_EQ_CONV "ASCII T T T T T T T T = ASCII F F F F F F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII T T T T T T T T";;
 
ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T F F F F F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F T T T T T T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T F F F F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F T T T T T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T F F F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F T T T T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T T F F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F F T T T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T T T F F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F F F T T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T T T T F F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F F F F T T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T T T T T F";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F F F F F T";;

ascii_EQ_CONV "ASCII T T T T T T T T = ASCII T T T T T T T T";;
ascii_EQ_CONV "ASCII F F F F F F F F = ASCII F F F F F F F F";;

ascii_EQ_CONV "ASCII F T F T T F T F = ASCII F T F T T F T F";;
ascii_EQ_CONV "ASCII F T F T T F T F = ASCII F T F T T F T x";;
-------------------------------------------------------------------%
