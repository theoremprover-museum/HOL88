% ===================================================================== %
% FILE		: stringconv.ml						%
% DESCRIPTION   : define the axiom scheme for character strings.	%
%									%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 87.08.23						%
% REVISED	: 90.10.27						%
% ===================================================================== %

% ---------------------------------------------------------------------	%
% string_CONV  "defines" the infinite family of constants:		%
%									%
%	'a'  = STRING(ASCII F T T F F F F T)``				%
%	'ab' = STRING(ASCII F T T F F F F T)`b`				%
%									%
%	 ... etc							%
%									%
% The auxiliary function bits n m computes the representation in n 	%
% bits of m (MOD 2**n)							%
% --------------------------------------------------------------------- %

let string_CONV = 
    let T = "T" and F = "F" and A = "ASCII" in
    let STR = curry mk_comb "STRING" in
    let chkty = assert (\t.fst(dest_type t) = `string`) in
    letrec bits n m = 
       if (n=0) then [] else
          let hm = m/2 in (hm*2 = m => F | T) . bits (n-1) hm in
    \tm. (let str,ty = (I # chkty) (dest_const tm) in
          if (str = `\`\``) then fail else
          let q.h.t = explode str in 
          let code = rev (bits 8 (ascii_code h)) in
          let tm1 = STR (list_mk_comb(A,code)) in
          let def = mk_comb(tm1,mk_const(implode (q.t),ty)) in
              mk_thm([], mk_eq(tm,def))) ? 
          failwith `string_CONV`;;
