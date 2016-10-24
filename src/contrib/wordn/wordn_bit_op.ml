% ===================================================================== %
% FILE		: wordn_bit_op.ml					%
% DESCRIPTION   : functions for defining wordn bitwise operations.	%
%									%
% AUTHOR	: (c) W. Wong						%
% DATE		: 19 March 1992						%
% ===================================================================== %

% The following three definitions should be autoloaded	%
%let HD = definition `list` `HD`;;
let TL = definition `list` `TL`;;
%

% --------------------------------------------------------------------- %
% define_bit_op = - : (thm -> string -> string -> conv)			%
% define_bit_op = defthm name lcons f					%
% where defthm is the theorem returned by prove_function_defn_thm	%
%   name is a string under which the definition is stroed		%
%   lcons is the name for the new constant being defined		%
%   f is a term specifying the binary operator, it must be of type	%
%     ":bool -> bool"	    					%
%   	    	    	    	    					%
% define_bit_op word3_FNDEF `NOT3_DEF` `NOT3` "$~";;			%
% |- !w. NOT3 w = WORD3(MAP $~ (BITS3 w))				%
% --------------------------------------------------------------------- %
let define_bit_op =
    let is_digit s =    
    	(let code = ascii_code s in
        let code_0 = (ascii_code `0`) - 1 in
    	let code_9 = (ascii_code `9`) + 1 in
    	((code > code_0) & (code < code_9))) in
   \defthm name lcons f.
    (let var = (genvar o type_of) (fst(dest_forall(concl defthm))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPEC var defthm)) in
     let efn,(_,eqn) = (I # strip_forall) (dest_exists(concl exists)) in
     let wd = fst(dest_comb(snd(dest_comb (lhs eqn)))) in
     let wty = hd(snd (dest_type (type_of efn))) in
     let n = (implode(fst 
    	(partition is_digit (explode(fst(dest_type wty)))))) in
     let bs = mk_const((`BITS`^n), ":^wty -> (bool)list") in
     let op = mk_var(lcons, ":^wty -> ^wty") in
     let lh = mk_comb(op, "w:^wty") in
     let tm = mk_eq(lh, "(^wd) (MAP (^f) (^bs (w:^wty)))") in
     new_definition(name,tm)) ? failwith `define_bit_op` ;;

% --------------------------------------------------------------------- %
% define_bin_bit_op = - : (bool -> thm -> string -> string -> conv)	%
% define_bin_bit_op = iflag defthm name lcons f				%
%  where iflag indicates whether an infix is defined;			%
%   defthm is the theorem returned by prove_function_defn_thm		%
%   name is a string under which the definition is stroed		%
%   lcons is the name for the new constant being defined		%
%   f is a term specifying the binary operator, it must be of type	%
%     ":bool -> bool -> bool"	    					%
%   	    	    	    	    					%
% define_bin_bit_op true word3_FNDEF `OR3_DEF` `OR3` "$\/";;		%
% |- !w w'. w OR3 w' = WORD3(MAP2 $\/(BITS3 w)(BITS3 w'))		%
% --------------------------------------------------------------------- %

let define_bin_bit_op =
    let is_digit s =    
    	(let code = ascii_code s in
        let code_0 = (ascii_code `0`) - 1 in
    	let code_9 = (ascii_code `9`) + 1 in
    	((code > code_0) & (code < code_9))) in
   \iflag defthm name lcons f.
    (let var = (genvar o type_of) (fst(dest_forall(concl defthm))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPEC var defthm)) in
     let efn,(_,eqn) = (I # strip_forall) (dest_exists(concl exists)) in
     let wd = fst(dest_comb(snd(dest_comb (lhs eqn)))) in
     let wty = hd(snd (dest_type (type_of efn))) in
     let n = (implode(fst 
    	(partition is_digit (explode(fst(dest_type wty)))))) in
     let bs = mk_const((`BITS`^n), ":^wty -> (bool)list") in
     let deffun = (iflag => new_infix_definition | new_definition) in
     let op = mk_var(lcons, ":^wty -> ^wty -> ^wty") in
     let lh = mk_comb(mk_comb(op, "w:^wty"), "w':^wty") in
     let tm = mk_eq(lh, "(^wd) (MAP2 (^f) (^bs (w:^wty)) (^bs (w':^wty)))") in
     deffun(name,tm)) ? failwith `define_bin_bit_op` ;;

% --------------------------------------------------------------------- %
% prove_not_thm = - : (thm -> thm -> thm -> thm -> thm)			%
% prove_bot_thm tdefthm defthm ithm lthm    				%
% where tdefthm is the theorem returned by the type definition		%
%    defthm is the definition of the operator				%
%   ithm is a theorem stating the self-inversion of underlying operator	%
%   lthm is the theorem returned by prove_LENGTH_BITS_thm		%
%   	    	    	    	    					%
% prove_not_thm word3 NOT3_DEF ithm word3_LENGTH_BITS;;			%
% |- !w. NOT3(NOT3 w) = w   	    					%
% where ithm = |- !t. ~~t = t	    					%
% --------------------------------------------------------------------- %
let prove_not_thm =
    let thm = theorem `wordn_bitops` `MAP_INV` in
  \tdefthm defthm ithm lthm.
    (let rhs = rand(snd(strip_forall(concl defthm))) in
     let wd,mlst = (dest_comb rhs) in
     let (_,[op; bs]) = strip_comb mlst in
     let w =  (snd o dest_comb) bs in
     let th1,th1' = CONJ_PAIR tdefthm in
     let th2 = AP_TERM wd (SPEC bs (MATCH_MP (ISPEC op thm) ithm)) in
     let th3 = EQ_MP (SPEC mlst th1')
    	(TRANS (ISPECL[bs;op] LENGTH_MAP) (SPEC w lthm)) in
     let th4 = TRANS (SUBS [th3] (SPEC rhs defthm)) th2 in
     (GEN_ALL (SUBS[(SYM(SPEC w defthm));(SPEC w th1)] th4)))
    ? failwith `prove_not_thm`;;

% --------------------------------------------------------------------- %
% prove_sym_thm = - : (thm -> thm -> thm -> thm)			%
% prove_sym_thm defthm sthm lthm    					%
% where defthm is the definition of the operator			%
%   sthm is a theorem stating the symmetry of the underlying operator	%
%   lthm is the theorem returned by prove_LENGTH_BITS_thm		%
%   	    	    	    	    					%
% prove_sym_thm OR3_DEF DISJ_SYM word3_LENGTH_BITS;;			%
% |- !w w'. w OR3 w' = w' OR3 w	    					%
% --------------------------------------------------------------------- %
let prove_sym_thm =
    let thm = theorem `wordn_bitops` `MAP2_SYM` in
  \defthm sthm lthm.
    (let rhs = rand(snd(strip_forall(concl defthm))) in
     let wd,(_,[op; bs; bs']) = (I # strip_comb) (dest_comb rhs) in
     let [w;w'] = map (snd o dest_comb) [bs;bs'] in
     let th2 = SPECL [bs;bs'] (MATCH_MP (ISPEC op thm) sthm) in
     let th4 = SPEC w lthm and th4' = SPEC w' lthm in
     let th5 = MP th2 (TRANS th4 (SYM th4')) in
     let th6 = SYM (SPECL[w;w'] defthm) and th6' = SYM (SPECL[w';w] defthm) in
     (GEN_ALL (SUBS[th6;th6'] (AP_TERM wd th5)))) ? failwith `prove_sym_thm` ;;

% --------------------------------------------------------------------- %
% prove_assoc_thm = - : (thm -> thm -> thm -> thm -> thm)		%
% prove_assoc_thm tdefthm defthm sthm lthm    				%
% where tdefthm is the theorem returned by the type definition		%
%    defthm is the definition of the operator				%
%   sthm is a theorem stating the associativity of underlying operator	%
%   lthm is the theorem returned by prove_LENGTH_BITS_thm		%
%   	    	    	    	    					%
% prove_ASSOC_thm word3 OR3_DEF DISJ_ASSOC word3_LENGTH_BITS;;		%
% |- !w w' w''. w OR3 (w' OR3 w'') = (w OR3 w') OR3 w''			%
% --------------------------------------------------------------------- %
let prove_assoc_thm =
    let thm = theorem `wordn_bitops` `MAP2_ASSOC` in
    let thm2 = theorem `wordn_bitops` `MAP2_EQ_LENGTH` in
    let bitword lth eth op =
    	(SUBS[lth] (MATCH_MP (ISPEC op thm2) eth)) in
  \tdefthm defthm sthm lthm.
    (let lhs,rhs = dest_eq(snd(strip_forall(concl defthm))) in
     let bop = fst (strip_comb lhs) in
     let wd,(_,[op; bs; bs']) = (I # strip_comb) (dest_comb rhs) in
     let [w;w'] = map (snd o dest_comb) [bs;bs'] in
     let w'' = variant[w;w'] w in
     let bs'' = mk_comb(fst(dest_comb bs), w'') in
     let dth = GEN_ALL (fst(EQ_IMP_RULE (SPEC_ALL (CONJUNCT2 tdefthm)))) in
     let th2 = SPECL [bs;bs';bs''] (MATCH_MP (ISPEC op thm) sthm) in
     let [th4;th4';th4''] = map (\t. SPEC t lthm)[w; w'; w''] in
     let eqth = TRANS th4 (SYM th4') and eqth' = TRANS th4' (SYM th4'') in
     let th5 = AP_TERM wd (MP th2 (CONJ eqth eqth')) in
     let th6 = (SPECL[w;w'] defthm) and th6'' = SPECL[w';w''] defthm in
     let th7 = SUBS [th6''] (SPECL [w; "(^bop)(^w')(^w'')"] defthm) and
         th7' = SUBS [th6] (SPECL ["(^bop)(^w)(^w')"; w''] defthm) in
     let lm = MATCH_MP dth (bitword th4'' eqth' op) and
         lm' = MATCH_MP dth (bitword th4' eqth op) in
     let th8 = SYM (SUBS[lm] th7) and th8' = SYM (SUBS[lm'] th7') in
     (GEN_ALL (SUBS[(SYM th6);(SYM th6'')] (SUBS[th8;th8'] th5))));;

