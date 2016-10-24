%-----------------------------------------------------------------------%
% use_wordn : int -> (thm)list	    					%
% use_wordn n performs the following actions:				%
%  1) defining the type :wordn	    					%
%  2) proving the following theorems:					%
%   	wordn_BITS_11, wordn_BITS_onto,					%
%   	wordn_WORD_11, wordn_WORD_onto,					%
%   	wordn_LENGTH_BITS, wordn_FNDEF,					%
%   	wordn_INDUCT, wordn_CASES   					%
%     All theorems are stored in the current theory and are returned in %
%     in a list.    	    	    					%
%-----------------------------------------------------------------------%

let use_wordn n = 
    let tyname = (`word` ^ (string_of_int n)) in
    let w_thm = define_wordn_type tyname n in
    let f_thm = prove_function_defn_thm w_thm in
    let i_thm = prove_wordn_induction_thm f_thm in
    let c_thm = prove_wordn_cases_thm i_thm in
    (w_thm . (map (\ (s,th). save_thm((tyname^s),th))
    	[(`_BITS_11`, prove_BITS_one_one w_thm);
    	 (`_BITS_onto`, prove_BITS_onto w_thm);
    	 (`_WORD_11`, prove_WORD_one_one w_thm);
    	 (`_WORD_onto`, prove_WORD_onto w_thm);
    	 (`_LENGTH_BITS`, prove_LENGTH_BITS_thm w_thm);
    	 (`_FNDEF`, f_thm); (`_INDUCT`, i_thm); (`_CASES`, c_thm)]));;

% --------------------------------------------------------------------- %
% define_wordn_bit_ops : thm -> int -> (thm) list			%
% define_wordn_bit_ops defthm n	    					%
% where defthm is the theorem returned by prove_function_defn_thm	%
% and n is the number of bits.	    					%
% It defines the following bitwise operators for the given word length: %
%   NOTn --- toggles the bits	    					%
%   ANDn --- bitwise AND    	    					%
%   ORn --- bitwise OR    	    					%
%   XORn --- bitwise XOR    	    					%
% The definitions are stored in the current theory under the names	%
%   NOTn_DEF, ANDn_DEF, ORn_DEF and XORn_DEF				%
% and are returned in a list as  the value of this function.		%
% --------------------------------------------------------------------- %

let define_wordn_bit_ops defthm n =
    let nstr = string_of_int n in
    let def_binop (nm, op) =
    	(define_bin_bit_op true defthm (nm^nstr^`_DEF`) (nm^nstr) op) in
    (define_bit_op defthm (`NOT`^nstr^`_DEF`) (`NOT`^nstr) "$~") .
    (map def_binop [(`AND`,"$/\"); (`OR`,"$\/");
    	    	 (`XOR`, "(\(x:bool) x'. ~(x=x'))")]) 
    ?\st  failwith `define_wordn_bit_ops: ` ^ st;;

% --------------------------------------------------------------------- %
% prove_bit_op_thms : (int -> thm list)	n				%
% proves several basic theorems about the bitwise operators of :wordn	%
% and stores them in the current theory under the names as shown below.	%
% The theorems are returned in a list in the order as shown below.	%
% e.g. prove_bit_op_thms 3 --->	    					%
% [ NOT3    	|- !w. NOT3(NOT3 w) = w;				%
%   AND3_SYM	|- !w1 w2. w1 AND3 w2 = w2 AND3 w1;			%
%   OR3_SYM 	|- !w1 w2. w1 OR3 w2 = w2 OR3 w1;			%
%   XOR3_SYM	|- !w1 w2. w1 XOR3 w2 = w2 XOR3 w1;			%
%   AND3_ASSOC	|- !w1 w2 w3. w1 AND3 (w2 AND3 w3) = (w1 AND3 w2) AND3 w3;%
%   OR3_ASSOC	|- !w1 w2 w3. w1 OR3 (w2 OR3 w3) = (w1 OR3 w2) OR3 w3;	%
%   XOR3_ASSOC	|- !w1 w2 w3. w1 XOR3 (w2 XOR3 w3) = (w1 XOR3 w2) XOR3 w3]%
% --------------------------------------------------------------------- %
let prove_bit_op_thms n =
    let n_str = string_of_int n in
    let tdefthm = definition `-` (`word`^n_str) in
    let lthm = theorem `-` (`word`^n_str^`_LENGTH_BITS`) in
    let dth = definition `-` (`NOT`^n_str^`_DEF`) in
    let nth = CONJUNCT1 NOT_CLAUSES in
    let prove_it op =
    	let dthm = definition `-` (op^n_str^`_DEF`) in
    	let sthm = if (op = `AND`) then CONJ_SYM
    	    	else if (op = `OR`) then DISJ_SYM
    	    	else if (op = `XOR`) then XOR_SYM
    	    	else fail in
    	let athm = if (op = `AND`) then CONJ_ASSOC
    	    	else if (op = `OR`) then DISJ_ASSOC
    	    	else if (op = `XOR`) then XOR_ASSOC
    	    	else fail in
    	[save_thm((op^n_str^`_SYM`),(prove_sym_thm dthm sthm lthm)); 
    	 save_thm((op^n_str^`_ASSOC`),(prove_assoc_thm tdefthm dthm athm lthm))] in
    (save_thm((`NOT`^n_str), (prove_not_thm tdefthm dth nth lthm)) .
    (flat (map prove_it [`AND`; `OR`; `XOR`])));;

let wordn_bit_ops defthm n =
    (define_wordn_bit_ops defthm n) @ (prove_bit_op_thms n);;

% --------------------------------------------------------------------- %
% wordn_partition : int -> int -> thm list				%
%  wordn_partition m n defines two constants:				%
%   JOIN_m_n : (wordm # wordn) -> wordl					%
%   SPLIT_m_n : wordl -> (wordm # wordn) where l = m + n		%
% The definitions are stored under the names JOIN_m_n_DEF, SPLIT_m_n_DEF%
% Three theorems are derived which are stored under the names:		%
%  JOIN_m_n, SPLIT_m_n, and PARTION_m_n					%
% They are also returned as the function value.				%
% --------------------------------------------------------------------- %

let wordn_partition =
    let get_cthm = \s. theorem `-` (`word`^(string_of_int s)^`_CASES`) in
    let get_bthm = \s. prove_BITS_WORD 
    	(definition `-` (`word`^(string_of_int s))) in
  \m n.
    let l = m + n in
    let bthms = map get_bthm [m;n;l] and cthms = map get_cthm [m;n;l] in
    let mnstr = ((string_of_int m) ^ `_` ^ (string_of_int n)) in
    let jstr = (`JOIN_`^mnstr) and sstr = (`SPLIT_`^mnstr) in
    let jdef = (jstr^`_DEF`) and sdef = (sstr^`_DEF`) in
    let (jthm,sthm) = define_wordn_partition (jdef,sdef) bthms in
    let pthm = prove_partition_thm (jthm,sthm) cthms in
    map save_thm [(jstr, jthm); (sstr,sthm); ((`PARTITION_`^mnstr),pthm)];;
    	

let wordn_word_val defthm n =
    let nstr = string_of_int n in
    let vstr = (`NVAL`^nstr) and wstr = (`NWORD`^nstr) in
    let [vdef;wdef] = define_word_val defthm
    	(vstr,(vstr^`_DEF`)) (wstr,(wstr^`_DEF`)) in
    ([vdef; wdef; (save_thm((`WORD_VAL_`^nstr),
    	prove_word_val defthm vdef wdef))]);;
