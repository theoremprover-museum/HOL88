loadf`wordn`;;

timer true;;

new_theory `test2`;;

let word3 = define_wordn_type `word3` 3;;

let word3_BITS_11 = prove_BITS_one_one word3;;
let word3_BITS_onto = prove_BITS_onto word3;;
let word3_WORD_11 = prove_WORD_one_one word3;;
let word3_WORD_onto = prove_WORD_onto word3;;

let word3_LENGTH_BITS = prove_LENGTH_BITS_thm word3;;
let word3_FNDEF = prove_function_defn_thm word3;;

let word3_INDUCT = prove_wordn_induction_thm word3_FNDEF;;
let word3_CASES = prove_wordn_cases_thm word3_INDUCT;;

let MID_DEF = new_wordn_definition false word3_FNDEF `MID_DEF`
    "MID (WORD3[b0;b1;b2]) = b1";;

let word3_3 = wordn_CONV "#011";;

let word3_CCASES = prove_wordn_const_cases word3_CASES;;

let word3_EQ = wordn_EQ_CONV word3 "#010 = #011";;

let word3_BITS_WORD = prove_BITS_WORD word3;;

let NOT3_DEF = define_bit_op word3_FNDEF `NOT3_DEF` `NOT3`  "$~";;

let ithm = CONJUNCT1 NOT_CLAUSES;;
let NOT3 = prove_not_thm word3 NOT3_DEF ithm word3_LENGTH_BITS;;

let AND3_DEF = define_bin_bit_op true word3_FNDEF `AND3_DEF` `AND3`  "$/\";;

let AND3_SYM = prove_sym_thm AND3_DEF CONJ_SYM word3_LENGTH_BITS;;

let AND3_ASSOC = prove_assoc_thm word3 AND3_DEF CONJ_ASSOC word3_LENGTH_BITS;;


let word5 = define_wordn_type `word5` 5;;
let word5_FNDEF = prove_function_defn_thm word5;;
let word5_INDUCT = prove_wordn_induction_thm word5_FNDEF;;
let word5_CASES = prove_wordn_cases_thm word5_INDUCT;;
let word5_BITS_WORD = prove_BITS_WORD word5;;

let word8 = define_wordn_type `word8` 8;;
let word8_FNDEF = prove_function_defn_thm word8;;
let word8_INDUCT = prove_wordn_induction_thm word8_FNDEF;;
let word8_CASES = prove_wordn_cases_thm word8_INDUCT;;
let word8_BITS_WORD = prove_BITS_WORD word8;;

let JOIN_3_5_DEF,SPLIT_3_5_DEF =
    define_word_partition (`JOIN_3_5`,`SPLIT_3_5`)
    	[word3_BITS_WORD; word5_BITS_WORD; word8_BITS_WORD];;

let PARTION_3_5 = prove_partition_thm (JOIN_3_5_DEF,SPLIT_3_5_DEF)
    	[word3_CASES; word5_CASES; word8_CASES];;

let [NVAL3_DEF;NWORD3_DEF] = define_word_val word3
    (`NVAL3`,`NVAL3_DEF`) (`NWORD3`,`NWORD3_DEF`);;

let word3_NVAL_NWORD = prove_word_val word3 NVAL3_DEF NWORD3_DEF;;

let word3_NWORD_MOD = prove_NWORD_MOD word3_NVAL_NWORD;;

let NVAL3_3 = NVAL_CONV word3 NVAL3_DEF "NVAL3 #011";;

let NWORD3_3 = NWORD_CONV NWORD3_DEF word3_NWORD_MOD "NWORD3 3";;

