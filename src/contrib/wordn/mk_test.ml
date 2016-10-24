%set_library_search_path (`/homes/ww/hol2/`. library_search_path());; %

loadf`wordn`;;
loadt`wordn_pack`;;

timer true;; 


new_theory `test`;;


let [word8; word8_BITS_11; word8_BITS_onto; word8_WORD_11; word8_WORD_onto;
   	word8_LENGTH_BITS; word8_FNDEF; word8_INDUCT; word8_CASES] =
    use_wordn 8;;

let [word3; word3_BITS_11; word3_BITS_onto; word3_WORD_11; word3_WORD_onto;
   	word3_LENGTH_BITS; word3_FNDEF; word3_INDUCT; word3_CASES] =
    use_wordn 3;;

let [word5; word5_BITS_11; word5_BITS_onto; word5_WORD_11; word5_WORD_onto;
   	word5_LENGTH_BITS; word5_FNDEF; word5_INDUCT; word5_CASES] =
    use_wordn 5;;

let [NOT3_DEF; AND3_DEF; OR3_DEF; XOR3_DEF] =
    define_wordn_bit_ops word3_FNDEF 3;;

let [NOT3; AND3_SYM; OR3_SYM; XOR3_SYM; AND3_ASSOC; OR3_ASSOC; XOR3_ASSOC] =
    prove_bit_op_thms 3;;

let [NOT5_DEF; AND5_DEF; OR5_DEF; XOR5_DEF;
     NOT5; AND5_SYM; OR5_SYM; XOR5_SYM;
     AND5_ASSOC; OR5_ASSOC; XOR5_ASSOC] =
    wordn_bit_ops word5_FNDEF 5;;


let word3_6 = wordn_CONV "#110" ;;

let word3_2_6 = wordn_EQ_CONV word3 "#010 = #110";;

let word3_CCASES = prove_wordn_const_cases word3_CASES;;

let word3_BITS_WORD = prove_BITS_WORD word3;;

let [NVAL3_DEF; NWORD3_DEF] =
    define_word_val word3 (`NVAL3`,`NVAL3_DEF`) (`NWORD3`,`NWORD3_DEF`);;

let WORD_VAL_3 = save_thm(`WORD_VAL_3`, 
    prove_word_val word3 NVAL3_DEF NWORD3_DEF );;

let [NVAL5_DEF; NWORD5_DEF; WORD_VAL_5] =
    wordn_word_val word5 5;;

let word3_NWORD_MOD = prove_NWORD_MOD WORD_VAL_3;;

let word3_val_6 = wordn_NVAL_CONV word3 NVAL3_DEF "NVAL3 (WORD3[T;T;F])";;

let word3_val_6' = NVAL_CONV word3 NVAL3_DEF "NVAL3 #110";;

let word3_word_6 = wordn_NWORD_CONV NWORD3_DEF "NWORD3 6";;

let word3_word_16 = NWORD_CONV NWORD3_DEF word3_NWORD_MOD "NWORD3 16";;


let [word32; word32_BITS_11; word32_BITS_onto; word32_WORD_11;
     word32_WORD_onto; word32_LENGTH_BITS; word32_FNDEF;
     word32_INDUCT; word32_CASES] =
    use_wordn 32;;

let [word12; word12_BITS_11; word12_BITS_onto; word12_WORD_11;
     word12_WORD_onto; word12_LENGTH_BITS; word12_FNDEF;
     word12_INDUCT; word12_CASES] =
    use_wordn 12;;

let [word20; word20_BITS_11; word20_BITS_onto; word20_WORD_11;
     word20_WORD_onto; word20_LENGTH_BITS; word20_FNDEF;
     word20_INDUCT; word20_CASES] =
    use_wordn 20;;

let BWs = map prove_BITS_WORD [word20; word12; word32];;

let (JOIN_20_12, SPLIT_20_12) =
    define_word_partition (`JOIN_20_12`,`SPLIT_20_12`) BWs;;

let PARTITION_20_12 =
    prove_partition_thm (JOIN_20_12,SPLIT_20_12)
    [word20_CASES; word12_CASES; word32_CASES];;


let MSB8_DEF = define_wordn_msb word8 `MSB8_DEF`;;
let MSB8 = prove_msb_thm word8 MSB8_DEF;;
RIGHT_CONV_RULE (MSB_CONV MSB8)
 ((ONCE_DEPTH_CONV wordn_CONV) "MSB8 #10110001");;

let LSB8_DEF = define_wordn_lsb word8 `LSB8_DEF`;;
let LSB8 = prove_lsb_thm word8 LSB8_DEF;;
RIGHT_CONV_RULE (LSB_CONV LSB8) ((ONCE_DEPTH_CONV wordn_CONV) "LSB8 #10110001");;

let BIT8_DEF = define_wordn_bit word8 `BIT8_DEF`;;
let BIT8 = prove_bit_thm word8 BIT8_DEF 3;;
RIGHT_CONV_RULE (BIT_CONV BIT8) ((ONCE_DEPTH_CONV wordn_CONV) "BIT8 3 #10110001");;

let SEG8_3_DEF = define_wordn_seg word8 `SEG8_3_DEF` 3;;
let SEG8_3_2 = prove_seg_thm word8 SEG8_3_DEF 2;;
RIGHT_CONV_RULE (SEG_CONV SEG8_3_2)
 ((ONCE_DEPTH_CONV wordn_CONV) "SEG8_3 2 #10110001");;

let PAD8_3_DEF = define_wordn_pad word8 `PAD8_3_DEF` 3;;
let PAD8_3_2 = prove_pad_thm word8 word3 PAD8_3_DEF 2;;
RIGHT_CONV_RULE (PAD_CONV PAD8_3_2)
 ((ONCE_DEPTH_CONV wordn_CONV) "PAD8_3 #10110001 2 #011");;
