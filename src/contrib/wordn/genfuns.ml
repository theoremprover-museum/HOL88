% This file contains some general functions used in the library %

let mk_bit_list s1 n s2 =
    letrec upto m n = (m > n) => [] | (m . (upto (m + 1) n)) in
    let l = upto 0 (n-1) in
    map (\d. mk_var((s1 ^ (string_of_int d) ^ s2), ":bool")) l;;

let mk_bit_list_range s1 n1 n2 s2 =
    letrec upto m n = (m > n) => [] | (m . (upto (m + 1) n)) in
    let l = upto n1 n2 in
    map (\d. mk_var((s1 ^ (string_of_int d) ^ s2), ":bool")) l;;

let is_digit s =    
    	(let code = ascii_code s in
        let code_0 = (ascii_code `0`) - 1 in
    	let code_9 = (ascii_code `9`) + 1 in
    	((code > code_0) & (code < code_9))) ;;

