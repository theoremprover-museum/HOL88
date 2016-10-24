% filters.ml by Wai Wong  ver 1.0   					%
% This file conatins functions to filter out special characters and 	%
% convert them into LaTeX commands. 					%
  
% A list of special symbols which required to be converted to LaTeX	%
% special commands. This list is used in names				%
let spec_list = [
		 `_`, `\\US `;
		 `#`, `\\SH `;
		 `&`, `\\AM `;
		 `%`, `\\PC `;
		 `$`, `\\DO `;
		 `\\`, `\\BS `;
		 `'`, `\\PR `;
		 `~`, `\\TI `;
		 `*`, `\\AS `;
		 `<`, `\\LES `;
		 `|`, `\\BA `;
		 `>`, `\\GRE `;
		 `[`, `\\LB `;
		 `]`, `\\RB `;
		 `^`, `\\CI `;
		 `{`, `\\LC `;
		 `}`, `\\RC `];;

let do_char c = 
    let is_special c = mem c (fst(split spec_list)) in
    (is_special c) => (snd (assoc c spec_list)) | c;;

let filter_id id = concatl (map do_char (explode id));;

let dovar v =
    let isdigit x = mem x [`0`; `1`; `2`; `3`; `4`; `5`; `6`; `7`; `8`; `9`]
    in
    let chop f l =
    	letref hdstr = [] and tlstr = l in
        while  not (null tlstr) & not (f (hd tlstr))  do 
    	    (hdstr := hdstr @  [hd tlstr];
    	    tlstr := tl tlstr );
        (hdstr, tlstr)
    in
    letrec xformvar l =
    	let (c,t) = chop isdigit l in
        let (d,t') = chop (\x. not isdigit x) t in
    	    if null t then (flat (map (explode o do_char) c))
    	     else ( (flat(map (explode o do_char) c)) @
    	    	     [`_`;`{`] @ d @ [`}`] @ (xformvar t'))
    in
    implode (xformvar (explode v));;

   % Convert special constants to their symbols %

let symb_of sym =  case sym
		of `/\\`	. `\\AND `
		| `\\/`		. `\\OR `
		| `==>`		. `\\IMP `
    	    	| `-->`	    	. `\\LONG `
		| `<=>`		. `\\IFF `
		| `<=`		. `\\LEE `
		| `>=`		. `\\GEE `
    	    	| `?!`	    	. `\\EXISTSUNIQUE `
		| `<`		. `\\LES `
		| `>`		. `\\GRE `
		| `*`		. `\\MUL `
		| `~`		. `\\NOT `
		| `!`		. `\\FORALL `
		| `?`		. `\\EXISTS `
    	    	| `@`	    	. `\\SELECT `
    	    	| `o`	    	. `\\FUNCOM `
    	        | `RES_FORALL`  . `\\FORALL `
    	        | `RES_EXISTS`  . `\\EXISTS `
    	        | `RES_SELECT`  . `\\SELECT `
    	        | `RES_ABSTRACT`. `\\LAMBDA `
		| _		. (filter_id sym)
	;;

let doinfix x =
    let is_special y = tryfind (\c. not is_letter c) y in
    if( is_special (explode x))
    then (symb_of x)
    else (`\\:\\CONST{` ^ (filter_id x) ^ `}\\:`);;
