% sree@cs.ubc.ca %

letrec left_slice_list_at_char char list =
	if (null list) then []
	else
	   if ((hd list) = char) then
		[char]
	   else
		(hd list).(left_slice_list_at_char char (tl list));;

letrec right_slice_list_at_char char list =
	if (null list) then []
	else
	   if ((hd list) = char) then
	      list
	   else
		right_slice_list_at_char char (tl list);;
		  

let get_path file =
	let fullpath = find_file file in
	implode (rev (right_slice_list_at_char `/`
	   	  	(rev (explode fullpath))));;

let pathname = get_path `hol-eval_setup.ml`;;

loadf (pathname ^ `hol2ml`);;

letref oldp = ``;;

let eval hol_term = 
    implode (rev (tl (rev (explode (h2v hol_term)))));;

let msg () = `\LType a function name to evaluate or\LType "eval <hol_term>;;" to evaluate a new <hol_term> or\LType "exit();;" to exit\L`;;

let exec thy const_block_list cons_block_list = 
              tty_write (`Translating HOL definitions in ` ^ thy ^` and its ancestors ...\L`);
              ihcomp thy const_block_list cons_block_list; 
              tty_write (`\LLoading derived ML definitions in ` 
				  ^ thy ^`_hol.ml ...\L`);
              loadf (pathname ^ `prim.ml`);
              (loadf (concat thy `_hol.ml`) ? 
                tty_write `\LProceeding further though...\L`);
              tty_write (msg());
              oldp := set_prompt `holer> `;;


let exit () = set_prompt oldp;;
	   


