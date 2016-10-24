
( print_string `loading the "prooftree" subgoal package`;
  print_newline () ;
  let pack_path = (hol_pathname () ^ `/contrib/prooftree/code/`) in
	loadf (pack_path ^ `prooftree`)) ;;


